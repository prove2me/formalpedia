-- Prove2me | solution 1 for AvramDividend.Classical.barrier_cstar_attains_value_above_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:17:13.945987+00:00
-- url     : https://prove2.me/submissions/7c7121bb-689d-4c3e-b637-ac6e011f6880
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, (cstar W).toReal < x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by
  intro x hax
  have hc0 : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  have hx0 : 0 ≤ x := hc0.trans hax.le
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hof : ENNReal.ofReal (cstar W).toReal = cstar W :=
    ENNReal.ofReal_toReal hctop
  obtain ⟨hAdmC, hValC⟩ :=
    AvramDividend.Classical.barrier_cstar_attains_value_below_barrier
      X hX q hq W hW hc (cstar W).toReal hc0 le_rfl
  have hAdmC' :
      IsAdmissibleLe X (cstar W).toReal (ENNReal.ofReal (cstar W).toReal)
        (barrierStrategy X (cstar W).toReal (cstar W).toReal) := by
    rw [hof]
    exact hAdmC
  obtain ⟨hAdmX, hValX⟩ :=
    AvramDividend.Classical.add_initial_excess_admissible_value
      X q x (cstar W).toReal hc0 hax
      (barrierStrategy X (cstar W).toReal (cstar W).toReal) hAdmC'
  have hstrat :=
    AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
      X x (cstar W).toReal hc0 hax
  have hmono : MonotoneOn W (Ici 0) := hW.2.2.2.1
  have hderiv : ∀ y : ℝ, 0 < y → 0 ≤ deriv W y := by
    intro y hy
    have hd : 0 ≤ derivWithin W (Ici 0) y :=
      hmono.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds hy)] at hd
    exact hd
  have hdzp : (0 : EReal) ≤ derivZeroPlus W := by
    unfold derivZeroPlus
    have hev : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
        (0 : EReal) ≤ ((deriv W y : ℝ) : EReal) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact_mod_cast hderiv y hy
    have hl :
        Filter.liminf (fun _ : ℝ => (0 : EReal)) (𝓝[>] (0 : ℝ)) ≤
          Filter.liminf (fun y : ℝ => ((deriv W y : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) :=
      Filter.liminf_le_liminf hev
    simpa only [Filter.liminf_const] using hl
  have hsd : (0 : EReal) ≤ scaleDeriv W (cstar W).toReal := by
    unfold scaleDeriv
    split_ifs with hz
    · exact hdzp
    · have hcpos : 0 < (cstar W).toReal :=
        lt_of_le_of_ne hc0 (Ne.symm hz)
      exact_mod_cast hderiv (cstar W).toReal hcpos
  have hvc0 : 0 ≤ vcstar W (cstar W).toReal := by
    unfold vcstar barrierValue
    rw [if_neg (not_lt.mpr hc0), if_pos le_rfl]
    unfold divE
    by_cases hdtop : scaleDeriv W (cstar W).toReal = ⊤
    · simp [hdtop]
    · rw [if_neg hdtop]
      exact div_nonneg (hW.2.1 (cstar W).toReal hc0) (EReal.toReal_nonneg hsd)
  have hvc :
      vcstar W x =
        (x - (cstar W).toReal) + vcstar W (cstar W).toReal := by
    unfold vcstar barrierValue
    rw [if_neg (not_lt.mpr hx0), if_neg (not_le.mpr hax)]
    rw [if_neg (not_lt.mpr hc0), if_pos le_rfl]
  have hdelta : 0 ≤ x - (cstar W).toReal := sub_nonneg.mpr hax.le
  constructor
  · rw [hstrat]
    simpa only [hof] using hAdmX
  · rw [hstrat, hValX, hValC, ← ENNReal.ofReal_add hdelta hvc0, ← hvc]
