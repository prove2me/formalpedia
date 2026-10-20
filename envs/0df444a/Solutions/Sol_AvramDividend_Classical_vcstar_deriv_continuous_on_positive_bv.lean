-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_continuous_on_positive_bv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:12:45.812538+00:00
-- url     : https://prove2.me/submissions/8cb19bc3-fcd7-4eac-86cb-4ccda0bdacab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

private theorem avram_derivative_glue (F G : ℝ → ℝ) (c : ℝ)
    (hF : ContinuousOn F (Ioi 0))
    (hjoin : F c = 1)
    (hformula : ∀ y : ℝ, y ∈ Ioi (0 : ℝ) →
      G y = if y ≤ c then F y else 1) :
    ContinuousOn G (Ioi 0) := by
  classical
  have hleft : ContinuousOn F
      (Ioi (0 : ℝ) ∩ closure {y : ℝ | y ≤ c}) :=
    hF.mono inter_subset_left
  have hright : ContinuousOn (fun _ : ℝ => (1 : ℝ))
      (Ioi (0 : ℝ) ∩ closure {y : ℝ | ¬y ≤ c}) :=
    continuousOn_const
  have hboundary : ∀ y ∈
      Ioi (0 : ℝ) ∩ frontier {z : ℝ | z ≤ c},
      F y = (1 : ℝ) := by
    intro y hy
    have heq : y = c :=
      (mem_singleton_iff).mp (frontier_Iic_subset c hy.2)
    simpa [heq] using hjoin
  have hpiece : ContinuousOn
      (fun y : ℝ => if y ≤ c then F y else 1) (Ioi 0) :=
    ContinuousOn.if hboundary hleft hright
  exact hpiece.congr (by
    intro y hy
    exact hformula y hy)

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContinuousOn (deriv (vcstar W)) (Ioi 0) := by
  let c : ℝ := (cstar W).toReal
  let d : ℝ := deriv W c
  have hcReal : 0 < c := by
    dsimp [c]
    exact ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hd : 0 < d := scaleDeriv_pos X hX q hq W hW c hcReal
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hdiff : DifferentiableAt ℝ W c := by
    exact ((hreg.differentiableOn (by norm_num)) c hcReal).differentiableAt
      (isOpen_Ioi.mem_nhds hcReal)
  have hbelow (y : ℝ) (hy : 0 < y) (hyc : y < c) :
      deriv (vcstar W) y = deriv W y / d := by
    have heq : (vcstar W) =ᶠ[𝓝 y] (fun z => W z / d) := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hy, hyc⟩] with z hz
      have hz0 : ¬z < 0 := not_lt.mpr hz.1.le
      have hzc : z ≤ c := hz.2.le
      simpa [vcstar, barrierValue, scaleDeriv, divE, c, d,
        hz0, hzc, (ne_of_gt hcReal)]
    calc
      deriv (vcstar W) y = deriv (fun z => W z / d) y :=
        Filter.EventuallyEq.deriv_eq heq
      _ = deriv W y / d := deriv_div_const d
  have hjoin : deriv (vcstar W) c = 1 := by
    have hs := vcstar_first_deriv_smooth_fit_of_nonzero
      W hcReal hdiff (ne_of_gt hd)
    simpa [c, d, scaleDeriv, divE, ne_of_gt hcReal,
      deriv_div_const, div_self (ne_of_gt hd)] using hs
  have hF : ContinuousOn (fun y : ℝ => deriv W y / d) (Ioi 0) :=
    hcont.div_const d
  have hformula : ∀ y : ℝ, y ∈ Ioi (0 : ℝ) →
      deriv (vcstar W) y =
      if y ≤ c then deriv W y / d else 1 := by
    intro y hy
    by_cases hlt : y < c
    · simpa [if_pos hlt.le] using hbelow y hy hlt
    · by_cases heq : y = c
      · subst y
        simpa [d, div_self (ne_of_gt hd)] using hjoin
      · have hgt : c < y :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        simpa [if_neg (not_le.mpr hgt), c] using
          vcstar_deriv_eq_one_above_cstar W y hgt
  exact avram_derivative_glue
    (fun y => deriv W y / d) (deriv (vcstar W)) c
    hF (div_self (ne_of_gt hd)) hformula
