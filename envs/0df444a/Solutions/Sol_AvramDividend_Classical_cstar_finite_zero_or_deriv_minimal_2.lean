-- Prove2me | solution 2 for AvramDividend.Classical.cstar_finite_zero_or_deriv_minimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:26:13.365102+00:00
-- url     : https://prove2.me/submissions/81a7c11c-8fc7-4484-9333-db565756138b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_eq_sInf_of_nonempty

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finiteness and positive-minimum closure for the canonical barrier,
using its real-infimum bridge and continuity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ((cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) := by
  have hfinite := cstar_lt_top X hX q hq W hW
  refine ⟨hfinite, ?_⟩
  by_cases hS : (cstarSet W).Nonempty
  · have hcont := scaleDeriv_continuous X hX q hq W hW
    have harg :=
      continuous_argmin_sInf_zero_or_minimal (deriv W) hcont
        (by simpa [cstarSet] using hS)
    have hEq := cstar_toReal_eq_sInf_of_nonempty W hS
    rw [hEq]
    simpa [cstarSet] using harg
  · have hzero : ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
      by_contra hn
      have htop : cstar W = ⊤ := by simp [cstar, hS, hn]
      exact (lt_irrefl (⊤ : ℝ≥0∞) (htop ▸ hfinite))
    rw [cstar, if_neg hS, if_pos hzero]
    exact Or.inl rfl
