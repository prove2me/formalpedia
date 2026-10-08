-- Prove2me | solution 2 for AvramDividend.Classical.cstar_scale_derivative_shape
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:15:19.8441+00:00
-- url     : https://prove2.me/submissions/41f84b23-3922-4d53-a55f-801e3859dfe4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_finite_zero_or_deriv_minimal
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_eq_sInf_of_nonempty
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_min_of_accumulated_minimizers
import Theorems.Thm_AvramDividend_Classical_cstar_shape_of_attained_positive_minimal
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_pos_of_excursion_and_W0

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Full analytic shape reduction, separating a positive attained barrier
from the two nondegenerate zero-barrier derivative-minimum regimes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hfinite : cstar W < ⊤) :
    ((cstar W).toReal = 0 ∧ W 0 = 0) ∨
      ∃ d : ℝ, 0 < d ∧
        scaleDeriv W (cstar W).toReal = (d : EReal) ∧
        (∀ a : ℝ, 0 ≤ a →
          scaleDeriv W a = ⊤ ∨
            (scaleDeriv W a).toReal = 0 ∨
            d ≤ (scaleDeriv W a).toReal) ∧
        (∀ b x : ℝ, 0 ≤ b → b ≤ x →
          x ≤ (cstar W).toReal →
          (x - b) * d ≤ W x - W b) := by
  obtain ⟨φe, μe, hφe, hnull, htailfin, hdiffAt, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  have hminimal :=
    (cstar_finite_zero_or_deriv_minimal X hX q hq W hW).2
  by_cases hc0 : (cstar W).toReal = 0
  · by_cases hW00 : W 0 = 0
    · exact Or.inl ⟨hc0, hW00⟩
    · right
      have hW0pos : 0 < W 0 :=
        lt_of_le_of_ne (hW.2.1 0 le_rfl) (Ne.symm hW00)
      have hsec_zero : ∀ (d : ℝ) (b x : ℝ),
          0 ≤ b → b ≤ x → x ≤ (cstar W).toReal →
          (x - b) * d ≤ W x - W b := by
        intro d b x hb hbx hxc
        have hx0 : x = 0 := by linarith [hc0]
        have hb0 : b = 0 := by linarith
        subst x
        subst b
        simp
      by_cases hS : (cstarSet W).Nonempty
      · have hScopy : (cstarSet W).Nonempty := hS
        obtain ⟨a₀, ha₀⟩ := hScopy
        have hsinf : sInf (cstarSet W) = 0 := by
          rw [← cstar_toReal_eq_sInf_of_nonempty W hS]
          exact hc0
        have hzero :
            derivZeroPlus W = ((deriv W a₀ : ℝ) : EReal) :=
          derivZeroPlus_eq_min_of_accumulated_minimizers W hS hsinf a₀ ha₀
        have hdpos : 0 < deriv W a₀ := by
          rw [hrepr a₀ ha₀.1]
          have hWpos : 0 < W a₀ :=
            scaleFunction_strict_pos_of_standing
              X hX q hq W hW a₀ ha₀.1
          have htail : 0 ≤ μe.real (Ici a₀) := measureReal_nonneg
          exact mul_pos hWpos (by linarith [hφe])
        refine ⟨deriv W a₀, hdpos, ?_, ?_, hsec_zero (deriv W a₀)⟩
        · simpa [hc0, scaleDeriv] using hzero
        · intro a ha
          by_cases ha0 : a = 0
          · subst a
            right
            right
            simp [scaleDeriv, hzero]
          · right
            right
            have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            simpa [scaleDeriv, ha0] using ha₀.2 a hapos
      · have hminzero : ∀ x : ℝ, 0 < x →
            derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
          by_contra hn
          have htop : cstar W = ⊤ := by
            simp [cstar, hS, hn]
          have : False := by simpa [htop] using hfinite
          exact this
        have hpositive : (0 : EReal) < derivZeroPlus W :=
          derivZeroPlus_pos_of_excursion_and_W0
            W φe μe hφe hW0pos hW.2.2.2.1 hrepr
        have hnotTop : derivZeroPlus W ≠ ⊤ := by
          intro ht
          have hh : (⊤ : EReal) ≤ ((deriv W 1 : ℝ) : EReal) := by
            simpa [ht] using hminzero 1 (by norm_num)
          simpa using hh
        have hnotBot : derivZeroPlus W ≠ ⊥ := by
          have hlt : (⊥ : EReal) < derivZeroPlus W :=
            lt_of_le_of_lt bot_le hpositive
          exact ne_of_gt hlt
        let d : ℝ := (derivZeroPlus W).toReal
        have hdpos : 0 < d := EReal.toReal_pos hpositive hnotTop
        have hcoe : (d : EReal) = derivZeroPlus W :=
          EReal.coe_toReal hnotTop hnotBot
        refine ⟨d, hdpos, ?_, ?_, hsec_zero d⟩
        · simpa [hc0, scaleDeriv] using hcoe.symm
        · intro a ha
          by_cases ha0 : a = 0
          · subst a
            right
            right
            simp [d, scaleDeriv]
          · right
            right
            have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hle := hminzero a hapos
            have hnotTopA : ((deriv W a : ℝ) : EReal) ≠ ⊤ := by
              simp
            have hreal := EReal.toReal_le_toReal hle hnotBot hnotTopA
            simpa [d, scaleDeriv, ha0] using hreal
  · right
    rcases hminimal with hz | ⟨hcpos, hmin⟩
    · exact (hc0 hz).elim
    · have hcont : ContinuousOn W (Icc 0 (cstar W).toReal) :=
        hW.2.2.1.mono (by
          intro x hx
          exact hx.1)
      have hdiff : DifferentiableOn ℝ W (Ioo 0 (cstar W).toReal) := by
        intro x hx
        exact (hdiffAt x hx.1).differentiableWithinAt
      have hpos : 0 < deriv W (cstar W).toReal := by
        rw [hrepr (cstar W).toReal hcpos]
        have hWpos : 0 < W (cstar W).toReal :=
          scaleFunction_strict_pos_of_standing
            X hX q hq W hW (cstar W).toReal hcpos
        have htail : 0 ≤ μe.real (Ici (cstar W).toReal) :=
          measureReal_nonneg
        exact mul_pos hWpos (by linarith [hφe])
      exact cstar_shape_of_attained_positive_minimal W ⟨hcpos, hmin⟩
        hpos hcont hdiff
