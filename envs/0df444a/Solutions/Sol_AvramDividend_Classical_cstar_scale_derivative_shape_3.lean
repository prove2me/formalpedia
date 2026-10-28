-- Prove2me | solution 3 for AvramDividend.Classical.cstar_scale_derivative_shape
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:26:11.091316+00:00
-- url     : https://prove2.me/submissions/e0c0db29-8945-4baa-abd4-eb688f27c4f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary
import Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_eq_sInf_of_nonempty
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_min_of_accumulated_minimizers
import Theorems.Thm_AvramDividend_Classical_cstar_shape_of_attained_positive_minimal
import Theorems.Thm_AvramDividend_Classical_scale_deriv_pos_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_scale_deriv_zero_pos_of_normalized_monotone_and_W0

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The complete finite-barrier shape using only positive-axis C1 and
Esscher-normalised monotonicity as unproved analytic prerequisites. -/
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
  obtain ⟨hpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact hC1.differentiableOn_one.differentiableAt (isOpen_Ioi.mem_nhds hx)
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) := hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl _)
  have hderiv_pos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    scale_deriv_pos_of_normalized_monotone W φ hφ hpos htilt hdiff
  have hminimal :
      (cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x) := by
    by_cases hS : (cstarSet W).Nonempty
    · have hArgmin :
          sInf (cstarSet W) = 0 ∨
            (0 < sInf (cstarSet W) ∧
              ∀ x : ℝ, 0 < x →
                deriv W (sInf (cstarSet W)) ≤ deriv W x) := by
            simpa only [cstarSet] using
              (continuous_argmin_sInf_zero_or_minimal (deriv W) hcont hS)
      rw [← cstar_toReal_eq_sInf_of_nonempty W hS] at hArgmin
      exact hArgmin
    · have hzero :=
        ((cstar_lt_top_iff_minimizer_or_zero_boundary W).mp hfinite).resolve_left hS
      have hc : cstar W = 0 := by unfold cstar; rw [if_neg hS, if_pos hzero]
      exact Or.inl (by simp [hc])
  by_cases hc0 : (cstar W).toReal = 0
  · by_cases hW00 : W 0 = 0
    · exact Or.inl ⟨hc0, hW00⟩
    · right
      have hW0pos : 0 < W 0 := lt_of_le_of_ne (hW.2.1 0 le_rfl) (Ne.symm hW00)
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
      · obtain ⟨a₀, ha₀⟩ := hS
        have hsinf : sInf (cstarSet W) = 0 := by
          rw [← cstar_toReal_eq_sInf_of_nonempty W ⟨a₀, ha₀⟩]
          exact hc0
        have hzero :
            derivZeroPlus W = ((deriv W a₀ : ℝ) : EReal) :=
          derivZeroPlus_eq_min_of_accumulated_minimizers
            W ⟨a₀, ha₀⟩ hsinf a₀ ha₀
        have hdpos : 0 < deriv W a₀ := hderiv_pos a₀ ha₀.1
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
          scale_deriv_zero_pos_of_normalized_monotone_and_W0
            W φ hφ hW0pos hW.2.2.2.1 htilt hdiff
        have hnotTop : derivZeroPlus W ≠ ⊤ := by
          intro ht
          have hh : (⊤ : EReal) ≤ ((deriv W 1 : ℝ) : EReal) := by
            simpa [ht] using hminzero 1 (by norm_num)
          simpa using hh
        have hnotBot : derivZeroPlus W ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hpositive)
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
            have hnotTopA : ((deriv W a : ℝ) : EReal) ≠ ⊤ := by simp
            have hreal := EReal.toReal_le_toReal hle hnotBot hnotTopA
            simpa [d, scaleDeriv, ha0] using hreal
  · right
    rcases hminimal with hz | ⟨hcpos, hmin⟩
    · exact (hc0 hz).elim
    · have hcontW : ContinuousOn W (Icc 0 (cstar W).toReal) :=
        hW.2.2.1.mono (by intro x hx; exact hx.1)
      have hdiffW : DifferentiableOn ℝ W (Ioo 0 (cstar W).toReal) := by
        intro x hx
        exact (hdiff x hx.1).differentiableWithinAt
      have hposc : 0 < deriv W (cstar W).toReal := hderiv_pos (cstar W).toReal hcpos
      exact cstar_shape_of_attained_positive_minimal W ⟨hcpos, hmin⟩
        hposc hcontW hdiffW
