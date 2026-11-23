-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.b_root_sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.609237+00:00
-- url     : https://prove2.me/submissions/4003b8d4-0c9e-411f-a9d3-0d684dc724c7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_b_pow_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution (s : ℕ) (hs : 0 < s) (z z' : ℂ) (hz : z ≠ 0) (h : z' ^ s = z ^ s) (hne : z' ≠ z) :
    ‖z‖ ≤ s * ‖z' - z‖ := by
  obtain ⟨ω, hω⟩ : ∃ ω, ω = z' / z := ⟨_, rfl⟩
  have hz' : z' = ω * z := by rw [hω]; field_simp
  have hzs : z ^ s ≠ 0 := pow_ne_zero _ hz
  have hω1 : ω ^ s = 1 := by rw [hω, div_pow, h, div_self hzs]
  have hωne : ω - 1 ≠ 0 := by
    intro h0
    apply hne
    rw [hz', sub_eq_zero.1 h0, one_mul]
  have hn : ‖ω‖ = 1 := by
    have : ‖ω‖ ^ s = 1 := by rw [← norm_pow, hω1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hs.ne').1 this
  have hsum : ∑ i ∈ range s, ω ^ i = 0 := by
    have := mul_geom_sum ω s
    rw [hω1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left hωne
  have h1 : (s : ℂ) = -∑ i ∈ range s, (ω ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have h2 : (s : ℝ) ≤ ∑ i ∈ range s, (s : ℝ) * ‖ω - 1‖ := by
    calc (s : ℝ) = ‖(s : ℂ)‖ := by simp
      _ = ‖∑ i ∈ range s, (ω ^ i - 1)‖ := by rw [h1, norm_neg]
      _ ≤ ∑ i ∈ range s, ‖ω ^ i - 1‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range s, (s : ℝ) * ‖ω - 1‖ := by
        refine Finset.sum_le_sum fun i hi => (b_pow_sub_one ω hn i).trans ?_
        have : (i : ℝ) ≤ s := by exact_mod_cast (Finset.mem_range.1 hi).le
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h3 : 1 ≤ (s : ℝ) * ‖ω - 1‖ := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have h4 : z' - z = (ω - 1) * z := by rw [hz']; ring
  rw [h4, norm_mul, ← mul_assoc]
  exact le_mul_of_one_le_left (norm_nonneg _) h3
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
