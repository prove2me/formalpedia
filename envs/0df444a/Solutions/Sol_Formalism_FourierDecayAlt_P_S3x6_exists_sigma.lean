-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.exists_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:33.478825+00:00
-- url     : https://prove2.me/submissions/f2651b71-b626-40d8-bf9e-3d5887ea9fa4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_two_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_exists_frob
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_pow_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_fibre
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_fixed_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hq : Fintype.card K = q ^ 2) :
    ∃ σ : K →+* K, (∀ x, σ x = x ^ q) ∧ Inv σ := by
  classical
  have h2 := c_two_le K q hq
  obtain ⟨σ, hσ⟩ := c_exists_frob K q hq
  have hinv : ∀ x, σ (σ x) = x := fun x => by rw [hσ, hσ, c_pow_pow K q hq]
  refine ⟨σ, hσ, hinv, ?_, ?_⟩
  · intro c hc
    by_cases hc0 : c = 0
    · exact ⟨0, by simp [hc0]⟩
    · have h3 := c_fibre K q hq c (by rw [← hσ]; exact hc) hc0
      have h4 : (univ.filter (fun x : K => x ^ (q + 1) = c)).Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨y, hy⟩ := h4
      simp only [mem_filter, mem_univ, true_and] at hy
      exact ⟨y, by rw [hσ, ← pow_succ]; exact hy⟩
  · have h3 : ∃ t : K, t + σ t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h11 : (1 : K) + 1 = 0 := by simpa using hcon 1
      have hall : ∀ t : K, t ^ q = t := by
        intro t
        have h5 := hcon t
        rw [hσ] at h5
        have h6 : t + t = 0 := by
          have : t + t = t * (1 + 1) := by ring
          rw [this, h11, mul_zero]
        have : t ^ q - t = (t + t ^ q) - (t + t) := by ring
        rw [h5, h6, sub_zero] at this
        exact sub_eq_zero.1 this
      have h7 := c_fixed_card_le K q hq
      rw [Finset.filter_true_of_mem (fun x _ => hall x), card_univ, hq] at h7
      nlinarith
    obtain ⟨t, ht⟩ := h3
    refine ⟨t / (t + σ t), ?_⟩
    rw [map_div₀, map_add, hinv, add_comm (σ t) t, ← add_div, div_self ht]
end Formalism.FourierDecayAlt.P.S3x6
