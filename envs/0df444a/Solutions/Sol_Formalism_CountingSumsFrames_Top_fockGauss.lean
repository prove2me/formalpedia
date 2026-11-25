-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.fockGauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:19:42.134198+00:00
-- url     : https://prove2.me/submissions/4014f8e0-bc82-4cc1-ba43-12a1451aabb1

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate
import Theorems.Thm_Formalism_CountingSumsFrames_fock_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.FockGauss := by
  intro p _ σ Z _ _ _ _ letter d N k a ha hcard hd F hF
  have hc := fun α (hα : α ∈ F.support) => fock_core p letter d N k a ha hcard hd α (hF α hα)
  refine ⟨?_, ?_⟩
  · unfold vBB
    apply Finset.le_inf
    intro α hα
    have h2 := (hc α hα).2
    have hle : vG p F ≤ (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ) := by
      unfold vG
      exact Finset.inf_le hα
    refine le_trans (add_le_add hle le_rfl) ?_
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    push_cast at h2 ⊢
    linarith
  · unfold vBB
    rcases F.support.eq_empty_or_nonempty with hs | hs
    · simp [vG, hs]
    · obtain ⟨α, hα, heq⟩ := Finset.exists_mem_eq_inf F.support hs
        (fun α => (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ))
      have hvg : vG p F = (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ) := heq
      rw [hvg, ← WithTop.coe_add]
      refine le_trans (Finset.inf_le hα) ?_
      rw [WithTop.coe_le_coe]
      have h1 := (hc α hα).1
      have h3 : (padicValNat p (factProd α) : ℝ) ≤ padicValNat p (∏ z, (d z).factorial) := by
        exact_mod_cast h1
      linarith
end Formalism.CountingSumsFrames.Top
