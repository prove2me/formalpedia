-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mul_last_letter_mod_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:53.579451+00:00
-- url     : https://prove2.me/submissions/9c8aa7c4-45e3-4aaa-a4ab-6344d872a004

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_succ_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_sq_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_dpow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_last_fwd
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_last_zero
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raise_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : MulLastModP := by
  intro p _ K r _ LL j M c h hj hv hU
  by_cases hc : c = 0
  · subst hc
    exact modCond_last_zero p LL j M hj hv h hU
  · have hstep : ∀ k, ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c (k + 1) h) →
        ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c k h) := by
      intro k hk
      apply modCond_last_zero p LL j M hj hv
      have h1 := modCond_dpow p LL j M _ hU c hc (k + 1)
      rw [dpow_succ_mul p LL j c _ _ (glAct_sq_X p LL j c hc _), last_X p LL j hj hv, if_pos rfl] at h1
      have h2 := modCond_last_fwd p LL j M hj hv c _ 0 hk (modCond_zero p LL j _)
      have h3 := modCond_sub p LL j M _ _ h1 h2
      have e : X (Fin.last K, (0 : Fin r)) * dpow p LL j c k h =
          X (Fin.last K, c) * dpow p LL j c (k + 1) h + X (Fin.last K, (0 : Fin r)) * dpow p LL j c k h -
            (X (Fin.last K, c) * dpow p LL j c (k + 1) h + X (Fin.last K, (0 : Fin r)) * 0) := by ring
      rw [e]
      exact h3
    have hdown : ∀ n, ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) (dpow p LL j c n h) →
        ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) h := by
      intro n
      induction n with
      | zero => intro hn; rwa [dpow_zero] at hn
      | succ n ih => exact fun hn => ih (hstep n hn)
    obtain ⟨n, hn⟩ := raise_nil p LL j c hc h
    refine hdown n ?_
    have : dpow p LL j c n h = 0 := by
      simp only [dpow, LinearMap.smul_apply]
      rw [hn, smul_zero]
    rw [this]
    exact modCond_zero p LL j _
end Formalism.InvariantFactorPaths.L4
