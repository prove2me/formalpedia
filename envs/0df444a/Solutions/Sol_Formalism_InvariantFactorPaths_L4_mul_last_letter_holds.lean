-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mul_last_letter_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:12.521539+00:00
-- url     : https://prove2.me/submissions/5d679eed-ddb3-4c0e-8032-80ee5fa2d236

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raise_nil
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mulLast_bwd
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mulLast_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_last
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : MulLast := by
  intro p hp K r hr LL j M c h hj hv
  constructor
  · intro hX
    by_cases hc : c = 0
    · subst hc; exact mulLast_zero p LL j M hj hv h hX
    · obtain ⟨n, hn⟩ := raise_nil p LL j c hc h
      have hpowY : ∀ (k : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), x ∈ YCond p LL j M →
          ((glAct p LL j 0 c) ^ k) x ∈ YCond p LL j M := by
        intro k
        induction k with
        | zero => intro x hx; simpa using hx
        | succ k ih =>
          intro x hx
          rw [pow_succ', Module.End.mul_apply]
          exact ycond_glStable (p := p) LL j M 0 c _ (ih x hx)
      have key : ∀ t i : ℕ, i + t = n →
          ((glAct p LL j 0 c) ^ i) h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) := by
        intro t
        induction t with
        | zero =>
          intro i hi
          rw [add_zero] at hi
          subst hi
          rw [hn]
          exact Submodule.zero_mem _
        | succ t ih =>
          intro i hi
          have h1 := ih (i + 1) (by omega)
          have h2 := mulLast_bwd p LL j M hj hv c _ h1
          have h3 := hpowY (i + 1) _ hX
          rw [pow_last p LL j hj hv c hc h i] at h3
          have h4 : ((i + 1 : ℕ) : ℚ_[p]) • (X (Fin.last K, (0 : Fin r)) * ((glAct p LL j 0 c) ^ i) h) ∈
              YCond p LL j M := by
            have := Submodule.sub_mem _ h3 h2
            simpa using this
          have hne : ((i + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)
          have h5 := Submodule.smul_mem _ ((i + 1 : ℕ) : ℚ_[p])⁻¹ h4
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h5
          exact mulLast_zero p LL j M hj hv _ h5
      simpa using key n 0 (by omega)
  · intro hh
    exact mulLast_bwd p LL j M hj hv c h hh
end Formalism.InvariantFactorPaths.L4
