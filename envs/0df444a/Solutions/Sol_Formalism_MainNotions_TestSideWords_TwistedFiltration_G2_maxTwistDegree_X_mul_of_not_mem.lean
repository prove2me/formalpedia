-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:24.001635+00:00
-- url     : https://prove2.me/submissions/6c7b84c6-df4c-41cb-bfd3-f9de549e7d9d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_twistSub_X_out
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_mem_of_X_mul_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_maxTwistDegree_X_mul_le_of
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lam1S_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
private lemma withBot_int_le_of_forall_le_coe {a b : WithBot ℤ}
    (h : ∀ M : ℤ, b ≤ (M : WithBot ℤ) → a ≤ (M : WithBot ℤ)) : a ≤ b := by
  cases a with
  | bot => exact bot_le
  | coe k =>
    cases b with
    | bot => exact absurd (WithBot.coe_le_coe.mp (h (k - 1) bot_le)) (by omega)
    | coe m => exact h m le_rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
theorem _root_.solution (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∉ S) :
    lam1S LL S (X v * F) = lam1S LL S F := by
  apply le_antisymm
  · exact maxTwistDegree_X_mul_le_of LL S F v (fun hv => absurd hv h)
  · apply withBot_int_le_of_forall_le_coe
    intro M hM
    rw [flt_lam1S_le] at hM ⊢
    rw [map_mul, twistSub_X_out LL S _ v h] at hM
    exact mem_of_X_mul_mem v _ hM
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
