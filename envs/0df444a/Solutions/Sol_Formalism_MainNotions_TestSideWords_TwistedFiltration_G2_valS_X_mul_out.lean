-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.valS_X_mul_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:27.747592+00:00
-- url     : https://prove2.me/submissions/83c7087d-5a6a-4496-b3e5-9edebfdd2bb1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_twistSub_X_out
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_mem_of_X_mul_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_valS_X_mul_of
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_le_valS

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
private lemma withTop_int_le_of_forall_coe_le {a b : WithTop ℤ}
    (h : ∀ t : ℤ, (t : WithTop ℤ) ≤ a → (t : WithTop ℤ) ≤ b) : a ≤ b := by
  cases b with
  | top => exact le_top
  | coe m =>
    cases a with
    | top => exact absurd (WithTop.coe_le_coe.mp (h (m + 1) le_top)) (by omega)
    | coe k => exact h k le_rfl
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
    valS LL S (X v * F) = valS LL S F := by
  apply le_antisymm
  · apply withTop_int_le_of_forall_coe_le
    intro t ht
    rw [flt_le_valS] at ht ⊢
    rw [map_mul, twistSub_X_out LL S _ v h] at ht
    exact mem_of_X_mul_mem v _ ht
  · exact valS_X_mul_of LL S F v (fun hv => absurd hv h)
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
