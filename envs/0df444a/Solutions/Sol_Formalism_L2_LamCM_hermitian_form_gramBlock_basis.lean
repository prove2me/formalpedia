-- Prove2me | solution 1 for Formalism.L2.LamCM.hermitian_form_gramBlock_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:20:20.564632+00:00
-- url     : https://prove2.me/submissions/a0fa5e9a-5b5a-41a8-8b23-f386201427b4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis
import Theorems.Thm_Formalism_L2_LamCM_dot_basis_vector_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain IsLocalRing Matrix
open scoped nonZeroDivisors ComplexOrder
variable {K : Type} [Field K] [NumberField K] {B : Type} {m : B → ℕ} {g : ℕ}
namespace Formalism.L2.LamCM
theorem _root_.solution (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K) (H : Matrix (Fin g) (Fin g) ℂ)
    (σ : K →+* ℂ) (b : B) (j : Fin (m b)) :
    ReciprocityTheory.MultiplicativeHeights.hq (gramBlock e U H σ b) ((1 : Matrix (Fin (m b)) (Fin (m b)) ℂ) j) =
      ReciprocityTheory.MultiplicativeHeights.hq H (ReciprocityTheory.MultiplicativeHeights.embVec σ (U (e ⟨b, j⟩))) := by
  simp only [ReciprocityTheory.MultiplicativeHeights.hq, dot_basis_vector_diag]
  rfl
end Formalism.L2.LamCM
