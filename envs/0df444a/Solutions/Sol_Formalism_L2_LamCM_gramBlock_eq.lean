-- Prove2me | solution 1 for Formalism.L2.LamCM.gramBlock_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:21.106946+00:00
-- url     : https://prove2.me/submissions/95e7acb4-1dc7-47f1-b97b-b62b8c16a5d4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis

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
    (σ : K →+* ℂ) (b : B) :
    gramBlock e U H σ b = (((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ)ᴴ * H *
      ((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ := by
  rw [Matrix.mul_assoc]
  ext j j'
  simp [gramBlock, Matrix.mul_apply, dotProduct, mulVec, ReciprocityTheory.MultiplicativeHeights.embVec]
end Formalism.L2.LamCM
