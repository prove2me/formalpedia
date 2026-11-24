-- Prove2me | solution 1 for Formalism.SLP.P.det_orth_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:43.811633+00:00
-- url     : https://prove2.me/submissions/07a38ca7-d308-4b54-8028-11495fbe0e97

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Theorems.Thm_Formalism_SLP_P_row_sq_le
import Theorems.Thm_Formalism_HadamardInequality_P_hadamard_inequality_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset ComplexConjugate
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
namespace Formalism.SLP.P
theorem _root_.solution (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖)
    {m : ℕ} (e : Fin m → V₁) (he : Orthonormal ℂ e) (f : Fin m → V₂) (hf : Orthonormal ℂ f) :
    ‖(Matrix.of fun k l => B (e k) (f l)).det‖ ^ 2 ≤ c ^ (2 * m) := by
  refine le_trans (Formalism.HadamardInequality.P.hadamard_inequality_holds m _) ?_
  calc ∏ k, ∑ l, ‖(Matrix.of fun k l => B (e k) (f l)) k l‖ ^ 2 ≤ ∏ _k : Fin m, c ^ 2 :=
        Finset.prod_le_prod (fun k _ => Finset.sum_nonneg fun l _ => by positivity)
          fun k _ => row_sq_le B c hB (e k) (he.1 k) f hf
    _ = c ^ (2 * m) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
end Formalism.SLP.P
