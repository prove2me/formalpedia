-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.jacobi_complementary_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:13.188144+00:00
-- url     : https://prove2.me/submissions/bd197f00-6c2a-48b7-b414-2008d86df3f7

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {R : Type*} [CommRing R] {m n₁ n₂ : Type*} [Fintype m] [DecidableEq m]
    [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    (A : Matrix m m R) (ρ γ : n₁ ⊕ n₂ ≃ m) :
    (A.submatrix ρ γ).det * (Matrix.of fun i j : n₁ => A.adjugate (γ (Sum.inl j)) (ρ (Sum.inl i))).det =
      A.det ^ Fintype.card n₁ * (Matrix.of fun i j : n₂ => A (ρ (Sum.inr i)) (γ (Sum.inr j))).det := by
  have hAB : A.submatrix ρ γ * A.adjugate.submatrix γ ρ = A.det • (1 : Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) R) := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_adjugate, Matrix.submatrix_smul, Pi.smul_apply, Pi.smul_apply,
      Matrix.submatrix_one_equiv]
  generalize hA' : A.submatrix ρ γ = A' at *
  generalize hB : A.adjugate.submatrix γ ρ = B at *
  have h1 := hAB
  rw [← Matrix.fromBlocks_toBlocks A', ← Matrix.fromBlocks_toBlocks B, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_inj] at h1
  obtain ⟨h11, -, h21, -⟩ := h1
  have key : A' * Matrix.fromBlocks B.toBlocks₁₁ 0 B.toBlocks₂₁ 1 =
      Matrix.fromBlocks (A.det • 1) A'.toBlocks₁₂ 0 A'.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks A']
    rw [Matrix.fromBlocks_multiply, h11, h21]
    simp
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  rw [← Matrix.det_transpose (Matrix.of fun i j : n₁ => A.adjugate (γ (Sum.inl j)) (ρ (Sum.inl i)))]
  subst hA' hB
  exact hdet
end Formalism.CohomologicalDescent.LD
