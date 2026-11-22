-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.fcoord_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:39.883581+00:00
-- url     : https://prove2.me/submissions/8da80a1d-6405-43ed-87bf-67101ed75aaa

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_blockInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.OrthogonalSumAlt
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) (x : Fin n → V) (j : Fin n)
    (a : ι) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x ⟨j, a⟩ =
        Formalism.HermitianLatticesTheory.fcoord b X v (x j) a := by
  have hinv : (Matrix.blockDiagonal' fun _ : Fin n => X v)⁻¹ =
      Matrix.blockDiagonal' fun _ : Fin n => (X v)⁻¹ :=
    Matrix.inv_eq_right_inv (blockInv X hX n v)
  simp only [Formalism.HermitianLatticesTheory.fcoord, hinv, Matrix.mulVec, dotProduct, Fintype.sum_sigma,
    Matrix.blockDiagonal'_apply, Formalism.HermitianLatticesTheory.vecAt]
  rw [Finset.sum_eq_single j]
  · simp [Pi.basis_repr]
  · intro k _ hk
    simp [hk.symm]
  · simp
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
