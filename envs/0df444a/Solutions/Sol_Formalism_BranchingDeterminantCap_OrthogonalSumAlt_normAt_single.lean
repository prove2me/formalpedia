-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.normAt_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:20.910126+00:00
-- url     : https://prove2.me/submissions/0308d876-d800-4890-a443-2f9814c4cbe6

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_fcoord_pi

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
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) (i : Fin n) (x : V) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v (Pi.single i x) =
        Formalism.HermitianLatticesTheory.normAt b X v x := by
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Fintype.sum_sigma, fcoord_pi b X hX]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk, Formalism.HermitianLatticesTheory.fcoord_zero]
  · simp
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
