-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.isAddTorsionFree_ringOfIntegers_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:23.141019+00:00
-- url     : https://prove2.me/submissions/94c109bc-89b5-47d7-b605-35fc6b76050f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (L : Submodule (NumberField.RingOfIntegers K) V) :
    IsAddTorsionFree L := by
  constructor
  intro n hn a b hab
  apply Subtype.ext
  have hab' : n • (a : V) = n • (b : V) := by
    have := congrArg (fun y : L => (y : V)) hab
    simpa using this
  have h1 : (n : K) • ((a : V) - (b : V)) = 0 := by
    rw [smul_sub, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul K, hab', sub_self]
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hnK)
end Formalism.HermitianLatticesTheory
