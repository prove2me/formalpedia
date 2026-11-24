-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_aT_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:34:41.275802+00:00
-- url     : https://prove2.me/submissions/d00c23ce-8b61-49da-9e59-c0508726e651

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
variable {R : Type*} [CommRing R] {V A B W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup W] [Module R W] {ι κ : Type*} [DecidableEq κ] {φ : κ → Type*}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (bA : ∀ k, Basis (φ k) R A) (bB : Basis κ R B) (x : Σ k, φ k) :
    qb_aT bA bB x = bA x.1 x.2 ⊗ₜ bB x.1 := by
  rw [qb_aT, Basis.map_apply, Finsupp.coe_basis, TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  exact Finsupp.sum_single_index (TensorProduct.zero_tmul _ _)
end Formalism.InvariantFactorPaths.ColumnFamilies
