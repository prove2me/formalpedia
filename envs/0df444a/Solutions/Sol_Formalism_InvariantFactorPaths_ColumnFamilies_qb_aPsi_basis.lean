-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_aPsi_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:57.6141+00:00
-- url     : https://prove2.me/submissions/79062c42-204d-4687-a574-dd26916578d2

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
theorem _root_.solution (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (i : ι) (hi : i ∈ s) :
    qb_aPsi b s c (b i) = c ⟨i, hi⟩ := by
  classical
  simp only [qb_aPsi, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self]
  rw [← Basis.repr_symm_single_one]
  congr 1
  ext z
  simp only [Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_apply, Finsupp.single_apply]
  congr 1
  exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
