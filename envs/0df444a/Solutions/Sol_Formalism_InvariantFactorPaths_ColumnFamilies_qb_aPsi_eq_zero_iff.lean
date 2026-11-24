-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_aPsi_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:34:40.147787+00:00
-- url     : https://prove2.me/submissions/e5e5a7de-81b0-4406-b043-7f21ca90bcf6

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
theorem _root_.solution (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (x : V) :
    qb_aPsi b s c x = 0 ↔ ∀ i ∈ s, b.repr x i = 0 := by
  simp only [qb_aPsi, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
  rw [Finsupp.ext_iff]
  constructor
  · intro h y hy; exact h ⟨y, hy⟩
  · rintro h ⟨y, hy⟩; exact h y hy
end Formalism.InvariantFactorPaths.ColumnFamilies
