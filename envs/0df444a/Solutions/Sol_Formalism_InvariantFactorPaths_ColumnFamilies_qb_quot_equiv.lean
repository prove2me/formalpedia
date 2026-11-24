-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_quot_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:34:42.677811+00:00
-- url     : https://prove2.me/submissions/4ace94e5-3243-44b7-814f-8d9ea908951b

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
theorem _root_.solution {N T : Type*} [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T]
    (f : N →ₗ[R] T) (hs : Function.Surjective f) (p : Submodule R N) (hk : LinearMap.ker f = p) :
    ∃ Phi : (N ⧸ p) ≃ₗ[R] T, ∀ x, Phi (Submodule.Quotient.mk x) = f x := by
  subst hk
  exact ⟨f.quotKerEquivOfSurjective hs, fun x => f.quotKerEquivOfSurjective_apply_mk hs x⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
