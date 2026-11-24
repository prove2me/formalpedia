-- Prove2me | solution 1 for Formalism.REAL.sum_update_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:03.775452+00:00
-- url     : https://prove2.me/submissions/cea59dee-ad88-41ec-be3a-a48d2d183d1e

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M] (i : Fin j)
    (σ : X → X) (hσ : ∀ x, σ (σ x) = x) (P : X → Prop) [DecidablePred P]
    (f : (Fin j → X) → (Fin j → X) → M) :
    ∑ α : Fin j → X, (if P (α i) then f (Function.update α i (σ (α i))) α else 0) =
      ∑ β : Fin j → X, (if P (σ (β i)) then f β (Function.update β i (σ (β i))) else 0) := by
  classical
  have hinv : Function.Involutive (fun α : Fin j → X => Function.update α i (σ (α i))) := by
    intro α
    simp [hσ]
  refine Fintype.sum_bijective _ hinv.bijective _ _ ?_
  intro α
  simp [hσ]
end Formalism.REAL
