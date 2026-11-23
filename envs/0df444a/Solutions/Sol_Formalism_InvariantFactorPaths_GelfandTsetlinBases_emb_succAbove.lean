-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.emb_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:50.038078+00:00
-- url     : https://prove2.me/submissions/f2eef5e5-985b-4e65-bedc-9d1c8bcb7f78

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {d : ℕ} {J J' : Finset (Fin n)} (h : J.card = d + 1) (j : Fin (d + 1))
    (hJ' : J' = J.erase (J.orderEmbOfFin h j)) (h' : J'.card = d) :
    (fun x => J.orderEmbOfFin h (j.succAbove x)) = J'.orderEmbOfFin h' := by
  subst hJ'
  apply Finset.orderEmbOfFin_unique h'
  · intro x
    rw [Finset.mem_erase]
    exact ⟨fun heq => Fin.succAbove_ne j x ((J.orderEmbOfFin h).injective heq),
      Finset.orderEmbOfFin_mem J h _⟩
  · exact (J.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove j)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
