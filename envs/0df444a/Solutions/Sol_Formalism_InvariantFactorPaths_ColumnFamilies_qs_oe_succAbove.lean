-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_oe_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:08.961123+00:00
-- url     : https://prove2.me/submissions/64c5f360-7e53-4738-abdd-0725434a2c07

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1))
    (hs' : (s.erase (s.orderEmbOfFin hs j)).card = h) (i : Fin h) :
    s.orderEmbOfFin hs (j.succAbove i) = (s.erase (s.orderEmbOfFin hs j)).orderEmbOfFin hs' i := by
  have := Finset.orderEmbOfFin_unique hs' (f := fun i => s.orderEmbOfFin hs (j.succAbove i))
    (fun x => Finset.mem_erase.2 ⟨(s.orderEmbOfFin hs).injective.ne (Fin.succAbove_ne j x),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove j))
  exact congrFun this i
end Formalism.InvariantFactorPaths.ColumnFamilies
