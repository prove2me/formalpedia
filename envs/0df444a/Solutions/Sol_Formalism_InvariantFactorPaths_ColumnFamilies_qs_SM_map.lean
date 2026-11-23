-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_SM_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:07.104287+00:00
-- url     : https://prove2.me/submissions/f11e7fba-24e3-4d6e-9118-13dfe0b3337f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (G : Matrix (Fin n) (Fin n) A) (b : ℕ)
    (α β : SymIdx n b) : f (qs_SM G b α β) = qs_SM (G.map f) b α β := by
  rw [qs_SM, qs_SM, ← MvPolynomial.coeff_map]
  simp [map_prod, map_pow, map_sum]
end Formalism.InvariantFactorPaths.ColumnFamilies
