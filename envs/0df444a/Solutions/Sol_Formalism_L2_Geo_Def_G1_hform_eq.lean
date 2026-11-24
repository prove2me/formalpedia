-- Prove2me | solution 1 for Formalism.L2.Geo.Def.G1.hform_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:34.916489+00:00
-- url     : https://prove2.me/submissions/ca5bdb7b-7bf4-4e9b-b0da-0d26a7436313

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.L2.Geo.Def.G1
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = Formalism.UG.hform (starRingEnd K) H x y := by
  simp [Formalism.DivisionValues.hform, Formalism.UG.hform, Matrix.toLinearMapₛₗ₂'_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end Formalism.L2.Geo.Def.G1
