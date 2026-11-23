-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.isClosed_upUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:35.200888+00:00
-- url     : https://prove2.me/submissions/b075c0ee-aab2-4374-8312-ac3d2d92780a

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution [T2Space K] (n : ℕ) :
    IsClosed {x : Matrix (Fin n) (Fin n) K | IsUpUni x} := by
  have e : {x : Matrix (Fin n) (Fin n) K | IsUpUni x} =
      (⋂ i, ⋂ j, ⋂ (_ : j < i), {x | x i j = 0}) ∩ ⋂ a, {x | x a a = 1} := by
    ext x; simp [IsUpUni, Matrix.IsUpperTriangular, Matrix.BlockTriangular]
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
