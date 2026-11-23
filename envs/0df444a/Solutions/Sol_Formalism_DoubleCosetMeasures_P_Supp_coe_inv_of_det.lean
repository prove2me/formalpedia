-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.coe_inv_of_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:09.20903+00:00
-- url     : https://prove2.me/submissions/60a43a3f-f9cc-4f64-82fd-c6df80b6526e

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution {K : Type} [CommRing K] {n : ℕ} (g : GL (Fin n) K)
    (hg : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, hg, Ring.inverse_one, one_smul]
end Formalism.DoubleCosetMeasures.P.Supp
