-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.isClosed_upUniG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:09.771614+00:00
-- url     : https://prove2.me/submissions/bb7f1891-78a3-4930-afe7-0c8c6f30406f

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_upUni

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
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (n : ℕ) : IsClosed (upUniG K n : Set (GL (Fin n) K)) := by
  have hset : (upUniG K n : Set (GL (Fin n) K)) =
      (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) ⁻¹' {x | IsUpUni x} := by
    ext g; exact Iff.rfl
  rw [hset]
  exact isClosed_upUni.preimage Units.continuous_val
end Formalism.DoubleCosetMeasures.P.Supp
