-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.isClosed_lowW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:55.468732+00:00
-- url     : https://prove2.me/submissions/936e594c-d5a4-44b1-b4ac-5432ac4954bf

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_lowUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_mem_lowW_iff

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
    [T2Space K] (s : List ℕ) (t : ℕ → Kˣ) (wi : Matrix (Fin s.sum) (Fin s.sum) K)
    (h1 : wi * pt s t = 1) (h2 : pt s t * wi = 1) :
    IsClosed (lowW K s t : Set (GL (Fin s.sum) K)) := by
  have hset : (lowW K s t : Set (GL (Fin s.sum) K)) =
      (fun g : GL (Fin s.sum) K => (g : Matrix (Fin s.sum) (Fin s.sum) K)) ⁻¹' {x | IsLowUni x} ∩
      (fun g : GL (Fin s.sum) K => wi * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) ⁻¹'
        {x | IsLowUni x} := by
    ext g; exact mem_lowW_iff s t wi h1 h2 g
  rw [hset]
  exact (isClosed_lowUni.preimage Units.continuous_val).inter (isClosed_lowUni.preimage
    ((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const))
end Formalism.DoubleCosetMeasures.P.Supp
