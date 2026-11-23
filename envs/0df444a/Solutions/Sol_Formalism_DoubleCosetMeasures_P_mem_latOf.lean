-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.mem_latOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:25.633799+00:00
-- url     : https://prove2.me/submissions/c46edb46-c5a5-4c10-ab14-a6ece1d1a4e4

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (g : GL (Fin n) K) (w : Fin n → K) :
    w ∈ latOf R g ↔ ∃ v : Fin n → R, (g : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (v j : K)) = w := by
  unfold latOf
  simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  rfl
end Formalism.DoubleCosetMeasures.P
