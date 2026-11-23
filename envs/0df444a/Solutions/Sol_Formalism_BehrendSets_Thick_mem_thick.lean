-- Prove2me | solution 1 for Formalism.BehrendSets.Thick.mem_thick
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:03.763939+00:00
-- url     : https://prove2.me/submissions/224a1928-b6c9-447e-9d33-3db3e31a5552

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Thick
namespace Formalism.BehrendSets.Thick
theorem _root_.solution {n : ℕ} {T : Finset ℕ} {u p : ZMod n} :
    p ∈ Formalism.BehrendSets.thick n T u ↔ ∃ t ∈ T, ((t : ℕ) : ZMod n) + u = p := by
  unfold Formalism.BehrendSets.thick
  simp only [Finset.mem_image]
end Formalism.BehrendSets.Thick
