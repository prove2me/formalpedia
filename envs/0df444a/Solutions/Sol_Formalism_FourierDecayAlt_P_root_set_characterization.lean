-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.root_set_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:57.01682+00:00
-- url     : https://prove2.me/submissions/b267f9b3-f1c6-45aa-a04c-dd72d589e732

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.RootSetSpec := by
  intro s a hs
  constructor
  · intro z
    simp [rootSet, Polynomial.mem_nthRoots hs]
  · intro ha
    have hprim := Complex.isPrimitiveRoot_exp s hs.ne'
    unfold rootSet
    rw [Multiset.toFinset_card_of_nodup (hprim.nthRoots_nodup ha), hprim.card_nthRoots]
    rw [if_pos (IsAlgClosed.exists_pow_nat_eq a hs)]
end Formalism.FourierDecayAlt.P
