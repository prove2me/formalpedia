-- Prove2me | solution 1 for FockRL.gradedOscillatorProperty_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:08.244194+00:00
-- url     : https://prove2.me/submissions/bd1cdcdf-9b7a-4d7e-bdb9-b275930d9e0b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_GradedOscillatorPropertyOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FockRL
namespace FockRL
theorem _root_.solution (hK : KCStep) (hP : PCStep) (hA : AdjStep) (hM : MatStep) : FockH1Action.H1 := by
  intro p q r s
  obtain ⟨e1, e2, k1, k2, o1, o2, c1, c2, a1, a2⟩ := hM p q r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ d P hP'
    rw [e1]; exact hK p q r s _ (k1 Z hZ) d P hP'
  · intro Z hZ d P hP'
    rw [e2]; exact hK p q r s _ (k2 Z hZ) d P hP'
  · intro Z hZ P
    rw [e1]; exact hP p q r s _ (o1 Z hZ) P
  · intro Z hZ P
    rw [e2]; exact hP p q r s _ (o2 Z hZ) P
  · intro Z hZ P Q
    rw [e1, e1]; exact hA p q r s _ _ (o1 Z hZ) (o1 _ (c1 Z hZ)) (a1 Z) P Q
  · intro Z hZ P Q
    rw [e2, e2]; exact hA p q r s _ _ (o2 Z hZ) (o2 _ (c2 Z hZ)) (a2 Z) P Q
end FockRL
