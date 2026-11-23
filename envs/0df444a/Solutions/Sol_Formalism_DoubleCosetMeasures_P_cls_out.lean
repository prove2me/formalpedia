-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.cls_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:27.484802+00:00
-- url     : https://prove2.me/submissions/538a3fe8-298b-4b0e-9748-af24c24633d1

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided

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
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) :
    clsTS K₁ K₂ (p.1.out, p.2.out) = p := by
  simp only [clsTS, Quotient.out_eq, QuotientGroup.out_eq']
end Formalism.DoubleCosetMeasures.P
