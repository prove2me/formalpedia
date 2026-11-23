-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.map_zsub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:39.088913+00:00
-- url     : https://prove2.me/submissions/5e91f748-19b6-473e-9f4d-cfdcc9162658

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (B : FI E) (hB : B ≠ 0) :
    (zsub E B).map (emb E) = mixedEmbedding.idealLattice E (Units.mk0 B hB) := by
  ext x
  rw [mixedEmbedding.mem_idealLattice, Submodule.mem_map]
  rfl
end Formalism.FourierDecayAlt.P.S6x5
