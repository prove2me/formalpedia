-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.meas_ii
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:46.041463+00:00
-- url     : https://prove2.me/submissions/ef222815-c1bd-4ac7-96a4-bb6a211f5e34

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_iiset_eq

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
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ0 : ϖ ≠ 0) (n a : ℕ) :
    MeasurableSet (IIset O ϖ : Set (Matrix (Fin n) (Fin a) F)) := by
  rw [iiset_eq O ϖ hϖ0]
  have hOm : MeasurableSet (O : Set F) := hO.measurableSet
  have e : {y : Matrix (Fin n) (Fin a) F | ∀ i j, ϖ⁻¹ * y i j ∈ O} =
      ⋂ i, ⋂ j, (fun y : Matrix (Fin n) (Fin a) F => ϖ⁻¹ * y i j) ⁻¹' (O : Set F) := by
    ext y
    simp
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  exact ((continuous_mul_left ϖ⁻¹).measurable.comp
    ((measurable_pi_apply j).comp (measurable_pi_apply i))) hOm
end Formalism.DoubleCosetMeasures.P.Vol
