-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.congSub_open
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:18.89203+00:00
-- url     : https://prove2.me/submissions/c29158f7-253e-453a-9181-42bea298e666

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.GLRed
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
namespace Formalism.DoubleCosetMeasures.P.GLRed
theorem _root_.solution (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (a : ℕ) :
    IsOpen (congSub O ϖ a : Set (GL (Fin a) F)) := by
  have e : (congSub O ϖ a : Set (GL (Fin a) F)) =
      ((⋂ i, ⋂ j, (fun g : GL (Fin a) F => (g : Matrix (Fin a) (Fin a) F) i j) ⁻¹' (O : Set F)) ∩
      (⋂ i, ⋂ j, (fun g : GL (Fin a) F =>
        ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j) ⁻¹' (O : Set F))) ∩
      (⋂ i, ⋂ j, (fun g : GL (Fin a) F =>
        ϖ⁻¹ * ((g : Matrix (Fin a) (Fin a) F) i j - (1 : Matrix (Fin a) (Fin a) F) i j)) ⁻¹'
          (O : Set F)) := by
    ext g; simp [congSub, GLint, IsInt]
  rw [e]
  refine IsOpen.inter (IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite
    fun j => hO.preimage ?_) (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite
    fun j => hO.preimage ?_)) (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite
    fun j => hO.preimage ?_)
  · exact Units.continuous_val.matrix_elem i j
  · exact Units.continuous_coe_inv.matrix_elem i j
  · exact continuous_const.mul ((Units.continuous_val.matrix_elem i j).sub continuous_const)
end Formalism.DoubleCosetMeasures.P.GLRed
