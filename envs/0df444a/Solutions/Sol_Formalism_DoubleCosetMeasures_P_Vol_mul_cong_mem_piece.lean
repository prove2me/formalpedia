-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.mul_cong_mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:26.821927+00:00
-- url     : https://prove2.me/submissions/98dafeb1-40f7-4863-b2c9-451ced908b0d

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mem_piece

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
variable {F : Type} [Field F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (ϖ : F) (hϖ0 : ϖ ≠ 0) {a : ℕ} {g k : GL (Fin a) F}
    (hg : g ∈ GLint O a) (hk : k ∈ congSub O ϖ a) :
    (((g * k : GL (Fin a) F)) : Matrix (Fin a) (Fin a) F) ∈
      piece O ϖ (g : Matrix (Fin a) (Fin a) F) := by
  have hgI : IsInt O (g : Matrix (Fin a) (Fin a) F) := hg.1
  have hk1 : IsInt O (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1)) := hk.2
  rw [mem_piece]
  intro i j
  refine ⟨((g : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1))) i j,
    isInt_mul' O hgI hk1 i j, ?_⟩
  have e : ((g * k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - g =
      ϖ • ((g : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((k : Matrix (Fin a) (Fin a) F) - 1))) := by
    rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hϖ0, one_smul, Matrix.mul_sub,
      Matrix.mul_one, Units.val_mul]
  have h1 := congrFun (congrFun e i) j
  simpa [Matrix.sub_apply, Matrix.smul_apply] using h1
end Formalism.DoubleCosetMeasures.P.Vol
