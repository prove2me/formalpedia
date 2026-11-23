-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.ker_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:53.193996+00:00
-- url     : https://prove2.me/submissions/dcb3ba1f-a71c-4b40-b38a-642d74db3296

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_red_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_mem_span_iff
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_one_kF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_one_coe

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
variable {F : Type} [Field F] (O : Subring F) {a : ℕ}
variable (a)
variable (ϖ : F) (hϖ : ϖ ∈ O)
variable {a}
namespace Formalism.DoubleCosetMeasures.P.GLRed
theorem _root_.solution (hϖ0 : ϖ ≠ 0) :
    (red O a ϖ hϖ).ker = (congSub O ϖ a).subgroupOf (GLint O a) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change _ ↔ (g : GL (Fin a) F) ∈ GLint O a ∧ _
  have key : ∀ i j, ((red O a ϖ hϖ g : GL (Fin a) (kF O ϖ hϖ)) : Matrix (Fin a) (Fin a) _) i j =
      (1 : Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) i j ↔
      (ϖ⁻¹ • (((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - 1)) i j ∈ O := by
    intro i j
    rw [red_val, one_kF, Ideal.Quotient.eq, mem_span_iff O ϖ hϖ hϖ0]
    simp [Matrix.smul_apply, Matrix.sub_apply, one_coe]
  constructor
  · intro h
    refine ⟨g.2, fun i j => (key i j).1 ?_⟩
    rw [h]; rfl
  · rintro ⟨-, h⟩
    apply Units.ext; ext i j
    exact (key i j).2 (h i j)
end Formalism.DoubleCosetMeasures.P.GLRed
