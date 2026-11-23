-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.piece_sub_mul_cong
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:32.897559+00:00
-- url     : https://prove2.me/submissions/ff201cf6-0237-4611-a81e-185693f196c2

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mem_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_one_add_mem_cong

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
theorem _root_.solution (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} {g : GL (Fin a) F} (hg : g ∈ GLint O a)
    {m : Matrix (Fin a) (Fin a) F} (hm : m ∈ piece O ϖ (g : Matrix (Fin a) (Fin a) F)) :
    ∃ k ∈ congSub O ϖ a, (((g * k : GL (Fin a) F)) : Matrix (Fin a) (Fin a) F) = m := by
  rw [mem_piece] at hm
  choose o ho hmo using hm
  have hY : IsInt O (Matrix.of o) := fun i j => ho i j
  have hgi : IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) := hg.2
  obtain ⟨k, hk, hkw⟩ := one_add_mem_cong O ϖ hϖ hϖ0 hloc _ (isInt_mul' O hgi hY)
  refine ⟨k, hk, ?_⟩
  rw [Units.val_mul, hkw, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  linear_combination -(hmo i j)
end Formalism.DoubleCosetMeasures.P.Vol
