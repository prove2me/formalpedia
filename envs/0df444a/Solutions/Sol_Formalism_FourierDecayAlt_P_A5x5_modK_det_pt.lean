-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.modK_det_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:42.243508+00:00
-- url     : https://prove2.me/submissions/9eee9761-e6b2-498e-aaa5-65971377a4a2

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (s : List ℕ) (t : ℕ → Kˣ) :
    modK R (pt s t).det = modK R (∏ a : Fin s.sum, ((t (blk s a) : Kˣ) : K)) := by
  set σ : Equiv.Perm (Fin s.sum) :=
    Function.Involutive.toPerm (Formalism.DoubleCosetMeasures.P.Phase.revF s)
      (show Function.Involutive (Formalism.DoubleCosetMeasures.P.Phase.revF s) from Formalism.DoubleCosetMeasures.P.Phase.revF_revF s) with hσ
  have hpt : pt s t = Matrix.diagonal (fun a : Fin s.sum => ((t (blk s a) : Kˣ) : K)) *
      (σ.toPEquiv.toMatrix : Matrix (Fin s.sum) (Fin s.sum) K) := by
    ext a b
    simp only [Formalism.DoubleCosetMeasures.pt, Matrix.diagonal_mul, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, hσ, Function.Involutive.coe_toPerm]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (Fin.ext (by simp only [Function.Involutive.coe_toPerm, Formalism.DoubleCosetMeasures.P.Phase.revF_val]; exact h1.symm)) h2
    · exact absurd (by rw [← h2]; simp only [Function.Involutive.coe_toPerm, Formalism.DoubleCosetMeasures.P.Phase.revF_val]) h1
    · simp
  rw [hpt, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp [modK_neg]
end Formalism.FourierDecayAlt.P.A5x5
