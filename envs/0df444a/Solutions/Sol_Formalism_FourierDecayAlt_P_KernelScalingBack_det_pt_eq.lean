-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.det_pt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:56.479211+00:00
-- url     : https://prove2.me/submissions/9b4abf84-7584-4123-b19f-77e94f96bd54

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (s : List ℕ) : ∃ e : Kˣ, ∀ t : ℕ → Kˣ,
    (pt s t).det = (∏ a : Fin s.sum, ((t (blk s a) : Kˣ) : K)) * (e : K) := by
  let σ : Equiv.Perm (Fin s.sum) :=
    ⟨Formalism.DoubleCosetMeasures.P.Phase.revF s, Formalism.DoubleCosetMeasures.P.Phase.revF s, Formalism.DoubleCosetMeasures.P.Phase.revF_revF s,
      Formalism.DoubleCosetMeasures.P.Phase.revF_revF s⟩
  have e : ∀ t : ℕ → Kˣ,
      pt s t = diagonal (fun a : Fin s.sum => ((t (blk s a) : Kˣ) : K)) * σ.permMatrix K := by
    intro t
    ext a c
    rw [diagonal_mul]
    simp only [pt, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, mul_ite, mul_one, mul_zero]
    congr 1
    simp only [σ, Equiv.coe_fn_mk, Fin.ext_iff, Formalism.DoubleCosetMeasures.P.Phase.revF_val, eq_iff_iff]
    exact eq_comm
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact ⟨1, fun t => by rw [e, det_mul, det_diagonal, det_permutation, h]; simp⟩
  · exact ⟨-1, fun t => by rw [e, det_mul, det_diagonal, det_permutation, h]; simp⟩
end Formalism.FourierDecayAlt.P.KernelScalingBack
