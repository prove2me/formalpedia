-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.pert_lamLin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:49.859522+00:00
-- url     : https://prove2.me/submissions/5dcd5d18-895b-4ecb-a773-5b28aff9e39d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
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



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {N : ℕ} (Z Z₁ W : Matrix (Fin N) (Fin N) K) (hW : IsInt R W)
    (h : Z₁⁻¹ = Z⁻¹ - W) (v : Fin N → R) : lamLin R Z₁ v = lamLin R Z v := by
  unfold lamLin
  have hc : ∀ w : Fin N → R, coeLin R w = fun i => ((w i : R) : K) := fun w => rfl
  have hWv : W *ᵥ coeLin R v =
      coeLin R ((Matrix.of fun i j => (⟨W i j, hW i j⟩ : R)) *ᵥ v) := by
    rw [hc, hc]
    funext i
    exact (RingHom.map_mulVec R.subtype (Matrix.of fun i j => (⟨W i j, hW i j⟩ : R)) v i).symm
  have hq : ∀ u : Fin N → R,
      (LinearMap.range (Algebra.linearMap R K)).mkQ (lastCoord R (coeLin R u)) = 0 := by
    intro u
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    unfold lastCoord
    rw [LinearMap.sum_apply]
    refine sum_mem fun j _ => ?_
    split_ifs
    · exact LinearMap.mem_range.2 ⟨u j, rfl⟩
    · simp
  show (LinearMap.range (Algebra.linearMap R K)).mkQ (lastCoord R (Z₁⁻¹ *ᵥ coeLin R v)) =
    (LinearMap.range (Algebra.linearMap R K)).mkQ (lastCoord R (Z⁻¹ *ᵥ coeLin R v))
  rw [h, Matrix.sub_mulVec, map_sub, map_sub, hWv, hq, sub_zero]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
