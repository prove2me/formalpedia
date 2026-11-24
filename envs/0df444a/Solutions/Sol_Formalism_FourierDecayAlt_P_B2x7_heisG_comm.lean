-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.heisG_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:47:02.895004+00:00
-- url     : https://prove2.me/submissions/9f6c9ba5-29f1-4e39-829c-ea1b1dae1351

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_heisAct
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heisAct
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (g : Mat k (1 + r')) (hg : g ∈ GV k (1 + r')) (c : ℝ) (hc : g *ᵥ e0 k r' = (c : ℂ) • e0 k r')
    (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    g * heisG k r' v b = heisG k r' ((c : ℂ) • (g *ᵥ v)) ((c : ℂ) ^ 2 * b) * g := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro u
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, heisAct, heisAct]
  have h1 : herm (Hpk k (1 + r')) (g *ᵥ u) ((c : ℂ) • (g *ᵥ v)) = (c : ℂ) * herm (Hpk k (1 + r')) u v := by
    rw [herm_smul_right, herm_UH hg, Complex.conj_ofReal]
  have h2 : (c : ℂ) * herm (Hpk k (1 + r')) (g *ᵥ u) (e0 k r') = herm (Hpk k (1 + r')) u (e0 k r') := by
    rw [← herm_UH hg u (e0 k r'), hc, herm_smul_right, Complex.conj_ofReal]
  rw [h1, ← h2, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, hc]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.B2x7
