-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:22.123912+00:00
-- url     : https://prove2.me/submissions/df0f4c47-0e12-40b5-bf57-774b0f7eaf1c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_eq_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_inLie_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_false
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_op_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_vf_false
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) :
    RdV X (RdV Y Φ) g - RdV Y (RdV X Φ) g = RdV (X * Y - Y * X) Φ g := by
  obtain ⟨U, Φ', hU, hgU, hc, he⟩ := hloc
  have hc2 : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) Φ' U := by
    have : (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) := by norm_num
    rw [this]; exact hc
  have h1 := B4.op_op_ext false false hU hc2 he hX hY hgU hgG
  have h2 := B4.op_op_ext false false hU hc2 he hY hX hgU hgG
  simp only [B4.op_false, B4.vf_false] at h1 h2
  rw [h1, h2, rdV_eq_fderiv (m := 2) (by norm_num) hU hgU hgG hc he (inLie_comm hX hY)]
  have hsym : IsSymmSndFDerivAt ℝ Φ' g :=
    (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs := hsym (g * X) (g * Y)
  have e3 : (fderiv ℝ Φ' g) (g * (X * Y - Y * X)) =
      (fderiv ℝ Φ' g) (g * X * Y) - (fderiv ℝ Φ' g) (g * Y * X) := by
    rw [Matrix.mul_sub, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e3]
  have key : ∀ (a a' b c : E), a = a' → a + b - (a' + c) = b - c := by
    intro a a' b c h; rw [h]; abel
  exact key _ _ _ _ hs
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
