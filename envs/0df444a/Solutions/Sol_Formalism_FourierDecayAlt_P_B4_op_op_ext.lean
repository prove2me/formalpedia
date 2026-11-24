-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.op_op_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:50.229671+00:00
-- url     : https://prove2.me/submissions/56969850-a3b1-4fdd-be04-e72866802045

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_natCast_succ_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cast_ne_zero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B4_op__contDiffOn_a13b807b4df6
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {f f' : Mat k r → E} {U : Set (Mat k r)} {X Y g : Mat k r} (b b' : Bool)
    (hU : IsOpen U) (hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) (hY : inLie k r Y)
    (hg : g ∈ U) (hgG : g ∈ GV k r) :
    op b X (op b' Y f) g =
      fderiv ℝ (fderiv ℝ f') g (vf b X g) (vf b' Y g) + fderiv ℝ f' g (vf b' Y (vf b X g)) := by
  rw [op_eq_op' 0 b hU (op'_contDiffOn 1 b' Y hU hc) (op_eq_op' 1 b' hU hc hff hY) hX g hg hgG]
  have hd : DifferentiableAt ℝ (fderiv ℝ f') g :=
    ((hc.fderiv_of_isOpen hU (natCast_succ_le 1)).differentiableOn (cast_ne_zero 0)).differentiableAt
      (hU.mem_nhds hg)
  have H := (hd.hasFDerivAt.clm_apply (vf b' Y).hasFDerivAt).fderiv
  unfold op'
  erw [H]
  exact add_comm _ _
end Formalism.FourierDecayAlt.P.B4
