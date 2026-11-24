-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.op_letter_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:54.423721+00:00
-- url     : https://prove2.me/submissions/f8bfa88c-9892-43b8-a221-a878f2fac605

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_vf_true
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_vf_false
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
theorem _root_.solution {f : Mat k r → E} {X Y g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hY : inLie k r Y) (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) (hg : g ∈ GV k r) :
    op b (X + Y) f g = op b X f g + op b Y f g := by
  unfold CkOn at hf
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g hg
  rw [op_eq_op' 0 b hU hc hff (inLie_add hX hY) g hgU hg, op_eq_op' 0 b hU hc hff hX g hgU hg,
    op_eq_op' 0 b hU hc hff hY g hgU hg]
  simp only [op']
  have hv : vf b (X + Y) g = vf b X g + vf b Y g := by
    cases b
    · rw [vf_false, vf_false, vf_false, Matrix.mul_add]
    · rw [vf_true, vf_true, vf_true, Matrix.add_mul, neg_add]
  rw [hv, map_add]
end Formalism.FourierDecayAlt.P.B4
