-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.op_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:40:54.161858+00:00
-- url     : https://prove2.me/submissions/3bdda7c4-d144-444b-b261-108f2daae80c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_vf_true
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_vf_false
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_op_ext

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
theorem _root_.solution {f : Mat k r → E} {X Y g : Mat k r} (hf : CkOn ((2 : ℕ) : ℕ∞) (GV k r) f)
    (hX : inLie k r X) (hY : inLie k r Y) (hg : g ∈ GV k r) :
    op false Y (op true X f) g = op true X (op false Y f) g := by
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g hg
  rw [op_op_ext false true hU hc hff hY hX hgU hg, op_op_ext true false hU hc hff hX hY hgU hg]
  have hsym : IsSymmSndFDerivAt ℝ f' g :=
    (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have h1 := hsym (vf false Y g) (vf true X g)
  have h2 : vf true X (vf false Y g) = vf false Y (vf true X g) := by
    simp [vf_true, vf_false, Matrix.mul_assoc]
  rw [h2]
  exact congrArg (· + fderiv ℝ f' g (vf false Y (vf true X g))) h1
end Formalism.FourierDecayAlt.P.B4
