-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.op_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:55.710187+00:00
-- url     : https://prove2.me/submissions/093f140f-e247-4558-8c28-0d1fd7a9d8e0

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cast_ne_zero
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
theorem _root_.solution {f f₂ : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) (hf₂ : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f₂) (hg : g ∈ GV k r) :
    op b X (f + f₂) g = op b X f g + op b X f₂ g := by
  unfold CkOn at hf hf₂
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := hf g hg
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := hf₂ g hg
  have hU := hU₁.inter hU₂
  have hgU : g ∈ U₁ ∩ U₂ := ⟨hg₁, hg₂⟩
  have hc₁' := hc₁.mono (Set.inter_subset_left (s := U₁) (t := U₂))
  have hc₂' := hc₂.mono (Set.inter_subset_right (s := U₁) (t := U₂))
  have d1 : DifferentiableAt ℝ f₁' g :=
    (hc₁'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (cast_ne_zero 0)
  have d2 : DifferentiableAt ℝ f₂' g :=
    (hc₂'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (cast_ne_zero 0)
  rw [op_eq_op' (f := f + f₂) 0 b hU (hc₁'.add hc₂')
      (fun h hh hG => by
        simp only [Pi.add_apply]
        rw [he₁ h hh.1 hG, he₂ h hh.2 hG]) hX g hgU hg,
    op_eq_op' 0 b hU hc₁' (fun h hh hG => he₁ h hh.1 hG) hX g hgU hg,
    op_eq_op' 0 b hU hc₂' (fun h hh hG => he₂ h hh.2 hG) hX g hgU hg]
  simp only [op']
  exact congrArg (fun L => L (vf b X g)) (d1.hasFDerivAt.add d2.hasFDerivAt).fderiv
end Formalism.FourierDecayAlt.P.B4
