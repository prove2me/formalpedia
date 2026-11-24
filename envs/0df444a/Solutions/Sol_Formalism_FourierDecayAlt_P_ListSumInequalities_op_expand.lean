-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.op_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:52:03.365353+00:00
-- url     : https://prove2.me/submissions/416f1063-f4f6-4124-9612-f481b26d9993

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_vf_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Lt_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_expandL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution {H : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) (hg : g ∈ GV k r) :
    op b X H g = ∑ i, kc i X • op b (Lt i) H g := by
  obtain ⟨U, f', hU, hgU, hf', heq⟩ := hH g hg
  have hd : DifferentiableAt ℝ f' g := (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hop : ∀ Z, inLie k r Z → op b Z H g = fderiv ℝ f' g (vf b Z g) := fun Z hZ =>
    (hasDerivAt_ext (f := H) b hU hgU hg hd heq hZ).deriv
  rw [hop X hX]
  conv_lhs => rw [expandL hX]
  rw [vf_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hop _ (Lt_unit i).1]
end Formalism.FourierDecayAlt.P.ListSumInequalities
