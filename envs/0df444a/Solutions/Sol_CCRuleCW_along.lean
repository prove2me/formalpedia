-- Prove2me | solution 1 for CCRuleCW.along
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:56.952148+00:00
-- url     : https://prove2.me/submissions/b72727c5-c2f3-4bc9-855f-11601fdce924

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_curve_zero
import Theorems.Thm_CCRuleCW_curve_mem
import Theorems.Thm_CCRuleCW_curve_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (H : B.Mat k r → E) {U : Set (B.Mat k r)} {f' : B.Mat k r → E} (hU : IsOpen U)
    (hf' : ContDiffOn ℝ ∞ f' U) (hagree : ∀ g ∈ U, g ∈ B.GV k r → H g = f' g)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (g : B.Mat k r) (hgU : g ∈ U) (hg : g ∈ B.GV k r) :
    HasDerivAt (fun t => H (curve o g t)) (fderiv ℝ f' g (dir o g)) 0 := by
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
  have hc := curve_hasDerivAt o g
  have h1 : HasDerivAt (f' ∘ curve o g) (fderiv ℝ f' g (dir o g)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (curve_zero o g).symm
  refine h1.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (curve o g) 0 := hc.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), curve o g t ∈ U :=
    hcont.preimage_mem_nhds (by rw [curve_zero]; exact hU.mem_nhds hgU)
  filter_upwards [hev] with t ht
  exact hagree _ ht (curve_mem o g t hX hg)
end CCRuleCW
