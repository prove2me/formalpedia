-- Prove2me | solution 1 for CCRuleCW.curve_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:59:54.979882+00:00
-- url     : https://prove2.me/submissions/c5ee34c6-c2fc-4483-8f05-6f38b624ac59

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_entry_hasDerivAt

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
theorem _root_.solution (o : Bool × B.Mat k r) (g : B.Mat k r) :
    HasDerivAt (curve o g) (dir o g) 0 := by
  rcases o with ⟨_ | _, X⟩
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    show HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j) ((g * X) i j) 0
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => g i l * NormedSpace.exp ((t : ℂ) • X) l j)
      fun l _ => (entry_hasDerivAt X l j).const_mul (g i l)
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    show HasDerivAt (fun t : ℝ => (NormedSpace.exp (-((t : ℂ) • X)) * g) i j) ((-(X * g)) i j) 0
    have e : ∀ t : ℝ, -((t : ℂ) • X) = (t : ℂ) • (-X) := fun t => (smul_neg _ _).symm
    simp only [e, Matrix.mul_apply]
    have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => NormedSpace.exp ((t : ℂ) • (-X)) i l * g l j)
      fun l _ => (entry_hasDerivAt (-X) i l).mul_const (g l j)
    have hv : (-(X * g)) i j = ∑ l, (-X) i l * g l j := by
      simp [Matrix.mul_apply, Finset.sum_neg_distrib]
    rw [hv]
    exact this
end CCRuleCW
