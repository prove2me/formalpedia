-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:40.299708+00:00
-- url     : https://prove2.me/submissions/49d3140e-d56a-47be-97b9-a10903680240

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h : GlRel E) {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) {l : ℕ}
    (hev : ∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0)
    {S : Finset ι} {z : ι} (hz : z ∉ S) (q : ℕ) :
    ∀ (k : ℕ), ∀ x ∈ NN, E z z x = -(k : K) • x → l < k + q → Om E S z q x = 0 := by
  induction q with
  | zero =>
    intro k x hx hk hlt
    have hx0 : x = 0 :=
      hev z (-(k : ℤ)) x hx (by push_cast; exact hk) (by rw [abs_neg, Nat.abs_cast]; omega)
    simp [Om, hx0]
  | succ q ih =>
    intro k x hx hk hlt
    simp only [Om, LinearMap.sum_apply, Module.End.mul_apply]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    have hw : E z z (E i z x) = -((k + 1 : ℕ) : K) • E i z x := by
      have e1 := DFunLike.congr_fun (h.sw z z i z) x
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, if_neg (Ne.symm hiz),
        if_pos (rfl : z = z), LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e1
      rw [e1, hk, map_smul]
      push_cast
      module
    rw [ih (k + 1) (E i z x) (hN _ _ _ hx) hw (by omega), map_zero]
end Formalism.InvariantFactorPaths.PW
