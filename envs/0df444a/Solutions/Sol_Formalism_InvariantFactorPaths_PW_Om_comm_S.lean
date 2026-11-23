-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_comm_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:55.176515+00:00
-- url     : https://prove2.me/submissions/4a3f9583-11c7-4a28-9694-222b2d3b0969

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_der3
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
theorem _root_.solution (h : GlRel E) {S : Finset ι} {z : ι} (hz : z ∉ S) {a b : ι} (ha : a ∈ S) (hb : b ∈ S)
    (q : ℕ) : E a b * Om E S z q = Om E S z q * E a b := by
  have hbz : b ≠ z := fun e => hz (e ▸ hb)
  have haz : a ≠ z := fun e => hz (e ▸ ha)
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    have key : ∀ i, E a b * (E z i * Om E S z q * E i z) =
        E z i * Om E S z q * E i z * E a b +
          ((if i = b then E z b * Om E S z q * E a z else 0) -
            (if i = a then E z b * Om E S z q * E a z else 0)) := by
      intro i
      have ho : E a b * Om E S z q = Om E S z q * E a b + 0 := by rw [ih, add_zero]
      rw [der3 _ _ _ _ _ _ _ (h.sw a b z i) ho (h.sw a b i z)]
      congr 1
      have hza : ¬ z = a := fun e => haz e.symm
      simp only [if_neg hbz, if_neg hza]
      by_cases hia : i = a <;> by_cases hib : i = b
      · subst hia; subst hib; simp
      · subst hia; simp [hib, Ne.symm hib]
      · subst hib; simp [hia]
      · simp [hia, hib, Ne.symm hib]
    simp only [Om]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hb, if_pos ha, sub_self, add_zero]
end Formalism.InvariantFactorPaths.PW
