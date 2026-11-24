-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.E_Om_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:19.505171+00:00
-- url     : https://prove2.me/submissions/92515df1-295b-429c-a37a-85faec241d18

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_E

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
theorem _root_.solution (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) {u : W}
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) (q : ℕ) :
    E j z (Om E S z (q + 1) u) = Om E S z (q + 1) (E j z u) +
      (((q : K) + 1) * ((q : K) + 1 + S.card)) • Om E S z q (E j z u) := by
  have h0 : ∑ i ∈ S, E i z (E j i u) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hS j hj i hi, map_zero])
  have hC : Cj E S z j u = ((S.card : K) + 1) • E j z u := by
    simp only [Cj, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply,
      LinearMap.smul_apply, hzz, map_zero, h0, sub_zero, zero_add]
  have e1 := DFunLike.congr_fun (Om_E h hz hj q) u
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hC] at e1
  rw [e1, ← add_smul, map_smul, smul_smul]
  congr 2
  ring
end Formalism.InvariantFactorPaths.PW
