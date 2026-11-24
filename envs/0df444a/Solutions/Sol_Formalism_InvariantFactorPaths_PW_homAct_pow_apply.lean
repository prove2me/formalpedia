-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.homAct_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:57:40.616226+00:00
-- url     : https://prove2.me/submissions/03a7c302-0cea-42c6-813a-572980bc31cc

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_postC_pow_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_preC_pow_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_postC_preC_commute
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_eq

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
variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (k : ℕ)
    (φ : V →ₗ[K] W) (x : V) :
    ((homAct EV EW a b) ^ k) φ x =
      ∑ m ∈ antidiagonal k, ((k.choose m.1 : K) * (-1) ^ m.2) • ((EW a b) ^ m.1) (φ (((EV a b) ^ m.2) x)) := by
  have hc : Commute (postC (V := V) (EW a b)) ((-1 : K) • preC (W := W) (EV a b)) :=
    (postC_preC_commute (EW a b) (EV a b)).smul_right (-1 : K)
  have he : homAct EV EW a b = postC (EW a b) + (-1 : K) • preC (EV a b) := by
    rw [homAct_eq, neg_one_smul]
  rw [he, hc.add_pow', LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_pow, mul_smul_comm, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, postC_pow_apply, preC_pow_apply]
end Formalism.InvariantFactorPaths.PW
