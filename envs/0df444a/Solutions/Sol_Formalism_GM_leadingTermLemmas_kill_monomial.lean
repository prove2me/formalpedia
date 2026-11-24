-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.kill_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:48.212145+00:00
-- url     : https://prove2.me/submissions/fa3c9658-d303-44ca-aa7d-9b8942722751

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
variable (P : σ → Prop) [DecidablePred P]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (M : σ →₀ ℕ) (a : K) :
    kill P (monomial M a) = if (∀ v, P v → M v = 0) then monomial M a else 0 := by
  unfold kill
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  split_ifs with h
  · rw [monomial_eq]
    congr 1
    refine Finsupp.prod_congr (fun v hv => ?_)
    have : ¬ P v := fun hp => (Finsupp.mem_support_iff.mp hv) (h v hp)
    rw [if_neg this]
  · push Not at h
    obtain ⟨v, hp, hv⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hv) (by rw [if_pos hp, zero_pow hv]),
      mul_zero]
end Formalism.GM.leadingTermLemmas
