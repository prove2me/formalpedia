-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.prod_places_hyperbolic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:23.224424+00:00
-- url     : https://prove2.me/submissions/03ad9c99-2b13-4c29-ad7f-461513f57800

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.ProdPlacesHyperbolicInequality := by
  intro ι _ T al n ch sh Nr hT hal hsh hch hbd hNr h1
  have hsq : ∀ v, T v * al v ^ 2 ≤ (n v * (1 + ch v) / sh v) ^ 2 := by
    intro v
    have h0 : 0 ≤ Real.sqrt (T v) * al v := mul_nonneg (Real.sqrt_nonneg _) (hal v)
    have h2 := pow_le_pow_left₀ h0 (hbd v) 2
    rwa [mul_pow, Real.sq_sqrt (hT v).le] at h2
  have hprod : (∏ v, T v) * ∏ v, al v ^ 2 ≤ (∏ v, n v ^ 2) * ∏ v, ((1 + ch v) / sh v) ^ 2 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v _
      exact mul_nonneg (hT v).le (sq_nonneg _)
    · intro v _
      calc T v * al v ^ 2 ≤ (n v * (1 + ch v) / sh v) ^ 2 := hsq v
        _ = n v ^ 2 * ((1 + ch v) / sh v) ^ 2 := by ring
  have hTpos : 0 ≤ ∏ v, T v := Finset.prod_nonneg fun v _ => (hT v).le
  calc (∏ v, T v) / Nr ≤ (∏ v, T v) * ∏ v, al v ^ 2 := by
        rw [div_le_iff₀ hNr]
        calc (∏ v, T v) = (∏ v, T v) * 1 := (mul_one _).symm
          _ ≤ (∏ v, T v) * ((∏ v, al v ^ 2) * Nr) := mul_le_mul_of_nonneg_left h1 hTpos
          _ = (∏ v, T v) * (∏ v, al v ^ 2) * Nr := by ring
    _ ≤ _ := hprod
end Formalism.SLP.GlobalBoundRefinements.P
