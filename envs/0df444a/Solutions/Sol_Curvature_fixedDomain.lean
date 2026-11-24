-- Prove2me | solution 1 for Curvature.fixedDomain
-- status  : ACCEPTED   (prove)
-- author  : @ssakaue
-- created : 2026-11-24T07:31:16.94813+00:00
-- url     : https://prove2.me/submissions/42169e59-0068-49c3-a448-c8aeb0379f09

import Definitions.Def_Curvature_AdaptivePredictor

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d : ℕ} {K : Set (Vec d)}


namespace DomainInitialization


theorem adaptiveBase_cost (I : DomainInitialization K) (hne : K.Nonempty) (hc : IsCompact K)
    (hcv : Convex ℝ K) : (I.adaptiveBase hne hc hcv).cost ≤ 393216*coordinateWidth K := by
  cases I with
  | dyadic D h => change 192*D.representationCost ≤ _; linarith
  | fixed center A ha hq hq' hgram hbody mode =>
    change 164*coordinateWidth K ≤ _
    have h := (AdaptiveBase.fixedAxes hne hc hcv center A ha hq hq' hgram hbody mode).cost_nonneg
    change 0 ≤ 164*coordinateWidth K at h
    linarith

end DomainInitialization


end Curvature
end
end

set_option autoImplicit false
noncomputable section
open Curvature
variable {d : ℕ} {K : Set (Vec d)}

theorem solution (hc : IsCompact K) (hcv : Convex ℝ K) (hnon : K.Nontrivial)
    (I : DomainInitialization K) {G ε : ℝ} (hG : 0 < G) (hε : 0 < ε) (hε' : ε ≤ 1)
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (u : K) (T : ℕ) :
    let w := (I.adaptiveBase hnon.nonempty hc hcv).play G ε g
    let r := fun t => excess (g t) (w t).val u.val
    2*(∑ t ∈ Finset.range T, r t) - ε*(∑ t ∈ Finset.range T, |r t|) ≤
      (393216*G/ε)*coordinateWidth K := by
  let B := I.adaptiveBase hnon.nonempty hc hcv
  have h := B.playedRegret hG hε hε' g hg u T
  have hc' := mul_le_mul_of_nonneg_left (I.adaptiveBase_cost hnon.nonempty hc hcv)
    (div_nonneg hG.le hε.le)
  calc
    _ ≤ G*B.cost/ε := h
    _ = G/ε*B.cost := by ring
    _ ≤ G/ε*(393216*coordinateWidth K) := hc'
    _ = _ := by ring
