-- Prove2me | solution 1 for Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.hasDerivAt_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:42.801183+00:00
-- url     : https://prove2.me/submissions/57b89b08-9ef4-4097-86b6-c3f940ca6d74

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
namespace Formalism.L2.Th1.F
namespace AnalyticIdentityTheoremsZetaFacts
private lemma hasDerivAt_inv_sub_add_inv_add_div_sq (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have h2 : HasDerivAt (fun w : ℂ => (w - l)⁻¹) (-((z - l) ^ 2)⁻¹ * 1) z :=
    (hasDerivAt_inv h).comp z ((hasDerivAt_id' z).sub_const l)
  have h4 := (h2.add_const (1 / l)).add ((hasDerivAt_id' z).div_const (l ^ 2))
  have e : (fun w : ℂ => 1 / (w - l) + 1 / l + w / l ^ 2) =
      fun w => (w - l)⁻¹ + 1 / l + w / l ^ 2 := by
    funext w
    rw [one_div]
  rw [e]
  exact h4.congr_deriv (by ring)
end AnalyticIdentityTheoremsZetaFacts
open AnalyticIdentityTheoremsZetaFacts
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
theorem _root_.solution (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  exact hasDerivAt_inv_sub_add_inv_add_div_sq l z h
end Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
