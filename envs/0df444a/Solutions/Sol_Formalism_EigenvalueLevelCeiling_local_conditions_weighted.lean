-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.local_conditions_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:23.674721+00:00
-- url     : https://prove2.me/submissions/ed7b4a7c-91ac-4a3d-869a-e616fd3ecfd1

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_enlarge_initial_lattice
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_local_conditions_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : LocalConditionsWeighted := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hk h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  have hT0' := enlarge_initial_lattice K Z w M Th1 Th hM hTh1 hTh h1le hle (E : ℝ) r hT0
  have hc' : (θ'.restrictScalars (𝓞 K)) ∘ₗ (eX.restrictScalars (𝓞 K)) =
      (e.restrictScalars (𝓞 K)) ∘ₗ (θ'.restrictScalars (𝓞 K)) :=
    LinearMap.ext fun x => LinearMap.congr_fun hc x
  have hk' : ∀ x ∈ LinearMap.range (eX.restrictScalars (𝓞 K)),
      x - (pr.restrictScalars (𝓞 K)) x ∈ LinearMap.ker (θ'.restrictScalars (𝓞 K)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (hk _ (LinearMap.mem_range_self eX y)))
  have hid := theta_identity (𝓞 K) X Z (θ'.restrictScalars (𝓞 K)) (eX.restrictScalars (𝓞 K))
    (pr.restrictScalars (𝓞 K)) (e.restrictScalars (𝓞 K)) hc' hk' Mt
  exact local_conditions_family K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃
    ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0' h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj (hTj.trans hid)
end Formalism.EigenvalueLevelCeiling
