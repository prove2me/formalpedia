-- Prove2me | solution 1 for Formalism.L2.Th1.F.elliptic_no_pole_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:39.793063+00:00
-- url     : https://prove2.me/submissions/873ee18a-8bfb-4f76-bbf5-0244ce0f01a2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Theorems.Thm_Formalism_L2_Th1_F_elliptic_entire_const
import Theorems.Thm_Formalism_L2_Th1_F_Elliptic_eq_of_eventuallyEq_nhdsNE
import Theorems.Thm_Formalism_L2_Th1_F_Elliptic_tendsto_add_nhdsNE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : EllipticNoPole := by
  intro L f hmer hper hord
  have hM : MeromorphicOn f Set.univ := fun z _ => hmer z
  set g := toMeromorphicNFOn f Set.univ with hg_def
  have heq : ∀ z, g =ᶠ[𝓝[≠] z] f := fun z =>
    hM.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han : ∀ z, AnalyticAt ℂ g z := fun z => by
    have hnf := meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ z)
    rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_congr (heq z)]
    exact hord z
  have hcont : ∀ z, ContinuousAt g z := fun z => (han z).continuousAt
  have hdiff : Differentiable ℂ g := fun z => (han z).differentiableAt
  have hpg : IsPeriodic L g := by
    intro ω hω z
    have hc1 : ContinuousAt (fun w => g (w + ω)) z :=
      show ContinuousAt (g ∘ fun w => w + ω) z from
        (hcont (z + ω)).comp_of_eq (continuous_add_right ω).continuousAt rfl
    have h1 : ∀ᶠ w in 𝓝[≠] z, g (w + ω) = f (w + ω) :=
      (Elliptic.tendsto_add_nhdsNE z ω).eventually (heq (z + ω))
    have h2 : (fun w => g (w + ω)) =ᶠ[𝓝[≠] z] g := by
      filter_upwards [h1, heq z] with w hw1 hw2
      rw [hw1, hper ω hω w, hw2]
    exact Elliptic.eq_of_eventuallyEq_nhdsNE hc1 (hcont z) h2
  refine ⟨g 0, fun z hz => ?_⟩
  rw [← elliptic_entire_const L g hdiff hpg z]
  exact Elliptic.eq_of_eventuallyEq_nhdsNE hz (hcont z) (heq z).symm
end Formalism.L2.Th1.F
