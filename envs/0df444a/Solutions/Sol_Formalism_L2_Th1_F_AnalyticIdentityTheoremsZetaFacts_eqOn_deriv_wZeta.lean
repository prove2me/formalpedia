-- Prove2me | solution 1 for Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.eqOn_deriv_wZeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:01.335773+00:00
-- url     : https://prove2.me/submissions/72e789ae-880d-4892-8fe7-4fd861b2e55c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_hasSumLU_wZeta
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_hasDerivAt_term
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
private lemma hasSum_deriv_of_hasSumLocallyUniformlyOn {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) : HasSum (fun i => deriv (F i) z) (deriv g z) := by
  have h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U := h
  have hd := h'.deriv
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU
  have hD : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, deriv (F i) x) (deriv g)
      Filter.atTop U := by
    refine hd.congr fun s x hx => ?_
    have he : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
      funext y
      simp [Finset.sum_apply]
    simp only [Function.comp_apply]
    rw [he, deriv_sum fun i _ => (hF i).differentiableAt (hU.mem_nhds hx)]
  exact HasSumLocallyUniformlyOn.hasSum hD hz
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
theorem _root_.solution (L : PeriodPair) :
    Set.EqOn (deriv (wZeta L)) (fun z ↦ -(L.weierstrassP z)) (L.lattice : Set ℂ)ᶜ := by
  intro z hz
  have hU : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hF : ∀ l : L.lattice, DifferentiableOn ℂ
      (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) (L.lattice : Set ℂ)ᶜ := by
    intro l w hw
    have hwl : w - l ≠ 0 := by
      intro e
      apply hw
      rw [sub_eq_zero.mp e]
      exact l.2
    exact (hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt
  have hs := hasSum_deriv_of_hasSumLocallyUniformlyOn (hasSumLU_wZeta L).hasSumLocallyUniformlyOn hF hU hz
  have hder : (fun l : L.lattice =>
      deriv (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) z) =
      fun l : L.lattice => -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
    funext l
    have hzl : z - l ≠ 0 := by
      intro e
      apply hz
      rw [sub_eq_zero.mp e]
      exact l.2
    exact (hasDerivAt_term l z hzl).deriv
  rw [hder] at hs
  exact hs.unique (L.hasSum_weierstrassP z).neg
end Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
