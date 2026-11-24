-- Prove2me | solution 1 for Formalism.L2.Th1.F.isogenyWeierstrassP_of_ellipticNoPole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:01.008214+00:00
-- url     : https://prove2.me/submissions/fe981ddf-9129-4f0e-9204-566c364c84c0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_analyticAt_P
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_ext_at
import Theorems.Thm_Formalism_L2_Th1_F_Elliptic_eq_of_eventuallyEq_nhdsNE


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
open IsogenyPAux
namespace Formalism.L2.Th1.F
theorem _root_.solution (hN : EllipticNoPole) : IsogenyP := by
  intro L α S hα hst hS z hz
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have h0S : (0 : ℂ) ∉ S := fun h => (hS1 0 h).2 L.lattice.zero_mem
  set T : Finset ℂ := insert 0 S with hT
  have h1 : ∀ P ∈ T, α * P ∈ L.lattice := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · simp
    · exact (hS1 P hP).1
  have h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_insert.1 hP with rfl | hP <;> rcases Finset.mem_insert.1 hQ with rfl | hQ
    · rfl
    · exact absurd (by simpa using hPQ) (hS1 Q hQ).2
    · exact absurd (by simpa using hPQ) (hS1 P hP).2
    · exact hS2 P hP Q hQ hPQ
  have h3 : ∀ z₀, α * z₀ ∈ L.lattice → ∃ P ∈ T, z₀ + P ∈ L.lattice := by
    intro z₀ hz₀
    by_cases hm : z₀ ∈ L.lattice
    · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
    · obtain ⟨P, hP, hPz⟩ := hS3 (-z₀) (by simpa using L.lattice.neg_mem hz₀)
        (fun h => hm (by simpa using L.lattice.neg_mem h))
      refine ⟨P, Finset.mem_insert_of_mem hP, ?_⟩
      have := L.lattice.neg_mem hPz
      have e : -(-z₀ - P) = z₀ + P := by ring
      rwa [e] at this
  set f : ℂ → ℂ := fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P) with hf

  have han : ∀ z₀, α * z₀ ∉ L.lattice → AnalyticAt ℂ f z₀ := by
    intro z₀ hz₀
    have a1 : AnalyticAt ℂ (fun w => L.weierstrassP (α * w)) z₀ := by
      simpa using analyticAt_P L α 0 z₀ (by simpa using hz₀)
    refine (analyticAt_const.mul a1).sub (Finset.analyticAt_fun_sum _ fun P hP => ?_)
    have := analyticAt_P L 1 P z₀ (by
      intro hmem
      rw [one_mul] at hmem
      apply hz₀
      have := L.lattice.sub_mem (hst _ hmem) (h1 P hP)
      have e : α * (z₀ + P) - α * P = α * z₀ := by ring
      rwa [e] at this)
    simpa using this
  have hext : ∀ z₀, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
    intro z₀
    by_cases hz₀ : α * z₀ ∈ L.lattice
    · obtain ⟨P', hP', hzP⟩ := h3 z₀ hz₀
      exact ⟨_, ext_at L α T hα hst h1 h2 z₀ P' hP' hzP⟩
    · exact ⟨f, han z₀ hz₀, EventuallyEq.rfl⟩
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    obtain ⟨g, hg, hfg⟩ := hext z
    exact hg.meromorphicAt.congr hfg.symm
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := fun z =>
    (hmer z).meromorphicOrderAt_nonneg_iff.2 (hext z)
  have hper : IsPeriodic L f := by
    intro ω hω w
    simp only [hf]
    have e1 : α * (w + ω) = α * w + α * ω := by ring
    rw [e1, L.weierstrassP_add_coe (α * w) ⟨α * ω, hst ω hω⟩]
    congr 1
    refine Finset.sum_congr rfl fun P _ => ?_
    have e2 : w + ω + P = w + P + ω := by ring
    rw [e2, L.weierstrassP_add_coe (w + P) ⟨ω, hω⟩]
  obtain ⟨c, hc⟩ := hN L f hmer hper hord

  have hc0 : c = -∑ P ∈ S, L.weierstrassP P := by
    obtain ⟨ha, he⟩ := ext_at L α T hα hst h1 h2 0 0 (Finset.mem_insert_self _ _) (by simp)
    have hev : (fun _ : ℂ => c) =ᶠ[𝓝[≠] 0] f := by
      filter_upwards [eventually_notMem L α 0 hα] with w hw
      exact (hc w (han w hw).continuousAt).symm
    have := Elliptic.eq_of_eventuallyEq_nhdsNE continuousAt_const ha.continuousAt (hev.trans he)
    rw [this, hT, Finset.erase_insert h0S]
    simp
  have hfz := hc z (han z hz).continuousAt
  rw [hc0] at hfz
  simp only [hf, hT, Finset.sum_insert h0S, add_zero] at hfz
  rw [Finset.sum_sub_distrib]
  linear_combination hfz
end Formalism.L2.Th1.F
