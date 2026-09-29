-- Prove2me | solution 1 for Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/12146f62-b9bc-5f59-8ff7-248331a08922

import Mathlib
import Theorems.Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt

p2m_open "Filter Complex P2MW.S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt.Complex Metric"
open scoped Topology Real

noncomputable section

namespace Complex
p2m_export "Complex" "ext I circleIntegral_eq_sum_residue_of_simplePole"
namespace WeightedArgumentPrinciple
p2m_open "Complex"

variable {R G : ℂ → ℂ} {z₀ t : ℂ} {r : ℝ}

theorem analyticOrderAt_ne_top (hr : 0 < r)
    (hR : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ R z)
    (hne : ∀ z ∈ sphere z₀ r, R z ≠ t) {a : ℂ} (ha : a ∈ closedBall z₀ r) :
    analyticOrderAt (fun z => R z - t) a ≠ ⊤ := by

  set f : ℂ → ℂ := fun z => R z - t with hf
  have hfa : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ f z := fun z hz => (hR z hz).sub analyticAt_const
  obtain ⟨e, he, hsub⟩ := (isCompact_closedBall z₀ r).exists_thickening_subset_open
    (isOpen_analyticAt ℂ f) hfa
  rw [thickening_closedBall he hr.le] at hsub
  have hU : AnalyticOnNhd ℂ f (ball z₀ (e + r)) := fun z hz => hsub hz
  intro htop
  have hzero : ∀ᶠ z in 𝓝 a, f z = 0 := analyticOrderAt_eq_top.1 htop
  have ha' : a ∈ ball z₀ (e + r) :=
    closedBall_subset_ball (by linarith) ha
  have hEq := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball z₀ (e + r)).isPreconnected ha' hzero

  have hpt : z₀ + r ∈ sphere z₀ r := by
    simp [abs_of_pos hr]
  have hpt' : (z₀ : ℂ) + r ∈ ball z₀ (e + r) := sphere_subset_ball (by linarith) hpt
  exact hne _ hpt (sub_eq_zero.1 (hEq hpt'))

theorem finite_zeros (hr : 0 < r)
    (hR : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ R z)
    (hne : ∀ z ∈ sphere z₀ r, R z ≠ t) :
    {a | a ∈ ball z₀ r ∧ R a = t}.Finite := by
  set S : Set ℂ := {a | a ∈ closedBall z₀ r ∧ R a = t} with hS
  have hSsub : {a | a ∈ ball z₀ r ∧ R a = t} ⊆ S := fun a ha => ⟨ball_subset_closedBall ha.1, ha.2⟩
  refine Set.Finite.subset ?_ hSsub

  have hcont : ContinuousOn R (closedBall z₀ r) := fun z hz =>
    (hR z hz).continuousAt.continuousWithinAt
  have hSclosed : IsClosed S := by
    have : S = closedBall z₀ r ∩ R ⁻¹' {t} := by
      ext a; simp [hS]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hScpt : IsCompact S := (isCompact_closedBall z₀ r).of_isClosed_subset hSclosed
    (fun a ha => ha.1)

  refine hScpt.finite (isDiscrete_iff_nhdsNE.2 fun a ha => ?_)
  have hfa : AnalyticAt ℂ (fun z => R z - t) a := (hR a ha.1).sub analyticAt_const
  rcases hfa.eventually_eq_zero_or_eventually_ne_zero with h0 | hne0
  · exact absurd (analyticOrderAt_eq_top.2 h0) (analyticOrderAt_ne_top hr hR hne ha.1)
  · rw [Filter.inf_principal_eq_bot]
    filter_upwards [hne0] with z hz hzS
    exact hz (sub_eq_zero.2 hzS.2)

theorem local_form {a : ℂ} (hRa : AnalyticAt ℂ R a) (hGa : AnalyticAt ℂ G a)
    (htop : analyticOrderAt (fun z => R z - t) a ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, G z * deriv R z / (R z - t) =
        ((analyticOrderNatAt (fun z => R z - t) a : ℂ) * G a) / (z - a) + g z := by
  set f : ℂ → ℂ := fun z => R z - t with hf
  set n : ℕ := analyticOrderNatAt f a with hn
  have hfa : AnalyticAt ℂ f a := hRa.sub analyticAt_const
  have hcast : (n : ℕ∞) = analyticOrderAt f a := Nat.cast_analyticOrderNatAt htop
  obtain ⟨q, hqa, hq0, hfq⟩ := hfa.analyticOrderAt_eq_natCast.1 hcast.symm

  obtain ⟨p, hp⟩ := hGa
  have hds : AnalyticAt ℂ (dslope G a) a := ⟨_, hp.has_fpower_series_dslope_fslope⟩
  refine ⟨fun z => (n : ℂ) * dslope G a z + G z * (deriv q z / q z), ?_, ?_⟩
  · have hGa' : AnalyticAt ℂ G a := ⟨p, hp⟩
    exact (analyticAt_const.mul hds).add (hGa'.mul (hqa.deriv.div hqa hq0))
  ·
    have hq_ne : ∀ᶠ z in 𝓝 a, q z ≠ 0 := hqa.continuousAt.eventually_ne hq0
    have hqan : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ q z := hqa.eventually_analyticAt
    have hfq' : ∀ᶠ z in 𝓝 a, ∀ᶠ w in 𝓝 z, f w = (w - a) ^ n • q w :=
      hfq.eventually_nhds
    have hall : ∀ᶠ z in 𝓝[≠] a,
        q z ≠ 0 ∧ AnalyticAt ℂ q z ∧ (∀ᶠ w in 𝓝 z, f w = (w - a) ^ n • q w) ∧ z ≠ a := by
      refine (eventually_nhdsWithin_of_eventually_nhds (hq_ne.and (hqan.and hfq'))).mp ?_
      filter_upwards [self_mem_nhdsWithin] with z hz h
      exact ⟨h.1, h.2.1, h.2.2, hz⟩
    filter_upwards [hall] with z ⟨hqz, hqaz, hfz, hza⟩
    have hza' : z - a ≠ 0 := sub_ne_zero.2 hza

    have hfun : f =ᶠ[𝓝 z] fun w => (w - a) ^ n * q w := by
      filter_upwards [hfz] with w hw; rw [hw, smul_eq_mul]
    have hdR : deriv R z = deriv f z := by
      simp only [hf, deriv_sub_const]
    have hpow : HasDerivAt (fun w : ℂ => (w - a) ^ n) (n * (z - a) ^ (n - 1)) z := by
      have h__af := ((hasDerivAt_id z).sub_const a).pow n
      simp at h__af
      exact h__af
    have hprod : HasDerivAt (fun w => (w - a) ^ n * q w)
        (n * (z - a) ^ (n - 1) * q z + (z - a) ^ n * deriv q z) z :=
      hpow.mul hqaz.differentiableAt.hasDerivAt
    have hfz0 : f z = (z - a) ^ n * q z := by
      have := hfz.self_of_nhds; rwa [smul_eq_mul] at this
    have hRt : R z - t = (z - a) ^ n * q z := hfz0
    rw [hdR, hfun.deriv_eq, hprod.deriv, hRt, dslope_of_ne _ hza, slope_def_field]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0]
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, zero_add, zero_div]
      field_simp
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hnpos
      rw [hk, Nat.add_sub_cancel, pow_succ]
      field_simp
      push_cast
      ring

end Complex.WeightedArgumentPrinciple

open Complex.WeightedArgumentPrinciple in

theorem solution
    {R G : ℂ → ℂ} {z₀ t : ℂ} {r : ℝ} (hr : 0 < r)
    (hR : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ R z)
    (hG : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, R z ≠ t) :
    ∃ Z : Finset ℂ, (∀ a, a ∈ Z ↔ a ∈ Metric.ball z₀ r ∧ R a = t) ∧
      (∮ z in C(z₀, r), G z * deriv R z / (R z - t)) =
        2 * π * Complex.I *
          ∑ a ∈ Z, (analyticOrderNatAt (fun z => R z - t) a : ℂ) * G a := by
  classical
  set Z : Finset ℂ := (finite_zeros hr hR hne).toFinset with hZ
  have hmem : ∀ a, a ∈ Z ↔ a ∈ Metric.ball z₀ r ∧ R a = t := fun a => by
    simp [hZ, Set.Finite.mem_toFinset]
  refine ⟨Z, hmem, ?_⟩
  have hres := Complex.circleIntegral_eq_sum_residue_of_simplePole hr
    (fun z => G z * deriv R z / (R z - t))
    (fun a => (analyticOrderNatAt (fun z => R z - t) a : ℂ) * G a) Z
    (fun a ha => ((hmem a).1 ha).1)
    (fun z hz hzZ => by
      have hRt : R z - t ≠ 0 := by
        intro h0
        have hzt : R z = t := sub_eq_zero.1 h0
        rcases (Metric.mem_closedBall.1 hz).lt_or_eq with hlt | heq
        · exact hzZ ((hmem z).2 ⟨Metric.mem_ball.2 hlt, hzt⟩)
        · exact hne z (Metric.mem_sphere.2 heq) hzt
      exact ((hG z hz).mul (hR z hz).deriv).div ((hR z hz).sub analyticAt_const) hRt)
    (fun a ha => by
      have ha' : a ∈ Metric.closedBall z₀ r := Metric.ball_subset_closedBall ((hmem a).1 ha).1
      exact local_form (hR a ha') (hG a ha') (analyticOrderAt_ne_top hr hR hne ha'))
  rw [hres]

end

end S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
end P2MW
export P2MW.S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (solution)
