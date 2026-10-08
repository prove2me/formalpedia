-- Prove2me | solution 1 for CachonPushPull.Coordination.chain_newsvendor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:06:32.41699+00:00
-- url     : https://prove2.me/submissions/377632db-0c7e-4532-b3b4-29b49df0eb21

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPullBfff

open MeasureTheory ProbabilityTheory CachonPushPull.Coordination Filter Topology Set

lemma cdf_eq_zero_of_nonpos (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f)
    {x : ℝ} (hx : x ≤ 0) : cdf μ x = 0 :=
  le_antisymm (hD.cdf_zero ▸ monotone_cdf μ hx) (cdf_nonneg μ x)

lemma cdf_continuous (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) :
    Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝 x] cdf μ := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact (cdf_eq_zero_of_nonpos μ f hD (le_of_lt hy)).symm
    exact (continuousAt_const).congr this
  · subst hx
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, (cdf μ).right_continuous 0⟩
    have : ContinuousWithinAt (fun _ : ℝ => (0:ℝ)) (Iic 0) 0 := continuousWithinAt_const
    refine this.congr (fun y hy => cdf_eq_zero_of_nonpos μ f hD hy) ?_
    exact cdf_eq_zero_of_nonpos μ f hD le_rfl
  · exact (hD.hasDerivAt x hx).continuousAt

lemma chainProfit_hasDerivAt (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f)
    (p c v x : ℝ) :
    HasDerivAt (chainProfit μ p c v) ((p - c) - (p - v) * cdf μ x) x := by
  have h1 : HasDerivAt (fun u => ∫ t in (0:ℝ)..u, cdf μ t) (cdf μ x) x :=
    ((cdf_continuous μ f hD).integral_hasStrictDerivAt 0 x).hasDerivAt
  have h2 : HasDerivAt (fun q => (p - v) * (q - ∫ t in (0:ℝ)..q, cdf μ t) - (c - v) * q)
      ((p - v) * (1 - cdf μ x) - (c - v) * 1) x :=
    (((hasDerivAt_id x).sub h1).const_mul (p - v)).sub ((hasDerivAt_id x).const_mul (c - v))
  have : (p - v) * (1 - cdf μ x) - (c - v) * 1 = (p - c) - (p - v) * cdf μ x := by ring
  rw [this] at h2
  exact h2

lemma chainProfit_deriv (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f)
    (p c v x : ℝ) : deriv (chainProfit μ p c v) x = (p - c) - (p - v) * cdf μ x :=
  (chainProfit_hasDerivAt μ f hD p c v x).deriv

lemma chainProfit_continuous (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f)
    (p c v : ℝ) : Continuous (chainProfit μ p c v) :=
  continuous_iff_continuousAt.2 fun x => (chainProfit_hasDerivAt μ f hD p c v x).continuousAt

lemma pos_of_cdf_eq (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) (p c v : ℝ)
    (hvc : v < c) (hcp : c < p) (qo : ℝ) (h : cdf μ qo = (p - c) / (p - v)) : 0 < qo := by
  by_contra hq
  rw [not_lt] at hq
  rw [cdf_eq_zero_of_nonpos μ f hD hq] at h
  have : 0 < (p - c) / (p - v) := div_pos (by linarith) (by linarith)
  linarith

lemma strictMono_part (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) (p c v : ℝ)
    (hvc : v < c) (hcp : c < p) (qo : ℝ) (h : cdf μ qo = (p - c) / (p - v)) (hqo : 0 < qo) :
    StrictMonoOn (chainProfit μ p c v) (Icc 0 qo) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 qo)
    (chainProfit_continuous μ f hD p c v).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [chainProfit_deriv μ f hD]
  have hlt : cdf μ x < cdf μ qo :=
    hD.strictMonoOn (le_of_lt hx.1) (le_of_lt hqo) hx.2
  rw [h] at hlt
  have hpv : 0 < p - v := by linarith
  have : (p - v) * cdf μ x < (p - v) * ((p - c) / (p - v)) := mul_lt_mul_of_pos_left hlt hpv
  rw [mul_div_cancel₀ _ hpv.ne'] at this
  linarith

lemma strictAnti_part (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) (p c v : ℝ)
    (hvc : v < c) (hcp : c < p) (qo : ℝ) (h : cdf μ qo = (p - c) / (p - v)) (hqo : 0 < qo) :
    StrictAntiOn (chainProfit μ p c v) (Ici qo) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici qo)
    (chainProfit_continuous μ f hD p c v).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [chainProfit_deriv μ f hD]
  have hlt : cdf μ qo < cdf μ x :=
    hD.strictMonoOn (le_of_lt hqo) (le_of_lt (hqo.trans hx)) hx
  rw [h] at hlt
  have hpv : 0 < p - v := by linarith
  have : (p - v) * ((p - c) / (p - v)) < (p - v) * cdf μ x := mul_lt_mul_of_pos_left hlt hpv
  rw [mul_div_cancel₀ _ hpv.ne'] at this
  linarith

lemma isMax_part (μ : Measure ℝ) (f : ℝ → ℝ) (hD : DemandModel μ f) (p c v : ℝ)
    (hvc : v < c) (hcp : c < p) (qo : ℝ) (h : cdf μ qo = (p - c) / (p - v)) (hqo : 0 < qo) :
    IsMaxOn (chainProfit μ p c v) (Ici 0) qo := by
  intro q hq
  show chainProfit μ p c v q ≤ chainProfit μ p c v qo
  rcases le_total q qo with hle | hle
  · exact (strictMono_part μ f hD p c v hvc hcp qo h hqo).monotoneOn
      ⟨hq, hle⟩ ⟨le_of_lt hqo, le_rfl⟩ hle
  · exact (strictAnti_part μ f hD p c v hvc hcp qo h hqo).antitoneOn
      ((Set.mem_Ici.2 (le_refl qo))) hle hle

end CachonPushPullBfff

open MeasureTheory ProbabilityTheory CachonPushPull.Coordination Filter Topology Set in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∃ qo : ℝ, 0 < qo ∧ cdf μ qo = (p - c) / (p - v)) ∧
    ConcaveOn ℝ (Set.Ici 0) (chainProfit μ p c v) ∧
    (∀ qo : ℝ, cdf μ qo = (p - c) / (p - v) →
      0 < qo ∧ IsMaxOn (chainProfit μ p c v) (Set.Ici 0) qo ∧
        StrictMonoOn (chainProfit μ p c v) (Set.Icc 0 qo)) ∧
    ∀ q : ℝ, 0 ≤ q → IsMaxOn (chainProfit μ p c v) (Set.Ici 0) q →
      cdf μ q = (p - c) / (p - v) := by
  have hpv : 0 < p - v := by linarith
  have ht0 : 0 < (p - c) / (p - v) := div_pos (by linarith) hpv
  have ht1 : (p - c) / (p - v) < 1 := (div_lt_one hpv).2 (by linarith)
  have hex : ∃ qo : ℝ, 0 < qo ∧ cdf μ qo = (p - c) / (p - v) := by
    obtain ⟨N, hN⟩ := ((tendsto_cdf_atTop (μ := μ)).eventually (lt_mem_nhds ht1)).and
      (eventually_ge_atTop 0) |>.exists
    have hsub := intermediate_value_Icc hN.2 (CachonPushPullBfff.cdf_continuous μ f hD).continuousOn
    obtain ⟨q, hq, hq'⟩ := hsub ⟨by rw [hD.cdf_zero]; exact ht0.le, hN.1.le⟩
    exact ⟨q, CachonPushPullBfff.pos_of_cdf_eq μ f hD p c v hvc hcp q hq', hq'⟩
  refine ⟨hex, ?_, ?_, ?_⟩
  · apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
      (CachonPushPullBfff.chainProfit_continuous μ f hD p c v).continuousOn
    · intro x _
      exact (CachonPushPullBfff.chainProfit_hasDerivAt μ f hD p c v x).differentiableAt.differentiableWithinAt
    · intro x _ y _ hxy
      simp only [CachonPushPullBfff.chainProfit_deriv μ f hD]
      have := monotone_cdf μ hxy
      nlinarith
  · intro qo h
    have hqo := CachonPushPullBfff.pos_of_cdf_eq μ f hD p c v hvc hcp qo h
    exact ⟨hqo, CachonPushPullBfff.isMax_part μ f hD p c v hvc hcp qo h hqo,
      CachonPushPullBfff.strictMono_part μ f hD p c v hvc hcp qo h hqo⟩
  · intro q hq hmax
    obtain ⟨qo, hqo, h⟩ := hex
    rcases lt_trichotomy q qo with hlt | heq | hgt
    · exfalso
      have h1 := CachonPushPullBfff.strictMono_part μ f hD p c v hvc hcp qo h hqo ⟨hq, hlt.le⟩
        ⟨hqo.le, le_rfl⟩ hlt
      have h2 : chainProfit μ p c v qo ≤ chainProfit μ p c v q :=
        hmax (show qo ∈ Ici (0:ℝ) from hqo.le)
      linarith
    · rw [heq]; exact h
    · exfalso
      have h1 := CachonPushPullBfff.strictAnti_part μ f hD p c v hvc hcp qo h hqo (Set.mem_Ici.2 (le_refl qo))
        (show q ∈ Ici qo from hgt.le) hgt
      have h2 : chainProfit μ p c v qo ≤ chainProfit μ p c v q :=
        hmax (show qo ∈ Ici (0:ℝ) from hqo.le)
      linarith
