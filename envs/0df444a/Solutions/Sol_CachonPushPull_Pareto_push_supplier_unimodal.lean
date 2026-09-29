-- Prove2me | solution 1 for CachonPushPull.Pareto.push_supplier_unimodal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:36:52.780011+00:00
-- url     : https://prove2.me/submissions/41401826-e801-4f6f-8170-71dfc083508d

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory
open Filter Topology

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ∃ qh : ℝ, 0 < qh ∧
      StrictMonoOn (pushSupplierProfit μ p c v) (Set.Icc 0 qh) ∧
      StrictAntiOn (pushSupplierProfit μ p c v) (Set.Ici qh) := by
  classical
  have hpv : 0 < p - v := by linarith
  have hF0 : cdf μ 0 = 0 := hD.cdf_zero
  have hFnn : ∀ x, 0 ≤ cdf μ x := fun x => cdf_nonneg μ x
  have hFle : ∀ x, cdf μ x ≤ 1 := fun x => cdf_le_one μ x
  have hFmono : Monotone (cdf μ) := monotone_cdf μ
  have hFlt1 : ∀ x, cdf μ x < 1 := by
    intro x
    rcases le_or_gt 0 x with hx | hx
    · have := hD.strictMonoOn (Set.mem_Ici.2 hx)
        (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ x + 1)) (by linarith)
      exact lt_of_lt_of_le this (hFle _)
    · have := hFmono hx.le
      rw [hF0] at this
      linarith
  have hFderiv : ∀ x, 0 < x → HasDerivAt (cdf μ) (f x) x := hD.hasDerivAt
  have hfnn : ∀ x, 0 < x → 0 ≤ f x := by
    intro x hx
    rw [← (hFderiv x hx).deriv]
    exact hFmono.deriv_nonneg
  have hFcontAt : ∀ x, 0 < x → ContinuousAt (cdf μ) x := fun x hx =>
    (hFderiv x hx).continuousAt
  have hFcont0 : ContinuousWithinAt (cdf μ) (Set.Ici 0) 0 := (cdf μ).right_continuous 0
  have hFcontOn : ContinuousOn (cdf μ) (Set.Ici 0) := by
    intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.1 hx) with h | h
    · subst h; exact hFcont0
    · exact (hFcontAt x h).continuousWithinAt
  -- the generalized failure rate
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun y : ℝ => y * f y / (1 - cdf μ y) := ⟨_, rfl⟩
  have hgpos : ∀ x, 0 < x → 0 < deriv g x := by rw [hg]; exact hD.igfr
  have hgdiff : ∀ x, 0 < x → DifferentiableAt ℝ g x := fun x hx =>
    differentiableAt_of_deriv_ne_zero (hgpos x hx).ne'
  have hgmono : StrictMonoOn g (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · intro x hx; exact (hgdiff x hx).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ioi] at hx; exact hgpos x hx
  have hgnn : ∀ x, 0 < x → 0 ≤ g x := by
    intro x hx
    rw [hg]
    exact div_nonneg (mul_nonneg hx.le (hfnn x hx)) (by linarith [hFlt1 x])
  have hgeq : ∀ x, x * f x = g x * (1 - cdf μ x) := by
    intro x
    have : (1 - cdf μ x) ≠ 0 := by linarith [hFlt1 x]
    rw [hg]; field_simp
  -- the sign function of the derivative
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ,
      ψ = fun x => (p - v) * (1 - g x) - (c - v) / (1 - cdf μ x) := ⟨_, rfl⟩
  have hφ : pushSupplierProfit μ p c v = fun q => (p - (p - v) * cdf μ q - c) * q := by
    funext q; rfl
  have hφderiv : ∀ x, 0 < x → HasDerivAt (pushSupplierProfit μ p c v)
      ((1 - cdf μ x) * ψ x) x := by
    intro x hx
    rw [hφ]
    have h1 : HasDerivAt (fun q => (p - (p - v) * cdf μ q - c) * q)
        (-((p - v) * f x) * x + (p - (p - v) * cdf μ x - c) * 1) x :=
      ((((hFderiv x hx).const_mul (p - v)).const_sub p).sub_const c).mul (hasDerivAt_id' x)
    refine h1.congr_deriv ?_
    have : (1 - cdf μ x) ≠ 0 := by linarith [hFlt1 x]
    rw [hψ, hg]
    simp only
    field_simp
    ring
  have hψanti : StrictAntiOn ψ (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hgxy := hgmono hx hy hxy
    have hFxy : cdf μ x < cdf μ y :=
      hD.strictMonoOn (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2 (le_of_lt hy)) hxy
    have h1 : 0 < 1 - cdf μ y := by linarith [hFlt1 y]
    have h2 : 1 - cdf μ y < 1 - cdf μ x := by linarith
    have h3 : (c - v) / (1 - cdf μ x) < (c - v) / (1 - cdf μ y) :=
      div_lt_div_of_pos_left (by linarith) h1 h2
    have h4 := mul_lt_mul_of_pos_left hgxy hpv
    rw [hψ]
    simp only
    nlinarith
  have hψcont : ∀ x, 0 < x → ContinuousAt ψ x := by
    intro x hx
    have hne : (1 - cdf μ x) ≠ 0 := by linarith [hFlt1 x]
    rw [hψ]
    exact (continuousAt_const.mul (continuousAt_const.sub (hgdiff x hx).continuousAt)).sub
      (continuousAt_const.div (continuousAt_const.sub (hFcontAt x hx)) hne)
  -- a point where ψ is positive
  set η : ℝ := (p - c) / (2 * (p - v)) with hηdef
  have hη : 0 < η := div_pos (by linarith) (by linarith)
  have hη2 : (p - v) * (2 * η) = p - c := by
    rw [hηdef]; field_simp
  obtain ⟨q2, hq2pos, hq2F⟩ : ∃ q2 : ℝ, 0 < q2 ∧ cdf μ q2 < η := by
    have h1 : ∀ᶠ x in 𝓝[≥] (0:ℝ), cdf μ x < η :=
      hFcont0.eventually (eventually_lt_nhds (by rw [hF0]; exact hη))
    have h2 : ∀ᶠ x in 𝓝[>] (0:ℝ), cdf μ x < η := nhdsWithin_mono _ Set.Ioi_subset_Ici_self h1
    obtain ⟨x, hx1, hx2⟩ := (h2.and self_mem_nhdsWithin).exists
    exact ⟨x, hx2, hx1⟩
  obtain ⟨a, ha0, haq2, hga⟩ : ∃ a, 0 < a ∧ a ≤ q2 ∧ g a < η := by
    by_contra hcon
    push Not at hcon
    set K := η * (1 - cdf μ q2) with hK
    have hKpos : 0 < K := mul_pos hη (by linarith [hFlt1 q2])
    have hxf : ∀ x, 0 < x → x ≤ q2 → K ≤ x * f x := by
      intro x hx hxq
      rw [hgeq x]
      have := hcon x hx hxq
      have h1 : cdf μ x ≤ cdf μ q2 := hFmono hxq
      have h2 : 0 ≤ 1 - cdf μ q2 := by linarith [hFlt1 q2]
      calc K = η * (1 - cdf μ q2) := rfl
        _ ≤ g x * (1 - cdf μ q2) := mul_le_mul_of_nonneg_right this h2
        _ ≤ g x * (1 - cdf μ x) := mul_le_mul_of_nonneg_left (by linarith) (le_trans hη.le this)
    have h2K : 0 < 2 / K := div_pos two_pos hKpos
    set e := q2 * Real.exp (-(2 / K)) with he
    have he0 : 0 < e := mul_pos hq2pos (Real.exp_pos _)
    have heq2 : e ≤ q2 := by
      have : Real.exp (-(2 / K)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      rw [he]; nlinarith
    have hmono : MonotoneOn (fun x => cdf μ x - K * Real.log x) (Set.Icc e q2) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc e q2)
        (f' := fun x => f x - K * x⁻¹)
      · intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le he0 hx.1
        exact ((hFcontAt x hx0).sub
          (continuousAt_const.mul (Real.continuousAt_log hx0.ne'))).continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := lt_trans he0 hx.1
        exact ((hFderiv x hx0).sub ((Real.hasDerivAt_log hx0.ne').const_mul K)).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := lt_trans he0 hx.1
        have := hxf x hx0 hx.2.le
        show 0 ≤ f x - K * x⁻¹
        rw [sub_nonneg, ← div_eq_mul_inv, div_le_iff₀ hx0]
        linarith
    have hm := hmono ⟨le_refl e, heq2⟩ ⟨heq2, le_refl q2⟩ heq2
    simp only at hm
    have hloge : Real.log e = Real.log q2 - 2 / K := by
      rw [he, Real.log_mul hq2pos.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    rw [hloge] at hm
    have hK2 : K * (2 / K) = 2 := by field_simp
    nlinarith [hFnn e, hFle q2]
  have hFa : cdf μ a < η := lt_of_le_of_lt (hFmono haq2) hq2F
  have hψa : 0 < ψ a := by
    have h1 : 0 < 1 - cdf μ a := by linarith [hFlt1 a]
    have hgan := hgnn a ha0
    have hFan := hFnn a
    have key : c - v < (p - v) * (1 - g a) * (1 - cdf μ a) := by
      have : (p - v) * (1 - g a - cdf μ a) ≤ (p - v) * (1 - g a) * (1 - cdf μ a) := by
        have : 0 ≤ (p - v) * (g a * cdf μ a) := mul_nonneg hpv.le (mul_nonneg hgan hFan)
        nlinarith
      have : (p - v) * (2 * η) < (p - v) * (2 * η) + (p - v) * (2 * η - g a - cdf μ a) := by
        have : 0 < 2 * η - g a - cdf μ a := by linarith
        nlinarith
      nlinarith
    rw [hψ]
    simp only
    rw [sub_pos, div_lt_iff₀ h1]
    exact key
  -- a point where ψ is negative
  obtain ⟨b, hba, hbF⟩ : ∃ b, a + 1 ≤ b ∧ 1 - (c - v) / (p - v) < cdf μ b := by
    have h1 : 1 - (c - v) / (p - v) < 1 := by
      have : 0 < (c - v) / (p - v) := div_pos (by linarith) hpv
      linarith
    have h2 := (tendsto_cdf_atTop μ).eventually (lt_mem_nhds h1)
    obtain ⟨b, hb1, hb2⟩ := ((eventually_ge_atTop (a + 1)).and h2).exists
    exact ⟨b, hb1, hb2⟩
  have hb0 : 0 < b := by linarith
  have hψb : ψ b < 0 := by
    have h1 : 0 < 1 - cdf μ b := by linarith [hFlt1 b]
    have hgbn := hgnn b hb0
    have h3 : (p - v) * (1 - cdf μ b) < c - v := by
      have : 1 - cdf μ b < (c - v) / (p - v) := by linarith
      rw [lt_div_iff₀ hpv] at this
      linarith
    have h4 : p - v < (c - v) / (1 - cdf μ b) := by
      rw [lt_div_iff₀ h1]; linarith
    rw [hψ]
    simp only
    nlinarith
  -- the crossing point
  have hab : a ≤ b := by linarith
  have hψcontOn : ContinuousOn ψ (Set.Icc a b) := fun x hx =>
    (hψcont x (lt_of_lt_of_le ha0 hx.1)).continuousWithinAt
  obtain ⟨qh, hqh, hψqh⟩ := intermediate_value_Ioo' hab hψcontOn ⟨hψb, hψa⟩
  have hqhpos : 0 < qh := lt_trans ha0 hqh.1
  refine ⟨qh, hqhpos, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 qh)
    · rw [hφ]
      exact ((continuousOn_const.sub (continuousOn_const.mul
        (hFcontOn.mono Set.Icc_subset_Ici_self))).sub continuousOn_const).mul continuousOn_id
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hφderiv x hx.1).deriv]
      have : 0 < ψ x := by
        rw [← hψqh]
        exact hψanti hx.1 (Set.mem_Ioi.2 hqhpos) hx.2
      exact mul_pos (by linarith [hFlt1 x]) this
  · apply strictAntiOn_of_deriv_neg (convex_Ici qh)
    · rw [hφ]
      exact ((continuousOn_const.sub (continuousOn_const.mul
        (hFcontOn.mono (Set.Ici_subset_Ici.2 hqhpos.le)))).sub continuousOn_const).mul
          continuousOn_id
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hqhpos hx
      rw [(hφderiv x hx0).deriv]
      have : ψ x < 0 := by
        rw [← hψqh]
        exact hψanti (Set.mem_Ioi.2 hqhpos) (Set.mem_Ioi.2 hx0) hx
      exact mul_neg_of_pos_of_neg (by linarith [hFlt1 x]) this
