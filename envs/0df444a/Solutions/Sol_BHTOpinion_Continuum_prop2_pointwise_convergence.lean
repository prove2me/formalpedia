-- Prove2me | solution 1 for BHTOpinion.Continuum.prop2_pointwise_convergence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:49:18.393598+00:00
-- url     : https://prove2.me/submissions/083c0b32-82ce-48ef-aa72-d68c9be0a161

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model
import Theorems.Thm_BHTOpinion_Continuum_lemma3_partial_integral_converges

open MeasureTheory Filter Topology

namespace BHT6P2

open BHTOpinion.Continuum

/-- For a nondecreasing solution, opinions stay in `[x0 0, x0 1]`. -/
lemma bounds (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, x0 0 ≤ x t α ∧ x t α ≤ x0 1 := by
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩
  intro t ht α hα
  have hlow : x0 0 ≤ x t 0 := by
    rw [hx.eq t ht 0 h0I]
    have : 0 ≤ ∫ τ in (0 : ℝ)..t, opL (x τ) 0 := by
      refine intervalIntegral.integral_nonneg ht (fun τ hτ => ?_)
      unfold opL
      refine setIntegral_nonneg measurableSet_Icc (fun γ hγ => ?_)
      have := (hmono τ hτ.1).1 h0I hγ hγ.1
      split_ifs <;> linarith
    linarith
  have hup : x t 1 ≤ x0 1 := by
    rw [hx.eq t ht 1 h1I]
    have : 0 ≤ ∫ τ in (0 : ℝ)..t, -opL (x τ) 1 := by
      refine intervalIntegral.integral_nonneg ht (fun τ hτ => ?_)
      rw [neg_nonneg]
      unfold opL
      refine setIntegral_nonpos measurableSet_Icc (fun γ hγ => ?_)
      have := (hmono τ hτ.1).1 hγ h1I hγ.2
      split_ifs <;> linarith
    rw [intervalIntegral.integral_neg] at this
    linarith
  exact ⟨hlow.trans ((hmono t ht).1 h0I hα hα.1), ((hmono t ht).1 hα h1I hα.2).trans hup⟩

end BHT6P2

open BHTOpinion.Continuum in
theorem solution (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ α ∈ I, α ∉ S → ∃ l : ℝ, Tendsto (fun t => x t α) atTop (𝓝 l) := by
  have hb := BHT6P2.bounds x0 x hx hmono
  have havg := (lemma3_partial_integral_converges x0 x hx hmono).2
  -- clamp to I
  let cl : ℝ → ℝ := fun α => max 0 (min 1 α)
  have hclI : ∀ α, cl α ∈ I := fun α =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hclmono : Monotone cl := fun a b hab => max_le_max le_rfl (min_le_min le_rfl hab)
  have hclid : ∀ α ∈ I, cl α = α := fun α hα => by
    simp only [cl]; rw [min_eq_right hα.2, max_eq_right hα.1]
  have hbdd : ∀ α, IsBoundedUnder (· ≤ ·) atTop (fun t => x t (cl α)) := fun α =>
    ⟨x0 1, eventually_map.2 ((eventually_ge_atTop 0).mono fun t ht => (hb t ht _ (hclI α)).2)⟩
  have hcobdd : ∀ α, IsCoboundedUnder (· ≤ ·) atTop (fun t => x t (cl α)) := fun α =>
    isCoboundedUnder_le_of_eventually_le atTop
      ((eventually_ge_atTop 0).mono fun t ht => (hb t ht _ (hclI α)).1)
  let Y : ℝ → ℝ := fun α => limsup (fun t => x t (cl α)) atTop
  have hYmono : Monotone Y := by
    intro a b hab
    refine limsup_le_limsup ?_ (hcobdd a) (hbdd b)
    exact (eventually_ge_atTop 0).mono fun t ht =>
      (hmono t ht).1 (hclI a) (hclI b) (hclmono hab)
  refine ⟨{0} ∪ {α | ¬ContinuousAt Y α}, (Set.countable_singleton 0).union
    hYmono.countable_not_continuousAt, fun α hα hαS => ⟨Y α, ?_⟩⟩
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, not_or, not_not] at hαS
  obtain ⟨hα0, hcont⟩ := hαS
  have hαpos : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
  have hYα : Y α = limsup (fun t => x t α) atTop := by simp only [Y, hclid α hα]
  rw [tendsto_order]
  constructor
  · -- lower bound: the averaging argument of the paper
    intro a ha
    by_contra hcon
    rw [not_eventually] at hcon
    set ε := Y α - a with hε
    have hεpos : 0 < ε := by linarith
    -- continuity of Y at α: choose δ
    obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.continuousAt_iff.mp hcont (ε / 3) (by linarith)
    set δ := min (δ0 / 2) α with hδ
    have hδpos : 0 < δ := lt_min (by linarith) hαpos
    have hδle : δ ≤ α := min_le_right _ _
    have hYδ : Y α - ε / 3 < Y (α - δ) := by
      have hd : dist (α - δ) α < δ0 := by
        rw [Real.dist_eq, show α - δ - α = -δ by ring, abs_neg, abs_of_pos hδpos]
        have := min_le_left (δ0 / 2) α; linarith
      have := hδ0' hd
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hbI : α - δ ∈ I := ⟨by linarith, by linarith [hα.2]⟩
    obtain ⟨l, hl⟩ := havg (α - δ) hbI α hα (by linarith)
    have hlen : α - (α - δ) = δ := by ring
    have hint : ∀ t : ℝ, 0 ≤ t → x t (α - δ) ≤ (∫ β in (α - δ)..α, x t β) / (α - (α - δ)) ∧
        (∫ β in (α - δ)..α, x t β) / (α - (α - δ)) ≤ x t α := by
      intro t ht
      have hsub : Set.Icc (α - δ) α ⊆ I := fun β hβ => ⟨by linarith [hβ.1], by linarith [hβ.2, hα.2]⟩
      have hmon' : MonotoneOn (x t) (Set.uIcc (α - δ) α) := by
        rw [Set.uIcc_of_le (by linarith)]; exact (hmono t ht).1.mono hsub
      have hii := hmon'.intervalIntegrable (μ := volume)
      rw [hlen]
      constructor
      · rw [le_div_iff₀ hδpos]
        have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hii
          (fun β hβ => (hmono t ht).1 hbI (hsub hβ) hβ.1)
        simp only [intervalIntegral.integral_const, smul_eq_mul, hlen] at this
        linarith
      · rw [div_le_iff₀ hδpos]
        have := intervalIntegral.integral_mono_on (by linarith) hii intervalIntegrable_const
          (fun β hβ => (hmono t ht).1 (hsub hβ) hα hβ.2)
        simp only [intervalIntegral.integral_const, smul_eq_mul, hlen] at this
        linarith
    -- frequently x t α ≤ a, so frequently average ≤ a
    have hlim1 : l ≤ a := by
      by_contra h1
      push Not at h1
      have hev := (tendsto_order.1 hl).1 a h1
      obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((hcon.and_eventually (eventually_ge_atTop 0)).and_eventually
        hev).exists
      have := (hint t ht2).2
      linarith
    -- frequently x t (α - δ) > Y(α - δ) - ε/3
    have hfr : ∃ᶠ t in atTop, Y (α - δ) - ε / 3 < x t (α - δ) := by
      have h := frequently_lt_of_lt_limsup (hcobdd (α - δ))
        (show Y (α - δ) - ε / 3 < Y (α - δ) by linarith)
      simpa only [hclid _ hbI] using h
    have hlim2 : Y α - 2 * ε / 3 ≤ l := by
      by_contra h2
      push Not at h2
      have hev := (tendsto_order.1 hl).2 (Y α - 2 * ε / 3) h2
      obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((hfr.and_eventually (eventually_ge_atTop 0)).and_eventually
        hev).exists
      have := (hint t ht2).1
      linarith
    linarith
  · intro b hb'
    rw [hYα] at hb'
    have hbd : IsBoundedUnder (· ≤ ·) atTop (fun t => x t α) := by
      simpa only [hclid α hα] using hbdd α
    exact eventually_lt_of_limsup_lt hb' hbd
