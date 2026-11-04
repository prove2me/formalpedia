-- Prove2me | solution 1 for ChanceStateCtrl.PDE.clarke_singleton_strict
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:41:17.948696+00:00
-- url     : https://prove2.me/submissions/29a7bf40-bb15-44e7-81db-56acef09d7e4

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise
open ChanceStateCtrl.PDE

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (u y : H) (hf : LocLipschitzAt f u)
    (hy : clarkeSubdiffL2 f u = {y}) (h : H) :
    Tendsto (fun q : H × ℝ => (f (q.1 + q.2 • h) - f q.1) / q.2) (𝓝 u ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ y h)) := by
  classical
  set L : Filter (H × ℝ) := 𝓝 u ×ˢ 𝓝[>] (0 : ℝ) with hL
  set Q : H → H × ℝ → ℝ := fun k q => (f (q.1 + q.2 • k) - f q.1) / q.2 with hQ
  set p : H → ℝ := fun k => limsup (Q k) L with hp
  have hpdef : ∀ k, clarkeDir f u k = p k := fun k => rfl
  obtain ⟨K, t, ht, hK⟩ := hf
  -- moving the base point along `k` and rescaling time keep us in `L`
  have hpos : ∀ᶠ q in L, 0 < q.2 :=
    (tendsto_snd (f := 𝓝 u) (g := 𝓝[>] (0 : ℝ))).eventually self_mem_nhdsWithin
  have hshift : ∀ k : H, Tendsto (fun q : H × ℝ => q.1 + q.2 • k) L (𝓝 u) := by
    intro k
    have := (tendsto_fst (f := 𝓝 u) (g := 𝓝[>] (0 : ℝ))).add
      (((tendsto_snd (f := 𝓝 u) (g := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).smul_const k)
    simpa using this
  have hψ : ∀ k : H, Tendsto (fun q : H × ℝ => (q.1 + q.2 • k, q.2)) L L :=
    fun k => (hshift k).prodMk tendsto_snd
  have hφ : ∀ c : ℝ, 0 < c → Tendsto (fun q : H × ℝ => (q.1, c * q.2)) L L := by
    intro c hc
    refine tendsto_fst.prodMk ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (((tendsto_snd (f := 𝓝 u) (g := 𝓝[>] (0 : ℝ))).mono_right
        nhdsWithin_le_nhds).const_mul c)
      simpa using this
    · filter_upwards [hpos] with q hq
      exact mul_pos hc hq
  -- Lipschitz bound on difference quotients
  have hbound : ∀ k : H, ∀ᶠ q in L, |Q k q| ≤ K * ‖k‖ := by
    intro k
    have h1 : ∀ᶠ q in L, q.1 ∈ t := tendsto_fst.eventually ht
    have h2 : ∀ᶠ q in L, q.1 + q.2 • k ∈ t := (hshift k).eventually ht
    filter_upwards [h1, h2, hpos] with q hq1 hq2 hq3
    have := hK.dist_le_mul _ hq2 _ hq1
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hq3.le]
      at this
    simp only [hQ]
    rw [abs_div, abs_of_pos hq3, div_le_iff₀ hq3]
    linarith
  have hBdd : ∀ k : H, IsBoundedUnder (· ≤ ·) L (Q k) := fun k =>
    isBoundedUnder_of_eventually_le (a := (K : ℝ) * ‖k‖)
      (by filter_upwards [hbound k] with q hq; exact (abs_le.1 hq).2)
  have hCobdd : ∀ k : H, IsCoboundedUnder (· ≤ ·) L (Q k) := fun k =>
    isCoboundedUnder_le_of_eventually_le L
      (x := -(K * ‖k‖)) (by filter_upwards [hbound k] with q hq; exact (abs_le.1 hq).1)
  -- limsup characterisation
  have hlt : ∀ k : H, ∀ ε > 0, ∀ᶠ q in L, Q k q < p k + ε := fun k ε hε =>
    eventually_lt_of_limsup_lt (by linarith) (hBdd k)
  have hle : ∀ k : H, ∀ a : ℝ, (∀ ε > 0, ∀ᶠ q in L, Q k q ≤ a + ε) → p k ≤ a := by
    intro k a ha
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have := limsup_le_of_le (hCobdd k) (ha (ε / 2) (by positivity))
    linarith
  -- sublinearity of `p`
  have hadd : ∀ k₁ k₂ : H, p (k₁ + k₂) ≤ p k₁ + p k₂ := by
    intro k₁ k₂
    refine hle _ _ fun ε hε => ?_
    have e1 := hlt k₁ (ε / 2) (by positivity)
    have e2 := (hψ k₁).eventually (hlt k₂ (ε / 2) (by positivity))
    filter_upwards [e1, e2, hpos] with q hq1 hq2 hq3
    have hid : Q (k₁ + k₂) q = Q k₂ (q.1 + q.2 • k₁, q.2) + Q k₁ q := by
      simp only [hQ, smul_add, add_assoc]
      field_simp
      ring
    rw [hid]
    linarith
  have hhom_le : ∀ c : ℝ, 0 < c → ∀ k : H, p (c • k) ≤ c * p k := by
    intro c hc k
    refine hle _ _ fun ε hε => ?_
    have e := (hφ c hc).eventually (hlt k (ε / c) (by positivity))
    filter_upwards [e, hpos] with q hq hq3
    have hid : Q (c • k) q = c * Q k (q.1, c * q.2) := by
      simp only [hQ, smul_smul]
      rw [mul_comm q.2 c]
      field_simp
    rw [hid]
    have := mul_lt_mul_of_pos_left hq hc
    rw [mul_add, mul_div_cancel₀ _ hc.ne'] at this
    linarith
  have hhom : ∀ c : ℝ, 0 < c → ∀ k : H, p (c • k) = c * p k := by
    intro c hc k
    refine le_antisymm (hhom_le c hc k) ?_
    have := hhom_le c⁻¹ (inv_pos.2 hc) (c • k)
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
    have h2 := mul_le_mul_of_nonneg_left this hc.le
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h2
    exact h2
  have hp0 : p 0 = 0 := by
    have := hhom 2 (by norm_num) 0
    rw [smul_zero] at this
    linarith
  have hpK : ∀ k : H, p k ≤ K * ‖k‖ :=
    fun k => hle _ _ fun ε hε => by
      filter_upwards [hbound k] with q hq
      linarith [(abs_le.1 hq).2]
  -- every value of `p` is attained by an element of `∂^C f(u)` (Hahn–Banach)
  have hval : ∀ k : H, p k = inner ℝ y k := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [hp0]
    obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear
      (LinearPMap.mkSpanSingleton (σ := RingHom.id ℝ) k (p k) hk) p hhom hadd (by
        rintro ⟨x, hx⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
        rw [LinearPMap.mkSpanSingleton'_apply]
        simp only [RingHom.id_apply, smul_eq_mul]
        rcases lt_trichotomy c 0 with hc | hc | hc
        · have hneg : c • k = (-c) • (-k) := by rw [smul_neg, neg_smul, neg_neg]
          rw [hneg, hhom (-c) (by linarith) (-k)]
          have := hadd k (-k)
          rw [add_neg_cancel, hp0] at this
          nlinarith
        · subst hc; simp [hp0]
        · rw [hhom c hc k])
    have hgK : ∀ x, |g x| ≤ K * ‖x‖ := by
      intro x
      rw [abs_le]
      constructor
      · have := (hg2 (-x)).trans (hpK (-x))
        rw [map_neg, norm_neg] at this
        linarith
      · exact (hg2 x).trans (hpK x)
    let gc : StrongDual ℝ H := g.mkContinuous K (fun x => by
      rw [Real.norm_eq_abs]; exact hgK x)
    set z := (InnerProductSpace.toDual ℝ H).symm gc with hz
    have hzg : ∀ x, inner ℝ z x = g x := by
      intro x
      rw [hz, InnerProductSpace.toDual_symm_apply]
      rfl
    have hzmem : z ∈ clarkeSubdiffL2 f u := by
      intro x
      rw [hzg, hpdef]
      exact hg2 x
    rw [hy, Set.mem_singleton_iff] at hzmem
    rw [← hzmem, hzg]
    have := hg1 ⟨k, Submodule.mem_span_singleton_self k⟩
    rw [LinearPMap.mkSpanSingleton_apply ℝ ℝ hk] at this
    exact this.symm
  -- conclude: limsup and liminf both equal `(y, h)`
  rw [tendsto_order]
  constructor
  · intro a ha
    have e := (hψ h).eventually (hlt (-h) (inner ℝ y h - a) (by linarith))
    filter_upwards [e, hpos] with q hq hq3
    have hid : Q (-h) (q.1 + q.2 • h, q.2) = -Q h q := by
      simp only [hQ, smul_neg, add_neg_cancel_right]
      field_simp
      ring
    rw [hid, hval (-h), inner_neg_right] at hq
    show a < Q h q
    linarith
  · intro a ha
    have e := hlt h (a - inner ℝ y h) (by linarith)
    filter_upwards [e] with q hq
    rw [hval h] at hq
    show Q h q < a
    linarith
