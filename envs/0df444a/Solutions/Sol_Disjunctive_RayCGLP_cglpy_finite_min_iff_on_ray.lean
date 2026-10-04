-- Prove2me | solution 1 for Disjunctive.RayCGLP.cglpy_finite_min_iff_on_ray
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:01:37.938988+00:00
-- url     : https://prove2.me/submissions/393c6cfc-cb26-4427-bbfb-dccbb4692fda

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

open Filter Topology Disjunctive.RayCGLP

lemma clm_eq_dot_core {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∃ a : Fin n → ℝ, ∀ x, f x = dotProduct a x := by
  classical
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun x => ?_⟩
  conv_lhs => rw [pi_eq_sum_univ x]
  simp [map_sum, map_smul, dotProduct, mul_comm]

lemma cone_closed_core {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDclosed : IsClosed PD)
    (y α0 : Fin n → ℝ) (β0 : ℝ) (hα0 : ∀ x ∈ PD, β0 ≤ dotProduct α0 x)
    (hy : dotProduct α0 y = 1) :
    IsClosed {x : Fin n → ℝ | ∃ s : ℝ, 0 ≤ s ∧ x - s • y ∈ PD} := by
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_seq_limit] at hx
  obtain ⟨xs, hxs, hlim⟩ := hx
  choose s hs0 hsP using hxs
  have hcont : Continuous fun z : Fin n → ℝ => dotProduct α0 z := by fun_prop
  have hlim2 : Tendsto (fun k => dotProduct α0 (xs k)) atTop (𝓝 (dotProduct α0 x)) :=
    (hcont.tendsto x).comp hlim
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hlim2).bddAbove
  have hsB : ∀ k, s k ∈ Set.Icc 0 (B - β0) := by
    intro k
    refine ⟨hs0 k, ?_⟩
    have h1 := hα0 _ (hsP k)
    have h2 : dotProduct α0 (xs k) ≤ B := hB ⟨k, rfl⟩
    rw [dotProduct_sub, dotProduct_smul, hy, smul_eq_mul] at h1
    linarith
  obtain ⟨s0, hs0mem, φ, hφ, hφlim⟩ := (isCompact_Icc).tendsto_subseq hsB
  refine ⟨s0, hs0mem.1, ?_⟩
  exact hPDclosed.mem_of_tendsto ((hlim.comp hφ.tendsto_atTop).sub (hφlim.smul_const y))
    (Eventually.of_forall fun k => hsP (φ k))

theorem solution {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (y xbar : Fin n → ℝ)
    (hfeas : ∃ α β, IsCGLPYFeasible PD y α β) :
    CGLPYHasFiniteMin PD y xbar ↔ ∃ lam : ℝ, xbar + lam • y ∈ PD := by
  constructor
  · rintro ⟨m, hm⟩
    by_contra hno
    push Not at hno
    obtain ⟨α0, β0, hα0, hy⟩ := hfeas
    have hm' : ∀ α β, IsCGLPYFeasible PD y α β → m ≤ dotProduct α xbar - β := by
      intro α β h
      exact hm ⟨(α, β), h, rfl⟩
    set C : Set (Fin n → ℝ) := {x | ∃ s : ℝ, 0 ≤ s ∧ x - s • y ∈ PD} with hC
    have hCconv : Convex ℝ C := by
      intro a ha b hb t1 t2 ht1 ht2 ht
      obtain ⟨sa, hsa, ha'⟩ := ha
      obtain ⟨sb, hsb, hb'⟩ := hb
      refine ⟨t1 * sa + t2 * sb, by positivity, ?_⟩
      have := hPDconv ha' hb' ht1 ht2 ht
      convert this using 1
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hCclosed : IsClosed C := cone_closed_core PD hPDclosed y α0 β0 hα0 hy
    set p : Fin n → ℝ := xbar + (1 - m) • y with hp
    have hpC : p ∉ C := by
      rintro ⟨s, _, hs⟩
      apply hno (1 - m - s)
      convert hs using 1
      rw [hp, sub_smul, sub_smul]
      abel
    obtain ⟨f, u, hfu, hfC⟩ := geometric_hahn_banach_point_closed hCconv hCclosed hpC
    obtain ⟨a, ha⟩ := clm_eq_dot_core f
    have hPDC : ∀ x ∈ PD, x ∈ C := fun x hx => ⟨0, le_rfl, by simpa using hx⟩
    have hfp : f p = f xbar + (1 - m) * f y := by
      rw [hp, map_add, map_smul, smul_eq_mul]
    by_cases hPDne : PD.Nonempty
    · obtain ⟨z, hz⟩ := hPDne
      have hfy : 0 ≤ f y := by
        by_contra hneg
        push Not at hneg
        set s : ℝ := (f z - u) / (-f y) + 1 with hs
        have hspos : 0 ≤ s := by
          have : 0 < f z - u := by linarith [hfC z (hPDC z hz)]
          have : 0 ≤ (f z - u) / (-f y) := div_nonneg this.le (by linarith)
          linarith
        have hmem : z + s • y ∈ C := ⟨s, hspos, by simpa using hz⟩
        have h1 := hfC _ hmem
        rw [map_add, map_smul, smul_eq_mul] at h1
        have h2 : s * f y = -(f z - u) + f y := by
          have e1 := div_mul_cancel₀ (f z - u) (ne_of_gt (neg_pos.mpr hneg))
          have e2 : (f z - u) / -f y * f y = -((f z - u) / -f y * -f y) := by ring
          rw [hs, add_mul, one_mul, e2, e1]
        linarith
      rcases hfy.lt_or_eq with hpos | hzero
      · -- normalize `f`
        have hfeas' : IsCGLPYFeasible PD y ((1 / f y) • a) (u / f y) := by
          refine ⟨fun x hx => ?_, ?_⟩
          · rw [smul_dotProduct, smul_eq_mul, ← ha]
            have := hfC x (hPDC x hx)
            rw [div_le_iff₀ hpos]
            field_simp
            linarith
          · rw [smul_dotProduct, smul_eq_mul, ← ha]
            field_simp
        have h1 := hm' _ _ hfeas'
        rw [smul_dotProduct, smul_eq_mul, ← ha] at h1
        have h2 : 1 / f y * f xbar - u / f y = (f xbar - u) / f y := by ring
        rw [h2, le_div_iff₀ hpos] at h1
        nlinarith
      · have hfx : f xbar < u := by rw [← hzero] at hfp; linarith
        set s : ℝ := max 0 ((dotProduct α0 xbar - β0 - m + 1) / (u - f xbar)) with hs
        have hs0 : 0 ≤ s := le_max_left _ _
        have hfeas' : IsCGLPYFeasible PD y (α0 + s • a) (β0 + s * u) := by
          refine ⟨fun x hx => ?_, ?_⟩
          · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, ← ha]
            have := hfC x (hPDC x hx)
            have := hα0 x hx
            nlinarith
          · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, ← ha, hy, ← hzero]
            ring
        have h1 := hm' _ _ hfeas'
        rw [add_dotProduct, smul_dotProduct, smul_eq_mul, ← ha] at h1
        have hgap : 0 < u - f xbar := by linarith
        have h3 : (dotProduct α0 xbar - β0 - m + 1) / (u - f xbar) ≤ s := le_max_right _ _
        rw [div_le_iff₀ hgap] at h3
        nlinarith
    · rw [Set.not_nonempty_iff_eq_empty] at hPDne
      have hfeas' : IsCGLPYFeasible PD y α0 (dotProduct α0 xbar - m + 1) :=
        ⟨by simp [hPDne], hy⟩
      have := hm' _ _ hfeas'
      linarith
  · rintro ⟨lam, hlam⟩
    refine ⟨-lam, ?_⟩
    rintro _ ⟨⟨α, β⟩, ⟨hval, hy⟩, rfl⟩
    have := hval _ hlam
    rw [dotProduct_add, dotProduct_smul, hy, smul_eq_mul] at this
    simp only
    linarith

#print axioms solution
