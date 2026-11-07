-- Prove2me | solution 1 for DuffieHedge.Optimal.ode_13_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:55:40.52012+00:00
-- url     : https://prove2.me/submissions/1e102797-7fcd-4035-9fe5-6dc08fbecaa7

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem solution (T : ℝ≥0) (m v : ℝ≥0 → ℝ) (hm : Measurable m) (hv : Measurable v)
    (hbd : ∃ K : ℝ, ∀ t ≤ T, |m t| ≤ K ∧ |v t| ≤ K)
    (hv0 : ∃ δ : ℝ, 0 < δ ∧ ∀ t ≤ T, δ ≤ |v t|)
    (H : ℝ≥0 → ℝ)
    (hint : IntegrableOn (fun s : ℝ => m s.toNNReal ^ 2 / v s.toNNReal ^ 2 * H s.toNNReal)
      (Set.Icc (0 : ℝ) T))
    (hode : ∀ t ≤ T, H t = H 0 - ∫ s in Set.Icc (0 : ℝ) t,
      m s.toNNReal ^ 2 / v s.toNNReal ^ 2 * H s.toNNReal) :
    ∀ t ≤ T, H t = H 0 * Real.exp (-∫ s in Set.Icc (0 : ℝ) t,
      m s.toNNReal ^ 2 / v s.toNNReal ^ 2) := by
  obtain ⟨K, hK⟩ := hbd
  obtain ⟨δ, hδ, hδv⟩ := hv0
  set c : ℝ → ℝ := fun s => m s.toNNReal ^ 2 / v s.toNNReal ^ 2 with hc_def
  set f : ℝ → ℝ := fun s => m s.toNNReal ^ 2 / v s.toNNReal ^ 2 * H s.toNNReal with hf_def
  have hT0 : (0 : ℝ) ≤ T := T.2
  have huIcc : uIcc (0 : ℝ) (T : ℝ) = Icc (0 : ℝ) (T : ℝ) := uIcc_of_le hT0
  -- bound on c
  set B : ℝ := K ^ 2 / δ ^ 2 with hB
  have hc_nonneg : ∀ s, 0 ≤ c s := fun s => by positivity
  have hc_bd : ∀ s ∈ Icc (0 : ℝ) T, c s ≤ B := by
    intro s hs
    have hsT : s.toNNReal ≤ T := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
    have h1 := (hK _ hsT).1
    have h2 := hδv _ hsT
    have hm2 : m s.toNNReal ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs (m _)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hv2 : δ ^ 2 ≤ v s.toNNReal ^ 2 := by
      rw [← sq_abs (v _)]; exact pow_le_pow_left₀ hδ.le h2 2
    simp only [hc_def, hB]
    exact div_le_div₀ (by positivity) hm2 (by positivity) hv2
  have hc_meas : Measurable c := by
    simp only [hc_def]
    exact ((hm.comp measurable_real_toNNReal).pow_const 2).div
      ((hv.comp measurable_real_toNNReal).pow_const 2)
  have hc_int : IntegrableOn c (Icc (0 : ℝ) T) := by
    refine IntegrableOn.of_bound measure_Icc_lt_top hc_meas.aestronglyMeasurable B ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hc_nonneg s)]
    exact hc_bd s hs
  have hc_ii : IntervalIntegrable c volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).2 hc_int
  have hf_ii : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).2 hint
  -- convert set integrals to interval integrals
  have hconv : ∀ (g : ℝ → ℝ) (x : ℝ), 0 ≤ x →
      ∫ s in Icc (0 : ℝ) x, g s = ∫ s in (0 : ℝ)..x, g s := by
    intro g x hx
    rw [intervalIntegral.integral_of_le hx, integral_Icc_eq_integral_Ioc]
  set C : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, c s with hC_def
  set h : ℝ → ℝ := fun x => H 0 - ∫ s in (0 : ℝ)..x, f s with hh_def
  set E : ℝ → ℝ := fun x => Real.exp (C x) with hE_def
  have hHh : ∀ x ∈ Icc (0 : ℝ) T, H x.toNNReal = h x := by
    intro x hx
    have hxT : x.toNNReal ≤ T := by rw [Real.toNNReal_le_iff_le_coe]; exact hx.2
    rw [hode _ hxT, Real.coe_toNNReal _ hx.1, hconv f x hx.1]
  -- absolute continuity
  have hh_ac : AbsolutelyContinuousOnInterval h 0 T := by
    have h1 : AbsolutelyContinuousOnInterval (fun x => ∫ s in (0 : ℝ)..x, f s) 0 T :=
      hf_ii.absolutelyContinuousOnInterval_intervalIntegral (by simp)
    have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => H 0) 0 T :=
      (LipschitzWith.const (α := ℝ) (H 0)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact h2.sub h1
  -- C is Lipschitz on [0, T]
  have hC_lip : LipschitzOnWith B.toNNReal C (uIcc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [huIcc] at hx hy
    rw [Real.dist_eq, Real.dist_eq]
    have : C x - C y = ∫ s in y..x, c s := by
      simp only [hC_def]
      rw [intervalIntegral.integral_interval_sub_left]
      · exact hc_ii.mono_set (by rw [huIcc]; exact uIcc_subset_Icc ⟨le_rfl, hT0⟩ hx)
      · exact hc_ii.mono_set (by rw [huIcc]; exact uIcc_subset_Icc ⟨le_rfl, hT0⟩ hy)
    rw [this, Real.coe_toNNReal _ (by positivity)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x) (C := B)
      (f := c) (fun s hs => by
        have hs' : s ∈ Icc (0 : ℝ) T := by
          have := uIoc_subset_uIcc hs
          exact uIcc_subset_Icc hy hx this
        rw [Real.norm_eq_abs, abs_of_nonneg (hc_nonneg s)]
        exact hc_bd s hs')
    rw [Real.norm_eq_abs] at this
    exact this
  have hC0 : C 0 = 0 := by simp [hC_def]
  set R : ℝ := B * T with hR
  have hC_maps : MapsTo C (uIcc 0 T) (Icc (-R) R) := by
    intro x hx
    have h1 := hC_lip.dist_le_mul x hx 0 (by rw [huIcc]; exact ⟨le_rfl, hT0⟩)
    rw [hC0, Real.dist_eq, sub_zero, Real.dist_eq, sub_zero,
      Real.coe_toNNReal _ (by positivity)] at h1
    rw [huIcc] at hx
    have h2 : B * |x| ≤ R := by
      rw [abs_of_nonneg hx.1]; exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
    exact abs_le.1 (h1.trans h2)
  have hexp_lip : LipschitzOnWith (Real.exp R).toNNReal Real.exp (Icc (-R) R) := by
    apply (convex_Icc (-R) R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := Real.exp)
    · intro x _; exact (Real.hasDerivAt_exp x).hasDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
        Real.coe_toNNReal _ (Real.exp_pos R).le]
      exact Real.exp_le_exp.2 hx.2
  have hE_ac : AbsolutelyContinuousOnInterval E 0 T :=
    (hexp_lip.comp hC_lip hC_maps).absolutelyContinuousOnInterval
  have hu_ac : AbsolutelyContinuousOnInterval (fun x => h x * E x) 0 T := hh_ac.fun_mul hE_ac
  have hderiv : ∀ᵐ x, x ∈ uIcc (0 : ℝ) T → HasDerivAt (fun x => h x * E x) 0 x := by
    filter_upwards [hf_ii.ae_hasDerivAt_integral, hc_ii.ae_hasDerivAt_integral] with x hx1 hx2 hx
    have d1 : HasDerivAt h (-f x) x := (hx1 hx 0 (by simp)).const_sub (H 0)
    have d2 : HasDerivAt C (c x) x := hx2 hx 0 (by simp)
    have d3 : HasDerivAt E (Real.exp (C x) * c x) x := d2.exp
    have := d1.mul d3
    refine this.congr_deriv ?_
    have hfx : f x = c x * h x := by
      simp only [hf_def, hc_def]
      rw [hHh x (by rw [← huIcc]; exact hx)]
    rw [hfx]
    simp only [hE_def]
    ring
  obtain ⟨K0, hK0⟩ := hu_ac.const_of_ae_hasDerivAt_zero hderiv
  have hu0 : h 0 * E 0 = H 0 := by simp [hh_def, hE_def, hC0]
  intro t ht
  have htT : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.2, by exact_mod_cast ht⟩
  have hut : h t * E t = H 0 := by
    rw [hK0 t (by rw [huIcc]; exact htT), ← hK0 0 (by rw [huIcc]; exact ⟨le_rfl, hT0⟩), hu0]
  have hHt : H t = h t := by
    have := hHh t htT
    rwa [Real.toNNReal_coe] at this
  rw [hHt, hconv c t t.2]
  have hEpos : 0 < E t := Real.exp_pos _
  have : h t = H 0 * (E t)⁻¹ := by
    field_simp
    exact hut
  rw [this]
  simp only [hE_def, hC_def, Real.exp_neg]
