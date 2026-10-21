-- Prove2me | solution 1 for DynOpaque.TwoPeriod.lemma_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T02:19:47.164624+00:00
-- url     : https://prove2.me/submissions/f200cc2a-e51e-4b12-81b3-cd9f5e2f4ff0

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaqueLemma2Aux
open DynOpaque.TwoPeriod

/-- Objective (3) normalized by `c = cH - cL`, with `x = (vHL - cL)/(cH - cL)`. -/
noncomputable def F (α x u v : ℝ) : ℝ := u * (x - u) + (α * u + (1 - α) * v) * (x - v)

theorem obj3_F (vH vL cH cL α u v : ℝ) (hc : cH - cL ≠ 0) :
    obj3 vH vL cH cL α u v = (cH - cL) * F α ((vHL vH vL - cL) / (cH - cL)) u v := by
  unfold obj3 F; field_simp; ring

theorem opt_of_F (vH vL cH cL α u0 v0 : ℝ) (hc : 0 < cH - cL)
    (hb : (u0, v0) ∈ box)
    (h : ∀ u v : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
      F α ((vHL vH vL - cL) / (cH - cL)) u v ≤ F α ((vHL vH vL - cL) / (cH - cL)) u0 v0) :
    IsOptimalOffering (obj3 vH vL cH cL α) u0 v0 := by
  refine ⟨hb, ?_⟩
  rintro ⟨u, v⟩ ⟨⟨hu0, hu1⟩, ⟨hv0, hv1⟩⟩
  simp only
  rw [obj3_F _ _ _ _ _ _ _ hc.ne', obj3_F _ _ _ _ _ _ _ hc.ne']
  exact mul_le_mul_of_nonneg_left (h u v hu0 hu1 hv0 hv1) hc.le

/-- Exact second-order expansion of the quadratic `F` around `(u0, v0)`. -/
theorem taylor (α x u v u0 v0 : ℝ) :
    F α x u0 v0 - F α x u v =
      ((1 + α) * x - α * v0 - 2 * u0) * (u0 - u) +
        ((1 - α) * x - α * u0 - 2 * (1 - α) * v0) * (v0 - v) +
        ((u - u0) ^ 2 + α * (u - u0) * (v - v0) + (1 - α) * (v - v0) ^ 2) := by
  unfold F; ring

theorem conc_opt (α x u v u0 v0 : ℝ) (hD : 0 ≤ 4 - 4 * α - α ^ 2)
    (hg : 0 ≤ ((1 + α) * x - α * v0 - 2 * u0) * (u0 - u) +
        ((1 - α) * x - α * u0 - 2 * (1 - α) * v0) * (v0 - v)) :
    F α x u v ≤ F α x u0 v0 := by
  have ht := taylor α x u v u0 v0
  have hQ : 0 ≤ (u - u0) ^ 2 + α * (u - u0) * (v - v0) + (1 - α) * (v - v0) ^ 2 := by
    nlinarith [sq_nonneg (u - u0 + α * (v - v0) / 2), mul_nonneg hD (sq_nonneg (v - v0))]
  linarith

theorem corner11 (α x u v : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (hx : 2 - α ≤ (1 - α) * x)
    (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hu0 : 0 ≤ u) :
    F α x u v ≤ F α x 1 1 := by
  have e : F α x 1 1 - F α x u v =
      (1 - v) * ((1 - α) * (x - v) - 1) + (1 - u) * ((1 + α) * x - α * v - u - 1) := by
    unfold F; ring
  have hx1 : 1 ≤ x := by nlinarith
  have a1 : 0 ≤ (1 - α) * (x - v) - 1 := by nlinarith
  have a2 : 0 ≤ (1 + α) * x - α * v - u - 1 := by
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hv1), mul_nonneg h0 (sub_nonneg.2 hx1)]
  have := mul_nonneg (sub_nonneg.2 hv1) a1
  have := mul_nonneg (sub_nonneg.2 hu1) a2
  linarith

theorem edge_vertex (α x v : ℝ) (h1 : α < 1) :
    F α x 1 (((1 - α) * x - α) / (2 * (1 - α))) - F α x 1 v =
      (1 - α) * (v - ((1 - α) * x - α) / (2 * (1 - α))) ^ 2 := by
  have : (1 - α) ≠ 0 := by linarith
  unfold F; field_simp; ring

theorem edge_direct (α x u v : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (hx : 2 + α ≤ (1 + α) * x)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    F α x u v ≤ F α x 1 (((1 - α) * x - α) / (2 * (1 - α))) := by
  have e1 := edge_vertex α x v h1
  have e2 : F α x 1 v - F α x u v = (1 - u) * ((1 + α) * x - α * v - u - 1) := by
    unfold F; ring
  have a2 : 0 ≤ (1 + α) * x - α * v - u - 1 := by
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hv1)]
  have := mul_nonneg (sub_nonneg.2 hu1) a2
  have : 0 ≤ (1 - α) * (v - ((1 - α) * x - α) / (2 * (1 - α))) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

theorem edge_conc (α x u v : ℝ) (h1 : α < 1) (hD : 0 ≤ 4 - 4 * α - α ^ 2)
    (hx : 4 - 4 * α - α ^ 2 ≤ (2 - α - α ^ 2) * x) (hu1 : u ≤ 1) :
    F α x u v ≤ F α x 1 (((1 - α) * x - α) / (2 * (1 - α))) := by
  apply conc_opt α x u v _ _ hD
  have h1a : 0 < 1 - α := by linarith
  have hgv : (1 - α) * x - α * 1 - 2 * (1 - α) * (((1 - α) * x - α) / (2 * (1 - α))) = 0 := by
    field_simp; ring
  have hgu : 0 ≤ (1 + α) * x - α * (((1 - α) * x - α) / (2 * (1 - α))) - 2 * 1 := by
    have e : (1 + α) * x - α * (((1 - α) * x - α) / (2 * (1 - α))) - 2 * 1 =
        ((2 - α - α ^ 2) * x - (4 - 4 * α - α ^ 2)) / (2 * (1 - α)) := by
      field_simp; ring
    rw [e]; apply div_nonneg (by linarith) (by linarith)
  rw [hgv]
  have := mul_nonneg hgu (sub_nonneg.2 hu1)
  linarith

/-- Regime `(1, 0)` of Lemma 2 (ii). -/
theorem corner10 (α x u v : ℝ) (h0 : 0 ≤ α) (h1 : α < 1)
    (hx1 : 2 ≤ (1 + α) * x) (hx2 : (1 - α) * x ≤ α)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    F α x u v ≤ F α x 1 0 := by
  set s := 1 - u with hs
  set A := (1 + α) * x - 2 with hA
  set B := α - (1 - α) * x with hB
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have e : F α x 1 0 - F α x u v = s * A + s ^ 2 + v * B - α * s * v + (1 - α) * v ^ 2 := by
    rw [hs, hA, hB]; unfold F; ring
  by_cases hBs : α * s ≤ B
  · have : 0 ≤ v * (B - α * s) := mul_nonneg hv0 (by linarith)
    have : 0 ≤ s * A := mul_nonneg hs0 hA0
    nlinarith [sq_nonneg s, sq_nonneg v]
  · push Not at hBs
    by_cases hD : 0 ≤ 4 - 4 * α - α ^ 2
    · -- concave case: expand around (1, 0)
      have : 0 ≤ s * A := mul_nonneg hs0 hA0
      have : 0 ≤ v * B := mul_nonneg hv0 hB0
      nlinarith [sq_nonneg (s - α * v / 2), mul_nonneg hD (sq_nonneg v)]
    · push Not at hD
      have h1a : 0 < 1 - α := by linarith
      have key : 4 * (1 - α) * (s * A + s ^ 2 + v * B - α * s * v + (1 - α) * v ^ 2) =
          (2 * (1 - α) * v + B - α * s) ^ 2 +
            ((4 - 4 * α - α ^ 2) * s ^ 2 + 4 * (1 - α) * A * s + 2 * α * s * B - B ^ 2) := by
        ring
      have t1 : 0 ≤ B * (α * s - B) := mul_nonneg hB0 (by linarith)
      have t2 : 0 ≤ (4 - 4 * α - α ^ 2) * (s - 1) * s := by
        have : 0 ≤ (-(4 - 4 * α - α ^ 2)) * (1 - s) * s :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) hs0
        nlinarith
      have t3 : 0 ≤ (4 - 4 * α - α ^ 2) + 4 * (1 - α) * A + α * B := by
        have e3 : (4 - 4 * α - α ^ 2) + 4 * (1 - α) * A + α * B = (1 - α) * ((4 + 3 * α) * x - 4) := by
          rw [hA, hB]; ring
        rw [e3]
        apply mul_nonneg h1a.le
        nlinarith
      have t4 : 0 ≤ s * ((4 - 4 * α - α ^ 2) + 4 * (1 - α) * A + α * B) := mul_nonneg hs0 t3
      have : 0 ≤ 4 * (1 - α) * (s * A + s ^ 2 + v * B - α * s * v + (1 - α) * v ^ 2) := by
        rw [key]; nlinarith [sq_nonneg (2 * (1 - α) * v + B - α * s)]
      have := (mul_nonneg_iff_of_pos_left (show (0:ℝ) < 4 * (1 - α) by linarith)).1 this
      linarith

theorem boundI1 (α x u v : ℝ) (hD : 0 < 4 - 4 * α - α ^ 2) :
    (4 - 4 * α - α ^ 2) * F α x u v ≤ 2 * (1 - α) * x ^ 2 := by
  have key : (4 - 4 * α - α ^ 2) * (2 * (1 - α) * x ^ 2 - (4 - 4 * α - α ^ 2) * F α x u v) =
      ((4 - 4 * α - α ^ 2) * u - (2 - α - α ^ 2) * x +
          α * ((4 - 4 * α - α ^ 2) * v - (2 - 3 * α - α ^ 2) * x) / 2) ^ 2 +
        (4 - 4 * α - α ^ 2) * ((4 - 4 * α - α ^ 2) * v - (2 - 3 * α - α ^ 2) * x) ^ 2 / 4 := by
    unfold F; ring
  have hr : 0 ≤ (4 - 4 * α - α ^ 2) * (2 * (1 - α) * x ^ 2 - (4 - 4 * α - α ^ 2) * F α x u v) := by
    rw [key]; positivity
  have := (mul_nonneg_iff_of_pos_left hD).1 hr
  linarith

theorem valI1 (α x : ℝ) (hD : 4 - 4 * α - α ^ 2 ≠ 0) :
    F α x ((2 - α - α ^ 2) * x / (4 - 4 * α - α ^ 2)) ((2 - 3 * α - α ^ 2) * x / (4 - 4 * α - α ^ 2)) =
      2 * (1 - α) * x ^ 2 / (4 - 4 * α - α ^ 2) := by
  unfold F
  generalize hDD : 4 - 4 * α - α ^ 2 = D at *
  field_simp
  linear_combination (-2 * x ^ 2 * (1 - α)) * hDD

theorem boundII1 (α x u v : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (hk : 0 ≤ α ^ 2 + 3 * α - 2)
    (hx : 0 ≤ u) (hy : 0 ≤ v) :
    4 * F α x u v ≤ (1 + α) ^ 2 * x ^ 2 := by
  have key : (1 + α) ^ 2 * ((1 + α) ^ 2 * x ^ 2 - 4 * F α x u v) =
      ((1 + α) * ((1 + α) * x - 2 * u) - 2 * (1 - α) * v) ^ 2 +
        4 * (1 - α) * (α ^ 2 + 3 * α) * v ^ 2 +
        4 * (1 + α) * (α ^ 2 + 3 * α - 2) * u * v := by
    unfold F; ring
  have h1a : 0 ≤ 1 - α := by linarith
  have hr : 0 ≤ (1 + α) ^ 2 * ((1 + α) ^ 2 * x ^ 2 - 4 * F α x u v) := by
    rw [key]
    have : 0 ≤ 4 * (1 - α) * (α ^ 2 + 3 * α) * v ^ 2 := by positivity
    have : 0 ≤ 4 * (1 + α) * (α ^ 2 + 3 * α - 2) * u * v := by positivity
    positivity
  have hp : 0 < (1 + α) ^ 2 := by positivity
  have := (mul_nonneg_iff_of_pos_left hp).1 hr
  linarith

theorem sqrt17_lt (α : ℝ) (h0 : 0 ≤ α) (h : α < alphaBar) : α ^ 2 + 3 * α < 2 := by
  unfold alphaBar at h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  nlinarith

theorem sqrt17_ge (α : ℝ) (h0 : 0 ≤ α) (h : alphaBar ≤ α) : 0 ≤ α ^ 2 + 3 * α - 2 := by
  unfold alphaBar at h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  nlinarith

end DynOpaqueLemma2Aux

open DynOpaque.TwoPeriod DynOpaqueLemma2Aux in
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) (hα : alphaBar ≤ α)
    (hα1 : α < 1) :
    ((vHL vH vL - cL) / (cH - cL) < 2 / (1 + α) →
      IsOptimalOffering (obj3 vH vL cH cL α)
        ((1 + α) * (vHL vH vL - cL) / (2 * (cH - cL))) 0) ∧
    (2 / (1 + α) ≤ (vHL vH vL - cL) / (cH - cL) →
      (vHL vH vL - cL) / (cH - cL) ≤ α / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1 0) ∧
    (α / (1 - α) < (vHL vH vL - cL) / (cH - cL) →
      (vHL vH vL - cL) / (cH - cL) < (2 - α) / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1
        (((1 - α) * (vHL vH vL - cL) - α * (cH - cL)) / (2 * (1 - α) * (cH - cL)))) ∧
    ((vHL vH vL - cL) / (cH - cL) ≥ (2 - α) / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1 1) := by
  obtain ⟨hv, hc, h0, h1, hl⟩ := hS
  have hc0 : 0 < cH - cL := by linarith
  have hd0 : 0 < vHL vH vL - cL := by unfold vHL; linarith
  have hk := sqrt17_ge α h0 hα
  have h1a : 0 < 1 - α := by linarith
  have hp : 0 < 1 + α := by linarith
  have hx0 : 0 < (vHL vH vL - cL) / (cH - cL) := div_pos hd0 hc0
  set x := (vHL vH vL - cL) / (cH - cL) with hxdef
  have hdx : vHL vH vL - cL = x * (cH - cL) := by rw [hxdef]; field_simp
  refine ⟨fun hx => ?_, fun hx1 hx2 => ?_, fun hx1 hx2 => ?_, fun hx => ?_⟩
  · rw [lt_div_iff₀ hp] at hx
    have e1 : (1 + α) * (vHL vH vL - cL) / (2 * (cH - cL)) = (1 + α) * x / 2 := by
      rw [hdx]; field_simp
    rw [e1]
    apply opt_of_F _ _ _ _ _ _ _ hc0
    · refine ⟨⟨by positivity, by linarith⟩, ⟨le_rfl, zero_le_one⟩⟩
    · intro u v hu0 _ hv0 _
      have hval : F α x ((1 + α) * x / 2) 0 = (1 + α) ^ 2 * x ^ 2 / 4 := by unfold F; ring
      rw [hval]
      have := boundII1 α x u v h0 h1 hk hu0 hv0
      linarith
  · rw [div_le_iff₀ hp] at hx1
    rw [le_div_iff₀ h1a] at hx2
    apply opt_of_F _ _ _ _ _ _ _ hc0
    · exact ⟨⟨by norm_num, le_rfl⟩, ⟨le_rfl, zero_le_one⟩⟩
    · intro u v hu0 hu1 hv0 hv1
      exact corner10 α x u v h0 hα1 (by linarith) (by linarith) hu0 hu1 hv0 hv1
  · rw [div_lt_iff₀ h1a] at hx1
    rw [lt_div_iff₀ h1a] at hx2
    have e : ((1 - α) * (vHL vH vL - cL) - α * (cH - cL)) / (2 * (1 - α) * (cH - cL)) =
        ((1 - α) * x - α) / (2 * (1 - α)) := by
      rw [hdx]; field_simp
    rw [e]
    apply opt_of_F _ _ _ _ _ _ _ hc0
    · refine ⟨⟨by norm_num, le_rfl⟩, ⟨?_, ?_⟩⟩
      · apply div_nonneg _ (by linarith)
        nlinarith
      · rw [div_le_one (by linarith)]; linarith
    · intro u v hu0 hu1 hv0 hv1
      by_cases hd : 2 + α ≤ (1 + α) * x
      · exact edge_direct α x u v h0 hα1 hd hu0 hu1 hv0 hv1
      · push Not at hd
        have hsm : α ^ 2 + α < 1 := by nlinarith
        have hD : 0 ≤ 4 - 4 * α - α ^ 2 := by nlinarith
        apply edge_conc α x u v hα1 hD _ hu1
        nlinarith
  · rw [ge_iff_le, div_le_iff₀ h1a] at hx
    apply opt_of_F _ _ _ _ _ _ _ hc0
    · exact ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩⟩
    · intro u v hu0 hu1 hv0 hv1
      exact corner11 α x u v h0 hα1 (by linarith) hu1 hv0 hv1 hu0
