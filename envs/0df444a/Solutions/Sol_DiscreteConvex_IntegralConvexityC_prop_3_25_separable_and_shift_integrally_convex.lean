-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityC.prop_3_25_separable_and_shift_integrally_convex
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:46:59.576107+00:00
-- url     : https://prove2.me/submissions/9692375b-3f32-4c92-8f47-76a3372c7689

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_SeparableConvex

open DiscreteConvex.IntegralConvexityC

namespace GapSepCore

/-- A univariate function with domain `{0, 3}`: it satisfies the formal (C[Z→R]) inequality
`φ(t-1)+φ(t+1) ≥ 2φ(t)` (the gap `{1,2}` has length two), but is not convex-extensible. -/
noncomputable def phi : ℤ → WithTop ℝ := fun t => if t = 0 ∨ t = 3 then 0 else ⊤

lemma phi_univ : UnivDiscreteConvex phi := by
  refine ⟨⟨0, by simp [phi]⟩, fun t => ?_⟩
  by_cases h : t = 0 ∨ t = 3
  · have h1 : ¬ (t - 1 = 0 ∨ t - 1 = 3) := by omega
    simp only [phi, if_neg h1, top_add]
    exact le_top
  · have hl : phi t + phi t = ⊤ := by simp [phi, h]
    rw [hl]
    by_cases h1 : t - 1 = 0 ∨ t - 1 = 3
    · have h2 : ¬ (t + 1 = 0 ∨ t + 1 = 3) := by omega
      simp [phi, h2]
    · simp [phi, h1]

/-- `f(x) = φ(x₀)` on `ℤ¹`. -/
noncomputable def f : (Fin 1 → ℤ) → WithTop ℝ := fun x => phi (x 0)

lemma f_sep : SeparableConvex f :=
  ⟨fun _ => phi, fun _ => phi_univ, fun x => by simp [f]⟩

/-- The point `x = 3/2`. -/
noncomputable def xh : Fin 1 → ℝ := fun _ => 3 / 2

lemma local_top : LocalConvexExtension f xh = ⊤ := by
  unfold LocalConvexExtension
  refine sSup_eq_top.mpr (fun b hb => ?_)
  induction b using EReal.rec with
  | bot =>
    refine ⟨((0 + ∑ i, (0 : Fin 1 → ℝ) i * xh i : ℝ) : EReal), ⟨0, 0, ?_, rfl⟩,
      EReal.bot_lt_coe _⟩
    intro y hy
    have h1 : (1 : ℤ) ≤ y 0 := le_trans (Int.le_floor.mpr (by norm_num [xh])) (hy 0).1
    have h2 : y 0 ≤ 2 := le_trans (hy 0).2 (Int.ceil_le.mpr (by norm_num [xh]))
    have hne : ¬ (y 0 = 0 ∨ y 0 = 3) := by omega
    have : f y = ⊤ := by simp [f, phi, hne]
    rw [this]; exact le_top
  | top => exact absurd hb (lt_irrefl _)
  | coe M =>
    refine ⟨((|M| + 1 + ∑ i, (0 : Fin 1 → ℝ) i * xh i : ℝ) : EReal), ⟨0, |M| + 1, ?_, rfl⟩, ?_⟩
    · intro y hy
      have h1 : (1 : ℤ) ≤ y 0 := le_trans (Int.le_floor.mpr (by norm_num [xh])) (hy 0).1
      have h2 : y 0 ≤ 2 := le_trans (hy 0).2 (Int.ceil_le.mpr (by norm_num [xh]))
      have hne : ¬ (y 0 = 0 ∨ y 0 = 3) := by omega
      have : f y = ⊤ := by simp [f, phi, hne]
      rw [this]; exact le_top
    · rw [EReal.coe_lt_coe_iff]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      linarith [le_abs_self M]

lemma closure_le : ConvexClosure f xh ≤ 0 := by
  unfold ConvexClosure
  refine sSup_le (fun v hv => ?_)
  obtain ⟨p, a, hmin, rfl⟩ := hv
  have h0 := hmin (fun _ => 0)
  have h3 := hmin (fun _ => 3)
  have e0 : f (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) := by simp [f, phi]
  have e3 : f (fun _ => 3) = ((0 : ℝ) : WithTop ℝ) := by simp [f, phi]
  rw [e0] at h0; rw [e3] at h3
  have h0' := EReal.coe_le_coe_iff.mp h0
  have h3' := EReal.coe_le_coe_iff.mp h3
  simp only [Fin.sum_univ_one, Int.cast_zero, mul_zero, add_zero, Int.cast_ofNat] at h0' h3'
  have : a + ∑ i, p i * xh i ≤ 0 := by
    simp only [Fin.sum_univ_one, xh]; linarith
  exact_mod_cast this

lemma not_ic : ¬ IntegrallyConvex f := by
  intro h
  have := h xh
  rw [local_top] at this
  have h2 := closure_le
  rw [← this] at h2
  exact absurd h2 (by simp)

end GapSepCore

theorem solution : ¬ (∀ {n : ℕ},
    (∀ f : (Fin n → ℤ) → WithTop ℝ, SeparableConvex f → IntegrallyConvex f) ∧
      (∀ f : (Fin n → ℤ) → WithTop ℝ, IntegrallyConvex f → ∀ p : Fin n → ℝ,
        IntegrallyConvex (fun x => f x - ((∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ)))) := by
  intro h
  exact GapSepCore.not_ic ((@h 1).1 GapSepCore.f GapSepCore.f_sep)

#print axioms solution
