-- Prove2me | solution 1 for EnsembleSpaceDraft.internal_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:37:18.493991+00:00
-- url     : https://prove2.me/submissions/60265294-c719-44d7-b3cf-bbb17a267f95

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

namespace ENSL

variable {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)

lemma mix_zero (a b : E) : X.mix 0 a b = b := by
  rw [X.mix_comm, unitInterval.symm_zero, X.mix_one]

lemma mix_of_eq_one {p : unitInterval} (hp : (p : ℝ) = 1) (a b : E) : X.mix p a b = a := by
  have : p = 1 := Subtype.ext hp
  subst this; exact X.mix_one a b

lemma mix_of_eq_zero {p : unitInterval} (hp : (p : ℝ) = 0) (a b : E) : X.mix p a b = b := by
  have : p = 0 := Subtype.ext hp
  subst this; exact mix_zero X a b

lemma mix_congr {p q : unitInterval} (h : (p : ℝ) = q) (a b : E) : X.mix p a b = X.mix q a b := by
  rw [Subtype.ext h]

/-- Re-association: `u (v x + (1-v) y) + (1-u) z = (u v) x + (1 - u v) (w y + (1-w) z)`. -/
lemma assoc_right (u v : unitInterval) (x y z : E) :
    ∃ w : unitInterval, X.mix u (X.mix v x y) z =
      X.mix ⟨(u : ℝ) * v, unitInterval.mul_mem u.2 v.2⟩ x (X.mix w y z) := by
  have hu0 := u.2.1; have hu1 := u.2.2; have hv0 := v.2.1; have hv1 := v.2.2
  rcases eq_or_lt_of_le hu0 with hu | hu
  · refine ⟨0, ?_⟩
    rw [mix_of_eq_zero X hu.symm, mix_of_eq_zero X (by simp [← hu]), mix_zero]
  by_cases huv : (u : ℝ) * v = 1
  · have hu1' : (u : ℝ) = 1 := by nlinarith
    have hv1' : (v : ℝ) = 1 := by nlinarith
    refine ⟨0, ?_⟩
    rw [mix_of_eq_one X hu1', mix_of_eq_one X hv1', mix_of_eq_one X huv]
  have huv1 : (u : ℝ) * v < 1 := lt_of_le_of_ne (unitInterval.mul_mem u.2 v.2).2 huv
  have h := X.mix_assoc ((u : ℝ) * v) (1 - u) x y z (mul_nonneg hu0 hv0) huv1
    (by linarith) (by linarith) (by nlinarith)
  refine ⟨⟨(1 - (u : ℝ) * v - (1 - u)) / (1 - u * v), assoc_left_coeff_mem (mul_nonneg hu0 hv0)
    huv1 (by linarith) (by linarith) (by nlinarith)⟩, ?_⟩
  rw [h]
  have hu' : (1 : ℝ) - (1 - u) ≠ 0 := by linarith
  congr 1
  · apply Subtype.ext; simp
  · congr 1; apply Subtype.ext; simp only; field_simp; ring

/-- `s e + (1-s) (t e + (1-t) a) = (s + (1-s) t) e + ... a`. -/
lemma mix_mix_same (s t : unitInterval) (e a : E) :
    X.mix s e (X.mix t e a) =
      X.mix ⟨(s : ℝ) + (1 - s) * t, by
        constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩ e a := by
  have hs0 := s.2.1; have hs1 := s.2.2; have ht0 := t.2.1; have ht1 := t.2.2
  rcases eq_or_lt_of_le hs1 with hs | hs
  · rw [mix_of_eq_one X hs, mix_of_eq_one X (by simp [hs])]
  by_cases h00 : (s : ℝ) = 0 ∧ (t : ℝ) = 0
  · rw [mix_of_eq_zero X h00.1, mix_of_eq_zero X h00.2, mix_of_eq_zero X (by simp [h00.1, h00.2])]
  have hp3 : (1 - (s : ℝ)) * (1 - t) < 1 := by
    by_contra hc
    push Not at hc
    have : (1 - (s : ℝ)) * (1 - t) ≤ 1 - s := by nlinarith
    have hs0' : (s : ℝ) = 0 := by linarith
    have : (t : ℝ) = 0 := by
      rw [hs0'] at hc; nlinarith
    exact h00 ⟨hs0', this⟩
  have h := X.mix_assoc (s : ℝ) ((1 - s) * (1 - t)) e e a hs0 hs
    (by nlinarith) hp3 (by nlinarith)
  rw [X.mix_self] at h
  convert h using 2
  · congr 1; apply Subtype.ext; simp; field_simp; ring
  · apply Subtype.ext; simp; ring

/-- Components compose. -/
lemma component_trans {c m n : E} (h1 : X.IsComponent c m) (h2 : X.IsComponent m n) :
    X.IsComponent c n := by
  obtain ⟨s, d1, hs, rfl⟩ := h1
  obtain ⟨r, d, hr, rfl⟩ := h2
  obtain ⟨w, hw⟩ := assoc_right X r s c d1 d
  exact ⟨_, _, by simp only; positivity, hw⟩

/-- For `0 < p ≤ q`, `p x + (1-p) y = (p/q) (q x + (1-q) y) + (1 - p/q) y`. -/
lemma mix_as_component (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : (p : ℝ) ≤ q) (x y : E) :
    X.IsComponent (X.mix q x y) (X.mix p x y) := by
  have hq : 0 < (q : ℝ) := lt_of_lt_of_le hp hpq
  have hr : (p : ℝ) / q ∈ unitInterval :=
    ⟨div_nonneg p.2.1 hq.le, (div_le_one hq).mpr hpq⟩
  obtain ⟨w, hw⟩ := assoc_right X ⟨_, hr⟩ q x y y
  refine ⟨⟨_, hr⟩, y, div_pos hp hq, ?_⟩
  rw [hw, X.mix_self]
  apply mix_congr; simp; field_simp

end ENSL

end EnsembleSpaceDraft

open EnsembleSpaceDraft
universe u
open scoped unitInterval

theorem solution {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)
    (e₁ e₂ : E) (p : unitInterval) (h₁ : X.IsInternal e₁) (h₂ : X.IsInternal e₂) :
    X.IsInternal (X.mix p e₁ e₂) := by
  intro a
  rcases eq_or_lt_of_le p.2.1 with hp | hp
  · rw [ENSL.mix_of_eq_zero X hp.symm]; exact h₂ a
  · obtain ⟨p1, b1, hp1, rfl⟩ := h₁ a
    obtain ⟨w, hw⟩ := ENSL.assoc_right X p p1 a b1 e₂
    exact ⟨_, _, show (0 : ℝ) < p * p1 from mul_pos hp hp1, hw⟩
