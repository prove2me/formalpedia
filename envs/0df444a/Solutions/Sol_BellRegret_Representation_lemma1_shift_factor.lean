-- Prove2me | solution 1 for BellRegret.Representation.lemma1_shift_factor
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:47:06.448876+00:00
-- url     : https://prove2.me/submissions/38332a43-1314-4d07-b8a3-d37c248a5302

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

set_option autoImplicit false

open BellRegret.Representation

namespace BRRsf

/-- antisymmetric part -/
def w (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := u x y - u y x

theorem pref_w (u : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ) (A B : Fin n → ℝ) :
    Prefers u p A B ↔ 0 < ∑ i, p i * w u (A i) (B i) := by
  unfold Prefers selectEU w
  simp only [mul_sub, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith


/-- Assumption 1 for `id` is invariant under shifts in both directions -/
theorem pref_iff (u : ℝ → ℝ → ℝ) (hA1 : Assumption1 u id) {n : ℕ} (p : Fin n → ℝ)
    (hp : IsProbVec p) (A B : Fin n → ℝ) (h : ℝ) :
    Prefers u p A B ↔ Prefers u p (fun i => A i + h) (fun i => B i + h) := by
  constructor
  · intro hP
    exact hA1 n p A B _ _ h hp (fun i => rfl) (fun i => rfl) hP
  · intro hP
    exact hA1 n p _ _ A B (-h) hp (fun i => by simp) (fun i => by simp) hP

theorem one_state (u : ℝ → ℝ → ℝ) (x y : ℝ) :
    Prefers u ![1] ![x] ![y] ↔ 0 < w u x y := by
  rw [pref_w]; simp

theorem isProb_one : IsProbVec (![1] : Fin 1 → ℝ) := by
  refine ⟨fun i => ?_, ?_⟩ <;> simp

theorem w_shift_pos (u : ℝ → ℝ → ℝ) (hA1 : Assumption1 u id) (x y h : ℝ) (hw : 0 < w u x y) :
    0 < w u (x + h) (y + h) := by
  have := (pref_iff u hA1 ![1] isProb_one ![x] ![y] h).1 ((one_state u x y).2 hw)
  have h2 := (pref_w u _ _ _).1 this
  simpa [w] using h2

theorem w_pos (u : ℝ → ℝ → ℝ) (hux : ∀ y, StrictMono (fun x => u x y))
    (huy : ∀ x, StrictAnti (fun y => u x y)) {x y : ℝ} (hxy : y < x) : 0 < w u x y := by
  have h1 : u y y < u x y := hux y hxy
  have h2 : u y x < u y y := huy y hxy
  unfold w; linarith

theorem w_anti (u : ℝ → ℝ → ℝ) (x y : ℝ) : w u x y = - w u y x := by
  unfold w; ring

theorem cross (u : ℝ → ℝ → ℝ) (hux : ∀ y, StrictMono (fun x => u x y))
    (huy : ∀ x, StrictAnti (fun y => u x y)) (hA1 : Assumption1 u id)
    {x1 y1 x2 y2 : ℝ} (h1 : y1 < x1) (h2 : y2 < x2) (h : ℝ) :
    w u (x1 + h) (y1 + h) * w u x2 y2 = w u (x2 + h) (y2 + h) * w u x1 y1 := by
  have hW1 := w_pos u hux huy h1
  have hW2 := w_pos u hux huy h2
  have hV1 := w_shift_pos u hA1 _ _ h hW1
  have hV2 := w_shift_pos u hA1 _ _ h hW2
  set W1 := w u x1 y1
  set W2 := w u x2 y2
  set V1 := w u (x1 + h) (y1 + h)
  set V2 := w u (x2 + h) (y2 + h)
  have hS : 0 < W1 + W2 := by linarith
  set a := W2 / (W1 + W2) with ha
  set b := W1 / (W1 + W2) with hb
  have ha0 : 0 ≤ a := div_nonneg hW2.le hS.le
  have hb0 : 0 ≤ b := div_nonneg hW1.le hS.le
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have hp : IsProbVec ![a, b] := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ha0, hb0]
    · simp [Fin.sum_univ_two, hab]
  -- the two comparisons
  have e0 : a * W1 - b * W2 = 0 := by rw [ha, hb]; field_simp; ring
  have e1 : a * V1 - b * V2 = (W2 * V1 - W1 * V2) / (W1 + W2) := by rw [ha, hb]; field_simp
  have hAB : ∀ s : ℝ, Prefers u ![a, b] ![x1 + s, y2 + s] ![y1 + s, x2 + s] ↔ 0 < a * w u (x1 + s) (y1 + s) - b * w u (x2 + s) (y2 + s) := by
    intro s
    rw [pref_w]
    simp [Fin.sum_univ_two, w_anti u (y2 + s) (x2 + s)]
    try (constructor <;> intro hh <;> linarith)
  have hBA : ∀ s : ℝ, Prefers u ![a, b] ![y1 + s, x2 + s] ![x1 + s, y2 + s] ↔ a * w u (x1 + s) (y1 + s) - b * w u (x2 + s) (y2 + s) < 0 := by
    intro s
    rw [pref_w]
    simp [Fin.sum_univ_two, w_anti u (y2 + s) (x2 + s), w_anti u (y1 + s) (x1 + s)]
    try (constructor <;> intro hh <;> linarith)
  have hsh1 := pref_iff u hA1 ![a, b] hp ![x1, y2] ![y1, x2] h
  have hsh2 := pref_iff u hA1 ![a, b] hp ![y1, x2] ![x1, y2] h
  have eA : (fun i : Fin 2 => (![x1, y2] : Fin 2 → ℝ) i + h) = ![x1 + h, y2 + h] := by
    funext i; fin_cases i <;> simp
  have eB : (fun i : Fin 2 => (![y1, x2] : Fin 2 → ℝ) i + h) = ![y1 + h, x2 + h] := by
    funext i; fin_cases i <;> simp
  rw [eA, eB] at hsh1 hsh2
  have h0 := hAB 0
  have h0' := hBA 0
  simp only [add_zero] at h0 h0'
  rw [hAB h] at hsh1
  rw [hBA h] at hsh2
  rw [h0] at hsh1
  rw [h0'] at hsh2
  have hsh1' : 0 < a * W1 - b * W2 ↔ 0 < a * V1 - b * V2 := hsh1
  have hsh2' : a * W1 - b * W2 < 0 ↔ a * V1 - b * V2 < 0 := hsh2
  rcases lt_trichotomy (W2 * V1) (W1 * V2) with hlt | heq | hgt
  · exfalso
    have h3 : a * V1 - b * V2 < 0 := by
      rw [e1]; apply div_neg_of_neg_of_pos _ hS; linarith
    have := hsh2'.2 h3
    linarith
  · linarith
  · exfalso
    have h3 : 0 < a * V1 - b * V2 := by
      rw [e1]; apply div_pos _ hS; linarith
    have := hsh1'.2 h3
    linarith

end BRRsf

open BRRsf in
theorem solution (u : ℝ → ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hA1 : Assumption1 u id) :
    ∃ k : ℝ → ℝ, (∀ h, 0 < k h) ∧
      ∀ x y h : ℝ, u (x + h) (y + h) - u (y + h) (x + h) = k h * (u x y - u y x) := by
  have hw1 : 0 < w u 1 0 := w_pos u hux huy one_pos
  refine ⟨fun h => w u (1 + h) (0 + h) / w u 1 0, fun h => ?_, ?_⟩
  · apply div_pos _ hw1
    apply w_pos u hux huy
    linarith
  · intro x y h
    show w u (x + h) (y + h) = w u (1 + h) (0 + h) / w u 1 0 * w u x y
    rcases lt_trichotomy x y with hlt | heq | hgt
    · have hc := cross u hux huy hA1 (x1 := 1) (y1 := 0) (x2 := y) (y2 := x) one_pos hlt h
      rw [w_anti u (x + h) (y + h), w_anti u x y]
      field_simp
      linarith [hc]
    · subst heq; simp [w]
    · have hc := cross u hux huy hA1 (x1 := 1) (y1 := 0) (x2 := x) (y2 := y) one_pos hgt h
      field_simp
      linarith [hc]
