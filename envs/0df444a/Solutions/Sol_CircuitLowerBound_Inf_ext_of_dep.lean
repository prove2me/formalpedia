-- Prove2me | solution 1 for CircuitLowerBound.Inf.ext_of_dep
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:23:45.205196+00:00
-- url     : https://prove2.me/submissions/aa72b37b-304a-416a-ac92-e0a5772825c9

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

private theorem wires_append' (x : List Bool) (C D : Circuit) :
    wires x (C ++ D) = wires (wires x C) D := List.foldl_append

private theorem wires_concat' (x : List Bool) (C : Circuit) (G : Gate) :
    wires x (C ++ [G]) =
      wires x C ++ [G.op ((wires x C).getD G.in₁ false) ((wires x C).getD G.in₂ false)] := by
  simp [wires]

private theorem length_wires' (x : List Bool) (C : Circuit) :
    (wires x C).length = x.length + C.length := by
  induction C using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton C G ih =>
    rw [wires_concat', List.length_append, ih, List.length_append]; simp; omega

private theorem prefix_wires' (x : List Bool) (C : Circuit) : x <+: wires x C := by
  induction C using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton C G ih =>
    rw [wires_concat']; exact ih.trans (List.prefix_append _ _)

private theorem getD_of_prefix' {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) : l₂.getD i false = l₁.getD i false := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

private theorem Avail_mono' {n : ℕ} {C : Circuit} {g : List Bool → Bool}
    (h : Avail n C g) (D : Circuit) : Avail n (C ++ D) g := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, by rw [List.length_append]; omega, fun x hx => ?_⟩
  rw [wires_append', getD_of_prefix' (prefix_wires' _ D) (by rw [length_wires', hx]; exact hw), h x hx]

private theorem Avail_gate' {n : ℕ} {C : Circuit} {g₁ g₂ : List Bool → Bool}
    (h₁ : Avail n C g₁) (h₂ : Avail n C g₂) (op : Bool → Bool → Bool) :
    ∃ G : Gate, Avail n (C ++ [G]) fun x => op (g₁ x) (g₂ x) := by
  obtain ⟨w₁, -, h₁⟩ := h₁
  obtain ⟨w₂, -, h₂⟩ := h₂
  refine ⟨⟨op, w₁, w₂⟩, n + C.length, by simp, fun x hx => ?_⟩
  rw [wires_concat', List.getD_append_right _ _ _ _ (by rw [length_wires', hx]),
    length_wires', hx, h₁ x hx, h₂ x hx]
  simp

private theorem Ext_congr' {n : ℕ} {g g' : List Bool → Bool}
    (h : Ext n g) (e : ∀ x : List Bool, x.length = n → g x = g' x) : Ext n g' := fun C₀ => by
  obtain ⟨D, w, hw, hD⟩ := h C₀
  exact ⟨D, w, hw, fun x hx => (hD x hx).trans (e x hx)⟩

private theorem Ext_op' {n : ℕ} {g₁ g₂ : List Bool → Bool}
    (h₁ : Ext n g₁) (h₂ : Ext n g₂) (op : Bool → Bool → Bool) :
    Ext n fun x => op (g₁ x) (g₂ x) := fun C₀ => by
  obtain ⟨D₁, a₁⟩ := h₁ C₀
  obtain ⟨D₂, a₂⟩ := h₂ (C₀ ++ D₁)
  obtain ⟨G, a⟩ := Avail_gate' (Avail_mono' a₁ D₂) a₂ op
  exact ⟨D₁ ++ D₂ ++ [G], by simpa only [List.append_assoc] using a⟩

private theorem ext_proj' {n i : ℕ} (hi : i < n) : Ext n fun x => x.getD i false := fun C₀ =>
  ⟨[], i, by omega, fun x hx => by
    rw [List.append_nil]
    exact getD_of_prefix' (prefix_wires' x C₀) (by omega)⟩

private theorem ext_const' (n : ℕ) (b : Bool) : Ext n fun _ => b := fun C₀ =>
  ⟨[⟨fun _ _ => b, 0, 0⟩], n + C₀.length, by simp, fun x hx => by
    rw [wires_concat', List.getD_append_right _ _ _ _ (by rw [length_wires', hx]), length_wires', hx]
    simp⟩

theorem solution {n : ℕ} : ∀ k, k ≤ n → ∀ g : List Bool → Bool,
    (∀ x y : List Bool, x.length = n → y.length = n → x.take k = y.take k → g x = g y) →
    Ext n g := by
  intro k
  induction k with
  | zero =>
    intro _ g hg
    exact Ext_congr' (ext_const' n (g (List.replicate n false))) fun x hx =>
      hg _ _ (by simp) hx (by simp)
  | succ k ih =>
    intro hk g hg
    have hdep : ∀ b : Bool, Ext n fun x => g (x.set k b) := fun b =>
      ih (by omega) _ fun x y hx hy hxy => hg _ _ (by simpa using hx) (by simpa using hy) (by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < k + 1
        · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi, List.getElem?_set, List.getElem?_set]
          by_cases hik : k = i
          · simp [hik, hx, hy]
          · have h1 : (x.take k)[i]? = (y.take k)[i]? := by rw [hxy]
            rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at h1
            simp [hik, h1]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])
    have h1 :=
      Ext_op'
        (Ext_op' (ext_proj' (n := n) (i := k) (by omega)) (hdep true) fun p q => p && q)
        (Ext_op' (ext_proj' (n := n) (i := k) (by omega)) (hdep false) fun p q => !p && q)
        fun p q => p || q
    refine Ext_congr' h1 fun x hx => ?_
    have hset : x.set k (x.getD k false) = x := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.set_getElem_self _
    cases hb : x.getD k false <;> rw [hb] at hset <;> simp [hset]
