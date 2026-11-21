-- Prove2me | solution 1 for DQI.Semicircle.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:21:50.450178+00:00
-- url     : https://prove2.me/submissions/b1e9f64c-34d1-4064-950d-4b149b082359

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQI_Semicircle_lemma_A_1

lemma esymm_zero' (s : Multiset ℝ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_left]

lemma esymm_one' (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map, Function.comp_def]

lemma esymm_cons (a : ℝ) (s : Multiset ℝ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t _
  simp [Multiset.prod_cons]

lemma key (α β : ℝ) (s : Multiset ℝ) (hs : ∀ y ∈ s, y ^ 2 = α * y + β) :
    ∀ k : ℕ, s.sum * s.esymm (k + 1) =
      ((k : ℝ) + 2) * s.esymm (k + 2) + α * ((k : ℝ) + 1) * s.esymm (k + 1) +
        β * ((Multiset.card s : ℝ) - k) * s.esymm k := by
  induction s using Multiset.induction_on with
  | empty =>
    intro k
    cases k with
    | zero => simp [Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.powersetCard_zero_right]
    | succ k => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a t ih =>
    intro k
    have ha : a ^ 2 = α * a + β := hs a (Multiset.mem_cons_self a t)
    have ih' := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    have hS1 : t.sum = t.esymm 1 := (esymm_one' t).symm
    rw [Multiset.sum_cons, Multiset.card_cons]
    cases k with
    | zero =>
      show (a + t.sum) * (a ::ₘ t).esymm 1 = (((0 : ℕ) : ℝ) + 2) * (a ::ₘ t).esymm 2 +
        α * (((0 : ℕ) : ℝ) + 1) * (a ::ₘ t).esymm 1 +
        β * (((Multiset.card t + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) * (a ::ₘ t).esymm 0
      have E1 : (a ::ₘ t).esymm 1 = t.esymm 1 + a := by
        have := esymm_cons a t 0
        rw [esymm_zero'] at this
        simpa using this
      have E2 : (a ::ₘ t).esymm 2 = t.esymm 2 + a * t.esymm 1 := esymm_cons a t 1
      have E0 : (a ::ₘ t).esymm 0 = 1 := esymm_zero' _
      have IH0 : t.sum * t.esymm 1 = (((0 : ℕ) : ℝ) + 2) * t.esymm 2 +
          α * (((0 : ℕ) : ℝ) + 1) * t.esymm 1 +
          β * ((Multiset.card t : ℝ) - ((0 : ℕ) : ℝ)) * t.esymm 0 := ih' 0
      rw [esymm_zero'] at IH0
      rw [E1, E2, E0]
      push_cast at IH0 ⊢
      linear_combination IH0 + ha + a * hS1
    | succ k =>
      have E1 : (a ::ₘ t).esymm (k + 1 + 1) = t.esymm (k + 1 + 1) + a * t.esymm (k + 1) :=
        esymm_cons a t (k + 1)
      have E2 : (a ::ₘ t).esymm (k + 1 + 2) = t.esymm (k + 1 + 2) + a * t.esymm (k + 1 + 1) :=
        esymm_cons a t (k + 1 + 1)
      have E0 : (a ::ₘ t).esymm (k + 1) = t.esymm (k + 1) + a * t.esymm k := esymm_cons a t k
      have IH1 := ih' (k + 1)
      have IH0 : t.sum * t.esymm (k + 1) = ((k : ℝ) + 2) * t.esymm (k + 1 + 1) +
          α * ((k : ℝ) + 1) * t.esymm (k + 1) + β * ((Multiset.card t : ℝ) - k) * t.esymm k :=
        ih' k
      rw [E1, E2, E0]
      push_cast at IH1 IH0 ⊢
      linear_combination IH1 + a * IH0 + t.esymm (k + 1) * ha

section W

variable {m : ℕ} (a b c : ℝ)

def Cn (x : Fin m → ℝ) : Prop := ∀ j, a * x j ^ 2 + b * x j + c = 0

def e (k : ℕ) (x : Fin m → ℝ) : ℝ := (Finset.univ.val.map x).esymm k

def InW (N : ℕ) (f : (Fin m → ℝ) → ℝ) : Prop :=
  ∃ v : ℕ → ℝ, ∀ x, Cn a b c x → f x = ∑ k ∈ Finset.range N, v k * e k x

variable {a b c}

lemma W_congr {N : ℕ} {f g : (Fin m → ℝ) → ℝ} (hf : InW a b c N f)
    (h : ∀ x, Cn a b c x → f x = g x) : InW a b c N g := by
  obtain ⟨v, hv⟩ := hf
  exact ⟨v, fun x hx => by rw [← h x hx, hv x hx]⟩

lemma W_mono {N N' : ℕ} (hN : N ≤ N') {f : (Fin m → ℝ) → ℝ} (hf : InW a b c N f) :
    InW a b c N' f := by
  obtain ⟨v, hv⟩ := hf
  refine ⟨fun k => if k < N then v k else 0, fun x hx => ?_⟩
  show f x = ∑ k ∈ Finset.range N', (if k < N then v k else 0) * e k x
  rw [hv x hx]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hN)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos (Finset.mem_range.mp hk)]
  · intro k _ hk
    rw [if_neg (fun h => hk (Finset.mem_range.mpr h)), zero_mul]

lemma W_add {N : ℕ} {f g : (Fin m → ℝ) → ℝ} (hf : InW a b c N f) (hg : InW a b c N g) :
    InW a b c N (fun x => f x + g x) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨w, hw⟩ := hg
  refine ⟨fun k => v k + w k, fun x hx => ?_⟩
  show f x + g x = ∑ k ∈ Finset.range N, (v k + w k) * e k x
  rw [hv x hx, hw x hx, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma W_smul {N : ℕ} (r : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : InW a b c N f) :
    InW a b c N (fun x => r * f x) := by
  obtain ⟨v, hv⟩ := hf
  refine ⟨fun k => r * v k, fun x hx => ?_⟩
  show r * f x = ∑ k ∈ Finset.range N, (r * v k) * e k x
  rw [hv x hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma W_zero (N : ℕ) : InW a b c N (m := m) (fun _ => 0) :=
  ⟨fun _ => 0, fun x _ => by simp⟩

lemma W_sum {N : ℕ} {ι : Type} (s : Finset ι) (F : ι → (Fin m → ℝ) → ℝ)
    (hF : ∀ i ∈ s, InW a b c N (F i)) : InW a b c N (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using W_zero (a := a) (b := b) (c := c) (m := m) N
  | insert i s hi ih =>
    have h1 := hF i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    refine W_congr (W_add h1 h2) (fun x _ => ?_)
    rw [Finset.sum_insert hi]

lemma W_e {N j : ℕ} (hj : j < N) : InW a b c N (m := m) (e j) := by
  refine ⟨fun k => if k = j then 1 else 0, fun x _ => ?_⟩
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range N) j, if_pos (Finset.mem_range.mpr hj)]

lemma W_se (ha : a ≠ 0) (k : ℕ) :
    InW a b c (k + 2) (m := m) (fun x => (∑ j, x j) * e k x) := by
  have hroot : ∀ x : Fin m → ℝ, Cn a b c x →
      ∀ y ∈ Finset.univ.val.map x, y ^ 2 = (-b / a) * y + (-c / a) := by
    intro x hx y hy
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hy
    have := hx j
    field_simp
    linarith
  have hsum : ∀ x : Fin m → ℝ, (∑ j, x j) = (Finset.univ.val.map x).sum := fun x => rfl
  have hcard : ∀ x : Fin m → ℝ, Multiset.card (Finset.univ.val.map x) = m := by
    intro x
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  cases k with
  | zero =>
    refine W_congr (W_e (N := 0 + 2) (j := 1) (by omega)) (fun x _ => ?_)
    simp only [e, esymm_zero', mul_one, hsum, esymm_one']
  | succ k =>
    have h3 : InW a b c (k + 1 + 2) (m := m) (fun x =>
        ((k : ℝ) + 2) * e (k + 2) x + ((-b / a) * ((k : ℝ) + 1) * e (k + 1) x +
          (-c / a) * ((m : ℝ) - k) * e k x)) :=
      W_add (W_smul _ (W_e (by omega))) (W_add (W_smul _ (W_e (by omega)))
        (W_smul _ (W_e (by omega))))
    refine W_congr h3 (fun x hx => ?_)
    have := key (-b / a) (-c / a) _ (hroot x hx) k
    rw [hcard x] at this
    simp only [e, hsum]
    rw [this]
    ring

lemma W_mul_s (ha : a ≠ 0) {N : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : InW a b c N f) :
    InW a b c (N + 1) (fun x => (∑ j, x j) * f x) := by
  obtain ⟨v, hv⟩ := hf
  have hg : InW a b c (N + 1)
      (fun x : Fin m → ℝ => ∑ k ∈ Finset.range N, v k * ((∑ j, x j) * e k x)) := by
    apply W_sum
    intro k hk
    exact W_smul _ (W_mono (by have := Finset.mem_range.mp hk; omega) (W_se ha k))
  refine W_congr hg (fun x hx => ?_)
  rw [hv x hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma W_pow (ha : a ≠ 0) (n : ℕ) : InW a b c (n + 1) (m := m) (fun x => (∑ j, x j) ^ n) := by
  induction n with
  | zero =>
    refine W_congr (W_e (N := 0 + 1) (j := 0) (by omega)) (fun x _ => ?_)
    simp [e, esymm_zero']
  | succ n ih =>
    refine W_congr (W_mul_s ha ih) (fun x _ => ?_)
    ring

end W

end Aux_DQI_Semicircle_lemma_A_1

open Aux_DQI_Semicircle_lemma_A_1 in
theorem solution (P : Polynomial ℝ) (a b c : ℝ) (ha : a ≠ 0) (m : ℕ) :
    ∃ u : ℕ → ℝ, ∀ x : Fin m → ℝ, (∀ j, a * x j ^ 2 + b * x j + c = 0) →
      P.eval (∑ j, x j) =
        ∑ k ∈ Finset.range (P.natDegree + 1), u k * (Finset.univ.val.map x).esymm k := by
  have hW : InW a b c (P.natDegree + 1) (m := m) (fun x => P.eval (∑ j, x j)) := by
    have h1 : InW a b c (P.natDegree + 1) (m := m) (fun x =>
        ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * (∑ j, x j) ^ n) := by
      apply W_sum
      intro n hn
      exact W_smul _ (W_mono (by have := Finset.mem_range.mp hn; omega) (W_pow ha n))
    refine W_congr h1 (fun x _ => ?_)
    rw [Polynomial.eval_eq_sum_range]
  obtain ⟨v, hv⟩ := hW
  exact ⟨v, fun x hx => hv x hx⟩
