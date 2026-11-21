-- Prove2me | solution 1 for FracTruthSched.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:03:32.513811+00:00
-- url     : https://prove2.me/submissions/7e0268d8-00ef-4f3f-8c07-46b066d54243

import Mathlib
import Definitions.Def_FracTruthSched_IsAdditiveOn
import Definitions.Def_FracTruthSched_IsSymmetricOn

section
set_option autoImplicit false

namespace FracTruthSched.Dev.L3
open FracTruthSched
open scoped Classical

variable {τ : Type*} [Fintype τ] [DecidableEq τ] {k : ℕ}

noncomputable def vec (cl : τ → Fin k) (e : Fin k → τ) (v : ℝ) (A B : Finset (Fin k)) : τ → ℝ :=
  fun d => if cl d ∈ A ∨ ∃ j ∈ B, e j = d then v else 0

lemma vec_nonneg (cl : τ → Fin k) (e : Fin k → τ) {v : ℝ} (hv : 0 ≤ v) (A B : Finset (Fin k)) :
    ∀ d, 0 ≤ vec cl e v A B d := by
  intro d; unfold vec; split_ifs <;> simp [hv]

lemma twelve (cl : τ → Fin k) (e : Fin k → τ) (he : ∀ j, cl (e j) = j) {ℓ : ℕ}
    (hcard : ∀ j, (Finset.univ.filter (fun d => cl d = j)).card = ℓ)
    (V : (τ → ℝ) → ℝ)
    (hadd : ∀ j, IsAdditiveOn V (Finset.univ.filter (fun d => cl d = j)))
    (hsym : ∀ j, IsSymmetricOn V (Finset.univ.filter (fun d => cl d = j)))
    (v : ℝ) (hv : 0 ≤ v) (A B : Finset (Fin k)) (j : Fin k) (hjA : j ∉ A) (hjB : j ∉ B) :
    V (vec cl e v A (insert j B)) =
      (1 - 1 / (ℓ : ℝ)) * V (vec cl e v A B) + (1 / (ℓ : ℝ)) * V (vec cl e v (insert j A) B) := by
  set D := Finset.univ.filter (fun d => cl d = j) with hD
  have hℓ : (0 : ℝ) < ℓ := by
    have : 0 < D.card := Finset.card_pos.mpr ⟨e j, by simp [hD, he]⟩
    rw [hcard j] at this; exact_mod_cast this
  set t := vec cl e v A B with ht
  have hz : ∀ d ∈ D, t d = 0 := by
    intro d hd
    have hcd : cl d = j := by simpa [hD] using hd
    simp only [ht, vec]
    rw [if_neg]
    rintro (h | ⟨i, hi, rfl⟩)
    · exact hjA (hcd ▸ h)
    · exact hjB (by rw [he] at hcd; exact hcd ▸ hi)
  have hta : vec cl e v (insert j A) B = fun d => if d ∈ D then v else t d := by
    funext d
    by_cases hd : d ∈ D
    · have hcd : cl d = j := by simpa [hD] using hd
      simp [vec, hd, hcd]
    · have hcd : cl d ≠ j := by simpa [hD] using hd
      simp [vec, hd, hcd, ht]
  have htb : vec cl e v A (insert j B) = Function.update t (e j) v := by
    funext d
    by_cases hd : d = e j
    · subst hd; simp [vec]
    · simp only [vec, Function.update, hd, dif_neg, not_false_eq_true, ht]
      simp only [Finset.mem_insert]
      congr 1
      apply propext
      constructor
      · rintro (h | ⟨i, hi | hi, hid⟩)
        · exact Or.inl h
        · exact absurd (hi ▸ hid.symm) hd
        · exact Or.inr ⟨i, hi, hid⟩
      · rintro (h | ⟨i, hi, hid⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, Or.inr hi, hid⟩
  have hnn : ∀ d, 0 ≤ (fun d => if d ∈ D then v else t d) d := by
    intro d; simp only; split_ifs
    · exact hv
    · exact vec_nonneg cl e hv A B d
  have h0 : (fun d => if d ∈ D then (0:ℝ) else (fun d => if d ∈ D then v else t d) d) = t := by
    funext d
    by_cases hd : d ∈ D
    · simp [hd, hz d hd]
    · simp [hd]
  have hA := hadd j _ hnn
  rw [h0] at hA
  have hsum : ∑ e' ∈ D, (V (Function.update t e' ((fun d => if d ∈ D then v else t d) e')) - V t)
      = ℓ * (V (Function.update t (e j) v) - V t) := by
    have : ∀ e' ∈ D, V (Function.update t e' ((fun d => if d ∈ D then v else t d) e')) - V t
        = V (Function.update t (e j) v) - V t := by
      intro e' he'
      simp only [he', if_true]
      by_cases hee : e' = e j
      · rw [hee]
      · have := hsym j (Equiv.swap e' (e j)) (by
          intro d hd
          rw [Equiv.swap_apply_of_ne_of_ne]
          · rintro rfl; exact hd he'
          · rintro rfl; exact hd (by simp [hD, he])) (Function.update t e' v)
          (by
            intro d; by_cases hd : d = e'
            · subst hd; simp [hv]
            · simp only [Function.update, hd, dif_neg, not_false_eq_true]; exact vec_nonneg cl e hv A B d)
        have heq : (Function.update t e' v) ∘ (Equiv.swap e' (e j)) = Function.update t (e j) v := by
          have h2 := hz (e j) (by simp [hD, he])
          have h3 := hz e' he'
          funext d
          simp only [Function.comp, Function.update_apply, Equiv.swap_apply_def]
          by_cases h1 : d = e'
          · subst h1; simp [Ne.symm hee, hee, h2, h3]
          · by_cases h4 : d = e j
            · subst h4; simp [h1, hee, Ne.symm h1]
            · simp [h1, h4]
        rw [heq] at this; rw [this]
    rw [Finset.sum_congr rfl this, Finset.sum_const, hcard j]; simp
  rw [hsum] at hA
  rw [htb, hta]
  have hℓ' : (ℓ : ℝ) ≠ 0 := hℓ.ne'
  field_simp
  field_simp at hA
  linarith

lemma expand (cl : τ → Fin k) (e : Fin k → τ) (he : ∀ j, cl (e j) = j) {ℓ : ℕ}
    (hcard : ∀ j, (Finset.univ.filter (fun d => cl d = j)).card = ℓ)
    (V : (τ → ℝ) → ℝ)
    (hadd : ∀ j, IsAdditiveOn V (Finset.univ.filter (fun d => cl d = j)))
    (hsym : ∀ j, IsSymmetricOn V (Finset.univ.filter (fun d => cl d = j)))
    (v : ℝ) (hv : 0 ≤ v) (B : Finset (Fin k)) :
    ∀ A : Finset (Fin k), Disjoint A B →
      V (vec cl e v A B) = ∑ C ∈ B.powerset,
        (1 / (ℓ : ℝ)) ^ C.card * (1 - 1 / (ℓ : ℝ)) ^ (B.card - C.card) *
          V (vec cl e v (A ∪ C) ∅) := by
  induction B using Finset.induction_on with
  | empty => intro A _; simp
  | insert j B' hj ih =>
    intro A hA
    have hjA : j ∉ A := fun h => (Finset.disjoint_left.mp hA h) (Finset.mem_insert_self _ _)
    have hAB : Disjoint A B' := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hA
    have hjAB : Disjoint (insert j A) B' := by
      rw [Finset.disjoint_insert_left]; exact ⟨hj, hAB⟩
    rw [twelve cl e he hcard V hadd hsym v hv A B' j hjA hj, ih A hAB, ih _ hjAB,
      Finset.sum_powerset_insert hj, Finset.card_insert_of_notMem hj, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun C hC => ?_
      have hCB : C ⊆ B' := Finset.mem_powerset.mp hC
      have : B'.card + 1 - C.card = (B'.card - C.card) + 1 := by
        have := Finset.card_le_card hCB; omega
      rw [this, pow_succ]; ring
    · refine Finset.sum_congr rfl fun C hC => ?_
      have hCB : C ⊆ B' := Finset.mem_powerset.mp hC
      have hjC : j ∉ C := fun h => hj (hCB h)
      rw [Finset.card_insert_of_notMem hjC, Finset.insert_union, Finset.union_insert]
      have : B'.card + 1 - (C.card + 1) = B'.card - C.card := by omega
      rw [this, pow_succ]; ring

lemma vec_empty_singleton (cl : τ → Fin k) (e : Fin k → τ) (he : ∀ j, cl (e j) = j) (v : ℝ) (j : Fin k) :
    vec cl e v ∅ {j} = Pi.single (e j) v := by
  funext d
  by_cases hd : d = e j
  · subst hd; simp [vec]
  · simp [vec, hd, Ne.symm hd]

lemma vec_empty_full (cl : τ → Fin k) (e : Fin k → τ) (v : ℝ) :
    vec cl e v ∅ Finset.univ = fun d => if d ∈ Finset.univ.image e then v else 0 := by
  funext d; simp [vec]

end FracTruthSched.Dev.L3

namespace FracTruthSched
theorem chk_lemma_3 {τ : Type*} [Fintype τ] [DecidableEq τ] {k ℓ : ℕ} (cl : τ → Fin k)
    (hcard : ∀ j, (Finset.univ.filter (fun d => cl d = j)).card = ℓ)
    (V : (τ → ℝ) → ℝ) (x : (τ → ℝ) → τ → ℝ)
    (hx : ∀ a, (∀ d, 0 ≤ a d) → ∀ d, 0 ≤ x a d)
    (hinc : ∀ a b, (∀ d, 0 ≤ a d) → (∀ d, 0 ≤ b d) →
      ∑ d, x b d * (b d - a d) ≤ V b - V a ∧ V b - V a ≤ ∑ d, x a d * (b d - a d))
    (hadd : ∀ j, IsAdditiveOn V (Finset.univ.filter (fun d => cl d = j)))
    (hsym : ∀ j, IsSymmetricOn V (Finset.univ.filter (fun d => cl d = j)))
    (e : Fin k → τ) (he : ∀ j, cl (e j) = j) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    (1 - 1 / (ℓ : ℝ)) ^ (k - 1) * ∑ j, x (Pi.single (e j) 1) (e j) ≤
      ∑ j, x (fun d => if d ∈ Finset.univ.image e then u else 0) (e j) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hℓ : (0 : ℝ) < ℓ := by
    have h := hcard ⟨0, hk⟩
    have : 0 < (Finset.univ.filter (fun d => cl d = (⟨0, hk⟩ : Fin k))).card :=
      Finset.card_pos.mpr ⟨e ⟨0, hk⟩, by simp [he]⟩
    rw [h] at this; exact_mod_cast this
  obtain ⟨hu0, hu1⟩ := hu
  set c : ℝ := 1 - 1 / (ℓ : ℝ) with hc
  have hc0 : 0 ≤ c := by
    have : 1 / (ℓ : ℝ) ≤ 1 := by
      rw [div_le_one hℓ]
      have h := hcard ⟨0, hk⟩
      have : 0 < (Finset.univ.filter (fun d => cl d = (⟨0, hk⟩ : Fin k))).card :=
        Finset.card_pos.mpr ⟨e ⟨0, hk⟩, by simp [he]⟩
      rw [h] at this; exact_mod_cast this
    linarith
  have hEinj : Function.Injective e := fun a b h => by rw [← he a, ← he b, h]
  -- monotonicity
  have mono : ∀ A B : Finset (Fin k), 0 ≤ V (Dev.L3.vec cl e 1 A B) - V (Dev.L3.vec cl e u A B) := by
    intro A B
    have h := (hinc (Dev.L3.vec cl e u A B) (Dev.L3.vec cl e 1 A B)
      (Dev.L3.vec_nonneg cl e hu0.le A B) (Dev.L3.vec_nonneg cl e zero_le_one A B)).1
    refine le_trans (Finset.sum_nonneg fun d _ => mul_nonneg
      (hx _ (Dev.L3.vec_nonneg cl e zero_le_one A B) d) ?_) h
    simp only [Dev.L3.vec]
    split_ifs <;> linarith
  -- single class
  have single : ∀ j, ℓ * (1 - u) * x (Pi.single (e j) 1) (e j) ≤
      (V (Dev.L3.vec cl e 1 {j} ∅) - V (Dev.L3.vec cl e u {j} ∅)) := by
    intro j
    have t1 := Dev.L3.twelve cl e he hcard V hadd hsym 1 zero_le_one ∅ ∅ j (by simp) (by simp)
    have t2 := Dev.L3.twelve cl e he hcard V hadd hsym u hu0.le ∅ ∅ j (by simp) (by simp)
    have z1 : Dev.L3.vec cl e 1 ∅ ∅ = Dev.L3.vec cl e u ∅ ∅ := by
      funext d; simp [Dev.L3.vec]
    have z2 : insert j (∅ : Finset (Fin k)) = {j} := rfl
    rw [z2] at t1 t2
    rw [z1] at t1
    have hl : V (Dev.L3.vec cl e 1 {j} ∅) - V (Dev.L3.vec cl e u {j} ∅) =
        ℓ * (V (Dev.L3.vec cl e 1 ∅ {j}) - V (Dev.L3.vec cl e u ∅ {j})) := by
      have hℓ' : (ℓ : ℝ) ≠ 0 := hℓ.ne'
      field_simp at t1 t2
      linarith
    rw [hl, Dev.L3.vec_empty_singleton cl e he, Dev.L3.vec_empty_singleton cl e he]
    have := (hinc (Pi.single (e j) u : τ → ℝ) (Pi.single (e j) 1 : τ → ℝ)
      (fun d => by by_cases h : d = e j <;> simp [h, hu0.le])
      (fun d => by by_cases h : d = e j <;> simp [h])).1
    have hs : ∑ d, x (Pi.single (e j) 1 : τ → ℝ) d * ((Pi.single (e j) 1 : τ → ℝ) d - (Pi.single (e j) u : τ → ℝ) d) =
        x (Pi.single (e j) 1 : τ → ℝ) (e j) * (1 - u) := by
      rw [Finset.sum_eq_single (e j)]
      · simp
      · intro d _ hd; simp [hd]
      · simp
    rw [hs] at this
    nlinarith
  -- the full expansion
  have hexp : ∀ v, 0 ≤ v → V (Dev.L3.vec cl e v ∅ Finset.univ) = ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset,
        (1 / (ℓ : ℝ)) ^ C.card * c ^ (k - C.card) * V (Dev.L3.vec cl e v C ∅) := by
    intro v hv
    have := Dev.L3.expand cl e he hcard V hadd hsym v hv Finset.univ ∅ (by simp)
    simp only [Finset.empty_union, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hdiff : V (Dev.L3.vec cl e 1 ∅ Finset.univ) - V (Dev.L3.vec cl e u ∅ Finset.univ) =
      ∑ C ∈ (Finset.univ : Finset (Fin k)).powerset,
        (1 / (ℓ : ℝ)) ^ C.card * c ^ (k - C.card) *
          (V (Dev.L3.vec cl e 1 C ∅) - V (Dev.L3.vec cl e u C ∅)) := by
    rw [hexp 1 zero_le_one, hexp u hu0.le, ← Finset.sum_sub_distrib]
    simp only [mul_sub]
  have hlow : ∑ j : Fin k, (1 / (ℓ : ℝ)) * c ^ (k - 1) * (V (Dev.L3.vec cl e 1 {j} ∅) - V (Dev.L3.vec cl e u {j} ∅))
      ≤ V (Dev.L3.vec cl e 1 ∅ Finset.univ) - V (Dev.L3.vec cl e u ∅ Finset.univ) := by
    rw [hdiff]
    have himg : ∑ j : Fin k, (1 / (ℓ : ℝ)) * c ^ (k - 1) *
        (V (Dev.L3.vec cl e 1 {j} ∅) - V (Dev.L3.vec cl e u {j} ∅)) =
        ∑ C ∈ (Finset.univ : Finset (Fin k)).image (fun j => ({j} : Finset (Fin k))),
          (1 / (ℓ : ℝ)) ^ C.card * c ^ (k - C.card) *
            (V (Dev.L3.vec cl e 1 C ∅) - V (Dev.L3.vec cl e u C ∅)) := by
      rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp
    rw [himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun C hC => by simp)
      (fun C _ _ => mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hc0 _)) (mono C ∅))
  -- upper bound
  have hup := (hinc (fun d => if d ∈ Finset.univ.image e then u else 0)
      (fun d => if d ∈ Finset.univ.image e then 1 else 0)
      (fun d => by split_ifs <;> simp [hu0.le]) (fun d => by split_ifs <;> simp)).2
  have hsup : ∑ d, x (fun d => if d ∈ Finset.univ.image e then u else 0) d *
      ((fun d => if d ∈ Finset.univ.image e then (1:ℝ) else 0) d -
        (fun d => if d ∈ Finset.univ.image e then u else 0) d) =
      (1 - u) * ∑ j, x (fun d => if d ∈ Finset.univ.image e then u else 0) (e j) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))
      (fun d _ hd => by simp [hd])]
    rw [Finset.sum_image (fun a _ b _ h => hEinj h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp; ring
  rw [hsup] at hup
  rw [Dev.L3.vec_empty_full cl e 1, Dev.L3.vec_empty_full cl e u] at hlow
  -- combine
  have hsingle : ∑ j : Fin k, (1 / (ℓ : ℝ)) * c ^ (k - 1) * (ℓ * (1 - u) * x (Pi.single (e j) 1) (e j)) ≤
      ∑ j : Fin k, (1 / (ℓ : ℝ)) * c ^ (k - 1) * (V (Dev.L3.vec cl e 1 {j} ∅) - V (Dev.L3.vec cl e u {j} ∅)) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (single j)
      (mul_nonneg (by positivity) (pow_nonneg hc0 _))
  have hlhs : ∑ j : Fin k, (1 / (ℓ : ℝ)) * c ^ (k - 1) * (ℓ * (1 - u) * x (Pi.single (e j) 1) (e j)) =
      (1 - u) * (c ^ (k - 1) * ∑ j, x (Pi.single (e j) 1) (e j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hlhs] at hsingle
  have : (1 - u) * (c ^ (k - 1) * ∑ j, x (Pi.single (e j) 1) (e j)) ≤
      (1 - u) * ∑ j, x (fun d => if d ∈ Finset.univ.image e then u else 0) (e j) := by
    linarith
  exact le_of_mul_le_mul_left this (by linarith)

end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_lemma_3 := @FracTruthSched.chk_lemma_3
