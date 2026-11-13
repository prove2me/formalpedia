-- Prove2me | solution 1 for AutoregLTF.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.333774+00:00
-- url     : https://prove2.me/submissions/c27c8210-3538-490b-9304-bb5f4d328de6

import Mathlib
import Definitions.Def_AutoregLTF_coef
import Definitions.Def_AutoregLTF_sigma

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Claim1
open AutoregLTF


/-- membership in `assignUpd`, unpacked. -/
lemma mem_upd (m : ℕ) (e : ℤ × ℤ) :
    e ∈ assignUpd m ↔
      (e = (1, 2) ∨ e = ((p m : ℤ) - 1, 1 - Bconst m) ∨ e = ((p m : ℤ), Bconst m + 1) ∨
        e = ((p m : ℤ) + 1, -Bconst m - 1) ∨ e = ((piTest m : ℤ), Bconst m + 1) ∨
        e = ((piTest m : ℤ) + 1, Bconst m - 1)) ∨
      (∃ j, (1 ≤ j ∧ j ≤ m) ∧
        (e = ((piOut m j : ℤ), Bconst m - 2) ∨ e = ((piOut m j : ℤ) + 1, Bconst m - 1))) ∨
      (∃ j, (1 ≤ j ∧ j ≤ m + 1) ∧
        (e = ((piPtr m j : ℤ), Bconst m - 3) ∨ e = ((piPtr m j : ℤ) + 1, Bconst m - 1))) ∨
      (∃ n : ℕ, (p m / 3 + 1 ≤ n ∧ n < p m / 3 + 1 + p m / 3) ∧ e = ((n : ℤ), -Bconst m ^ 2)) := by
  simp only [assignUpd, List.pure_def, List.bind_eq_flatMap, List.mem_append, List.mem_flatMap, List.mem_range'_1,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false, List.mem_singleton]
  constructor
  · rintro (((h | ⟨a, ⟨h1, h2⟩, h⟩) | ⟨a, ⟨h1, h2⟩, h⟩) | ⟨a, ⟨n, ⟨h1, h2⟩, hn⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, ⟨h1, by omega⟩, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, ⟨h1, by omega⟩, h⟩))
    · subst hn; exact Or.inr (Or.inr (Or.inr ⟨n, ⟨h1, h2⟩, h.symm⟩))
  · rintro (h | ⟨a, ⟨h1, h2⟩, h⟩ | ⟨a, ⟨h1, h2⟩, h⟩ | ⟨n, ⟨h1, h2⟩, h⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨a, ⟨h1, by omega⟩, h⟩))
    · exact Or.inl (Or.inr ⟨a, ⟨h1, by omega⟩, h⟩)
    · exact Or.inr ⟨(n : ℤ), ⟨n, ⟨h1, h2⟩, rfl⟩, h.symm⟩

lemma upd_nodup (m : ℕ) (hm : 2 ≤ m) : ((assignUpd m).map Prod.fst).Nodup := by
  simp only [assignUpd, List.pure_def, List.bind_eq_flatMap, List.map_append, List.map_flatMap,
    List.nodup_append, List.nodup_flatMap]
  refine ⟨⟨⟨?_, ⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp only [p, piTest]; simp; omega
  · intro x hx; simp
  · refine (List.pairwise_lt_range' (s := 1) (n := m)).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left]
    intro x h1 h2
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h1 h2
    simp only [piOut, p] at h1 h2
    omega
  · intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_range'_1] at ha hb
    obtain ⟨j, ⟨h1, h2⟩, hb⟩ := hb
    try simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    simp only [piOut, piTest, p] at ha hb
    intro hab
    rcases ha with ha|ha|ha|ha|ha|ha <;> rcases hb with hb|hb <;> omega
  · intro x _; simp
  · refine (List.pairwise_lt_range' (s := 1) (n := m + 1)).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left]
    intro x h1 h2
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h1 h2
    simp only [piPtr, p] at h1 h2
    omega
  · intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_range'_1, List.mem_append] at ha hb
    obtain ⟨j, ⟨h1, h2⟩, hb⟩ := hb
    try simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    simp only [piOut, piPtr, piTest, p] at ha hb
    intro hab
    rcases ha with (ha|ha|ha|ha|ha|ha) | ⟨i, ⟨h3, h4⟩, ha|ha⟩ <;>
      rcases hb with hb|hb <;> omega
  · refine ⟨fun x _ => by simp, ?_⟩
    refine (List.pairwise_lt_range' (s := p m / 3 + 1) (n := p m / 3)).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left]
    intro x h1 h2
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h1 h2
    omega
  · intro a ha b hb
    simp only [List.mem_flatMap, List.mem_range'_1, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_append] at ha hb
    obtain ⟨n, ⟨h1, h2⟩, hb⟩ := hb
    intro hab
    simp only [piOut, piPtr, piTest, p] at ha h1 h2
    subst hb
    rcases ha with ((ha|ha|ha|ha|ha|ha) | ⟨i, ⟨h3, h4⟩, ha|ha⟩) | ⟨i, ⟨h3, h4⟩, ha|ha⟩ <;>
      omega


lemma beq_false_of_ne (a ℓ : ℤ) (ha : a ≠ ℓ) : (ℓ == a) = false := by
  rw [beq_eq_false_iff_ne]; exact fun h => ha h.symm

lemma lookup_of_mem (l : List (ℤ × ℤ)) (ℓ v : ℤ) (hmem : (ℓ, v) ∈ l)
    (hc : ∀ e ∈ l, e.1 = ℓ → e.2 = v) : l.lookup ℓ = some v := by
  induction l with
  | nil => simp at hmem
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    by_cases ha : a = ℓ
    · subst ha
      have := hc (a, b) (List.mem_cons_self) rfl
      simpa [List.lookup] using this
    · simp only [List.lookup, beq_false_of_ne a ℓ ha]
      refine ih ?_ (fun e he => hc e (List.mem_cons_of_mem _ he))
      rcases List.mem_cons.1 hmem with h | h
      · exact absurd (congrArg Prod.fst h).symm ha
      · exact h

lemma key_unique (l : List (ℤ × ℤ)) (hl : (l.map Prod.fst).Nodup) (a b c : ℤ)
    (hb : (a, b) ∈ l) (hc : (a, c) ∈ l) : b = c := by
  induction l with
  | nil => simp at hb
  | cons x t ih =>
    obtain ⟨x1, x2⟩ := x
    rw [List.map_cons, List.nodup_cons] at hl
    rcases List.mem_cons.1 hb with h | h <;> rcases List.mem_cons.1 hc with h' | h'
    · rw [Prod.mk.injEq] at h h'; rw [h.2, h'.2]
    · exfalso; rw [Prod.mk.injEq] at h; exact hl.1 (List.mem_map.2 ⟨_, h', by simp [h.1]⟩)
    · exfalso; rw [Prod.mk.injEq] at h'; exact hl.1 (List.mem_map.2 ⟨_, h, by simp [h'.1]⟩)
    · exact ih hl.2 h h'

lemma lookup_upd (m : ℕ) (hm : 2 ≤ m) (ℓ v : ℤ) (hmem : (ℓ, v) ∈ assignUpd m) :
    (assignUpd m).lookup ℓ = some v :=
  lookup_of_mem _ ℓ v hmem (fun e he hℓ => by
    have : e = (e.1, e.2) := rfl
    rw [this, hℓ] at he
    exact key_unique _ (upd_nodup m hm) ℓ _ _ he hmem)

end AutoregLTF.Dev.Claim1

namespace AutoregLTF
open AutoregLTF.Dev.Claim1

theorem aCoef_of_mem_assignUpd (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (ℓ v : ℤ)
    (hmem : (ℓ, v) ∈ assignUpd m) : aCoef m θ ℓ = v := by
  simp [aCoef, lookup_upd m hm ℓ v hmem]

end AutoregLTF
end

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Claim3
open AutoregLTF AutoregLTF.Dev.Claim1

lemma hp (m : ℕ) : p m = 378 * (m + 2) := rfl

/-- a true block bit sits at a position of `Π`. -/
lemma block_inPi (m : ℕ) (f : St) (r : ℕ) (h : block m f r = true) : InPi m r := by
  simp only [block, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range'_1] at h
  unfold InPi
  rcases h with (((h | ⟨j, ⟨h1, h2⟩, h, _⟩) | ⟨h | h, _⟩) | ⟨j, ⟨h1, h2⟩, h | h, _⟩) |
    ⟨j, ⟨h1, h2⟩, h | h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, Finset.mem_Icc.2 ⟨h1, by omega⟩, h⟩)
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, Finset.mem_Icc.2 ⟨h1, by omega⟩, Or.inl h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, Finset.mem_Icc.2 ⟨h1, by omega⟩, Or.inr h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_Icc.2 ⟨h1, by omega⟩, Or.inl h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_Icc.2 ⟨h1, by omega⟩, Or.inr h⟩)))

/-- positions of `Π` are `0` or strictly between `p/6` and `p/3`. -/
lemma inPi_range (m : ℕ) (hm : 2 ≤ m) (r : ℕ) (h : InPi m r) :
    r = 0 ∨ (63 * (m + 2) < r ∧ r < 126 * (m + 2)) := by
  simp only [InPi, Finset.mem_Icc, piRow, piTest, piOut, piPtr, p] at h
  rcases h with h | ⟨j, ⟨h1, h2⟩, h⟩ | h | ⟨j, ⟨h1, h2⟩, h⟩ | ⟨j, ⟨h1, h2⟩, h⟩
  · exact Or.inl h
  all_goals (right; omega)

lemma ehat_true (m : ℕ) (θ : ℕ → ℤ) (i t : ℕ) (k : ℤ) (h : Ehat m θ i t k = true) :
    (0 ≤ k ∧ InPi m k.toNat) ∨ (-(p m : ℤ) ≤ k ∧ k < 0 ∧ InPi m (k + p m).toNat) := by
  unfold Ehat at h
  split_ifs at h with h1 h2
  · exact Or.inr ⟨by omega, h2, block_inPi m _ _ h⟩
  · exact Or.inl ⟨by omega, block_inPi m _ _ h⟩

lemma ehat_zero (m : ℕ) (θ : ℕ → ℤ) (i t : ℕ) : Ehat m θ i t 0 = true := by
  simp [Ehat, E, block]

/-- key lemma: for a coefficient position strictly inside `(p/6, p/3)`. -/
lemma ehat_mid (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (i t r : ℕ) (hr : r < p m) (ℓ : ℤ)
    (h1 : 63 * ((m : ℤ) + 2) < ℓ) (h2 : ℓ < 126 * ((m : ℤ) + 2))
    (h : Ehat m θ i t ((r : ℤ) - ℓ) = true) :
    (r : ℤ) = ℓ ∨ (126 * (m + 2) < r ∧ r < 252 * (m + 2)) := by
  have hpc : (p m : ℤ) = 378 * ((m : ℤ) + 2) := by rw [hp]; push_cast; ring
  rw [hp] at hr
  rcases ehat_true m θ i t _ h with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
  · rcases inPi_range m hm _ h4 with h | h <;> omega
  · rcases inPi_range m hm _ h5 with h | h <;> omega

lemma ehat_p (m : ℕ) (θ : ℕ → ℤ) (i t r : ℕ) (hr : r < p m)
    (h : Ehat m θ i t ((r : ℤ) - (p m : ℤ)) = true) : InPi m r := by
  rcases ehat_true m θ i t _ h with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
  · omega
  · have : ((r : ℤ) - p m + p m).toNat = r := by omega
    rwa [this] at h5

/-! ### sums over lookups -/

lemma lookup_cons_cases (a b : ℤ) (t : List (ℤ × ℤ)) (ℓ : ℤ) :
    ((a, b) :: t).lookup ℓ = if a = ℓ then some b else t.lookup ℓ := by
  by_cases h : a = ℓ
  · subst h; simp [List.lookup]
  · simp only [List.lookup, beq_false_of_ne a ℓ h, h, if_false]

lemma lookup_sum_le (φ : ℤ → ℤ) (h0 : φ 0 = 0) (hn : ∀ x, 0 ≤ φ x) (l : List (ℤ × ℤ))
    (S : Finset ℤ) :
    ∑ ℓ ∈ S, φ ((l.lookup ℓ).getD 0) ≤ (l.map (fun e => φ e.2)).sum := by
  induction l with
  | nil => simp [List.lookup, h0]
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    have hle : ∀ ℓ, φ ((((a, b) :: t).lookup ℓ).getD 0) ≤
        (if a = ℓ then φ b else 0) + φ ((t.lookup ℓ).getD 0) := by
      intro ℓ
      rw [lookup_cons_cases]
      by_cases h : a = ℓ
      · simp only [h, if_true, Option.getD_some]; linarith [hn ((t.lookup ℓ).getD 0)]
      · simp [h]
    calc ∑ ℓ ∈ S, φ ((((a, b) :: t).lookup ℓ).getD 0)
        ≤ ∑ ℓ ∈ S, ((if a = ℓ then φ b else 0) + φ ((t.lookup ℓ).getD 0)) :=
          Finset.sum_le_sum (fun ℓ _ => hle ℓ)
      _ = (∑ ℓ ∈ S, (if a = ℓ then φ b else 0)) + ∑ ℓ ∈ S, φ ((t.lookup ℓ).getD 0) :=
          Finset.sum_add_distrib
      _ ≤ φ b + (t.map (fun e => φ e.2)).sum := by
          refine add_le_add ?_ ih
          rw [Finset.sum_ite_eq]
          split_ifs
          · exact le_refl _
          · exact hn b
      _ = _ := by simp

lemma lookup_sum_le_nat (φ : ℤ → ℤ) (h0 : φ 0 = 0) (hn : ∀ x, 0 ≤ φ x) (l : List (ℤ × ℤ))
    (S : Finset ℕ) :
    ∑ ℓ ∈ S, φ ((l.lookup (ℓ : ℤ)).getD 0) ≤ (l.map (fun e => φ e.2)).sum := by
  have := lookup_sum_le φ h0 hn l (S.map ⟨Nat.cast, Nat.cast_injective⟩)
  rwa [Finset.sum_map] at this

lemma lookup_some_mem (l : List (ℤ × ℤ)) (ℓ v : ℤ) (h : l.lookup ℓ = some v) : (ℓ, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    rw [lookup_cons_cases] at h
    by_cases hc : a = ℓ
    · simp only [hc, if_true, Option.some.injEq] at h
      subst h; subst hc; exact List.mem_cons_self
    · simp only [hc, if_false] at h
      exact List.mem_cons_of_mem _ (ih h)

lemma aCoef_cases (m : ℕ) (θ : ℕ → ℤ) (ℓ : ℤ) :
    (∃ v, (ℓ, v) ∈ assignUpd m ∧ aCoef m θ ℓ = v) ∨
      ((assignUpd m).lookup ℓ = none ∧ aCoef m θ ℓ = a0 m θ ℓ) := by
  unfold aCoef
  rcases hl : (assignUpd m).lookup ℓ with _ | v
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨v, lookup_some_mem _ _ _ hl, rfl⟩


lemma flatMap_sum_le {α : Type} (g : α → List (ℤ × ℤ)) (f : ℤ × ℤ → ℤ) (c : ℤ) (l : List α)
    (h : ∀ x ∈ l, ((g x).map f).sum ≤ c) :
    ((l.flatMap g).map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    push_cast; linarith

lemma assign0At_abs (m : ℕ) (θ : ℕ → ℤ) (j : ℕ) (hj : j ≤ m) (h0 : 0 ≤ θ j)
    (h1 : θ j ≤ 2 ^ m - 1) (hm : 2 ≤ m) :
    ((assign0At m θ j).map (fun e => |e.2|)).sum ≤ 16 * 2 ^ m := by
  have h2 : (2 : ℤ) ^ (j + 1) ≤ 2 * 2 ^ m := by
    rw [pow_succ]
    have : (2 : ℤ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj
    linarith
  have h3 : (0 : ℤ) < 2 ^ (j + 1) := by positivity
  have h4 : (4 : ℤ) ≤ 2 ^ m := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  simp only [assign0At, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, abs_neg,
    abs_of_nonneg h0, abs_of_pos h3, abs_one]
  rw [abs_mul, abs_of_nonneg h0]
  norm_num
  linarith

lemma assign0_abs_sum (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) :
    ((assign0 m θ).map (fun e => |e.2|)).sum ≤ 16 * m * 2 ^ m := by
  have := flatMap_sum_le (assign0At m θ) (fun e => |e.2|) (16 * 2 ^ m) (List.range' 1 m)
    (fun j hj => by
      rw [List.mem_range'_1] at hj
      have := hθ j (Finset.mem_Icc.2 ⟨hj.1, by omega⟩)
      exact assign0At_abs m θ j (by omega) this.1 this.2 hm)
  simp only [List.length_range'] at this
  unfold assign0
  linarith

lemma a0_sum (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) (S : Finset ℕ) :
    ∑ ℓ ∈ S, |a0 m θ (ℓ : ℤ)| ≤ 16 * m * 2 ^ m := by
  have := lookup_sum_le_nat (fun x => |x|) (by simp) (fun x => abs_nonneg x) (assign0 m θ) S
  exact this.trans (assign0_abs_sum m hm θ hθ)


lemma bconst_ge (m : ℕ) (hm : 2 ≤ m) : 128 * ((m : ℤ) + 2) ≤ Bconst m := by
  have h4 : (4 : ℤ) ≤ 2 ^ m := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  unfold Bconst
  rw [pow_add]
  have : (0 : ℤ) ≤ (m : ℤ) + 2 := by positivity
  nlinarith

lemma neg_sum (m : ℕ) (X : List ℤ) :
    ((X.map (fun ℓ => (ℓ, -Bconst m ^ 2))).map (fun e => max e.2 0)).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  simp only [Function.comp]
  exact max_eq_right (by nlinarith)

lemma upd_pos_sum (m : ℕ) (hm : 2 ≤ m) :
    ((assignUpd m).map (fun e => max e.2 0)).sum ≤ (4 * m + 5) * Bconst m + 3 := by
  have hB := bconst_ge m hm
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have e1 := flatMap_sum_le
    (fun j : ℕ => [((piOut m j : ℤ), Bconst m - 2), ((piOut m j : ℤ) + 1, Bconst m - 1)])
    (fun e => max e.2 0) (2 * Bconst m) (List.range' 1 m) (fun j _ => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith)
  have e2 := flatMap_sum_le
    (fun j : ℕ => [((piPtr m j : ℤ), Bconst m - 3), ((piPtr m j : ℤ) + 1, Bconst m - 1)])
    (fun e => max e.2 0) (2 * Bconst m) (List.range' 1 (m + 1)) (fun j _ => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith)
  simp only [List.length_range'] at e1 e2
  simp only [assignUpd, List.pure_def, List.bind_eq_flatMap, List.map_append, List.sum_append]
  rw [neg_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [max_eq_left (by linarith : (0 : ℤ) ≤ 2), max_eq_right (by linarith : 1 - Bconst m ≤ 0),
    max_eq_left (by linarith : (0 : ℤ) ≤ Bconst m + 1),
    max_eq_right (by linarith : -Bconst m - 1 ≤ 0),
    max_eq_left (by linarith : (0 : ℤ) ≤ Bconst m - 1)]
  push_cast at e1 e2
  nlinarith


lemma a_small (m : ℕ) (hm : 2 ≤ m) : 2 * (16 * (m : ℤ) * 2 ^ m) + 256 ≤ Bconst m := by
  have h4 : (4 : ℤ) ≤ 2 ^ m := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  unfold Bconst
  rw [pow_add]
  nlinarith

lemma mul_toNat_le (a : ℤ) (b : Bool) : a * (b.toNat : ℤ) ≤ max a 0 := by
  cases b <;> simp

lemma pos_le (m : ℕ) (θ : ℕ → ℤ) (ℓ : ℤ) :
    max (aCoef m θ ℓ) 0 ≤ max (((assignUpd m).lookup ℓ).getD 0) 0 + |a0 m θ ℓ| := by
  unfold aCoef
  rcases hl : (assignUpd m).lookup ℓ with _ | v
  · simp only [Option.getD_none, max_self, zero_add]; exact max_le (le_abs_self _) (abs_nonneg _)
  · simp only [Option.getD_some]; linarith [abs_nonneg (a0 m θ ℓ)]

lemma caseA (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1)
    (i : ℕ) (t r : ℕ) (hr : r < p m) (h1 : 126 * (m + 2) < r) (h2 : r ≤ 252 * (m + 2)) :
    sigma m θ i t r < 0 := by
  have hpc : (p m : ℤ) = 378 * ((m : ℤ) + 2) := by rw [hp]; push_cast; ring
  have hmem : ((r : ℤ), -Bconst m ^ 2) ∈ assignUpd m := by
    rw [mem_upd]
    refine Or.inr (Or.inr (Or.inr ⟨r, ⟨?_, ?_⟩, rfl⟩)) <;> rw [hp] <;> omega
  have har : aCoef m θ r = -Bconst m ^ 2 := aCoef_of_mem_assignUpd m hm θ hθ _ _ hmem
  have hterm : ∀ ℓ ∈ Finset.Icc 1 (p m + 1),
      aCoef m θ (ℓ : ℤ) * ((Ehat m θ i t ((r : ℤ) - ℓ)).toNat : ℤ) ≤
        (max (((assignUpd m).lookup (ℓ : ℤ)).getD 0) 0 + |a0 m θ (ℓ : ℤ)|) +
          (if r = ℓ then -Bconst m ^ 2 else 0) := by
    intro ℓ _
    by_cases h : r = ℓ
    · subst h
      rw [if_pos rfl, har, sub_self, ehat_zero]
      simp only [Bool.toNat_true, Nat.cast_one, mul_one]
      have := le_max_right (((assignUpd m).lookup (r : ℤ)).getD 0) 0
      linarith [abs_nonneg (a0 m θ r)]
    · rw [if_neg h, add_zero]
      exact (mul_toNat_le _ _).trans (pos_le m θ ℓ)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩)] at hsum
  have hU := lookup_sum_le_nat (fun x => max x 0) (by simp) (fun x => le_max_right _ _)
    (assignUpd m) (Finset.Icc 1 (p m + 1))
  have hU' := hU.trans (upd_pos_sum m hm)
  have hA := a0_sum m hm θ hθ (Finset.Icc 1 (p m + 1))
  have hB := bconst_ge m hm
  have hAB := a_small m hm
  have hBB : 128 * ((m : ℤ) + 2) * Bconst m ≤ Bconst m * Bconst m := by nlinarith
  have hmB : (0 : ℤ) ≤ (m : ℤ) * Bconst m := mul_nonneg (by positivity) (by linarith)
  unfold sigma
  have hB2 : Bconst m ^ 2 = Bconst m * Bconst m := sq _
  rw [hB2] at hsum
  nlinarith


lemma e_zero_mid (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ) (i t r : ℕ) (hr : r < p m)
    (hnot : ¬ InPi m r) (hcase : ¬ (126 * (m + 2) < r ∧ r ≤ 252 * (m + 2)))
    (ℓ : ℤ) (n : ℕ) (hℓ : ℓ = (n : ℤ)) (hn : InPi m n) (h1 : 63 * (m + 2) < n)
    (h2 : n < 126 * (m + 2)) : Ehat m θ i t ((r : ℤ) - ℓ) = false := by
  cases hb : Ehat m θ i t ((r : ℤ) - ℓ)
  · rfl
  · exfalso
    have h1' : 63 * ((m : ℤ) + 2) < ℓ := by rw [hℓ]; exact_mod_cast h1
    have h2' : ℓ < 126 * ((m : ℤ) + 2) := by rw [hℓ]; exact_mod_cast h2
    rcases ehat_mid m hm θ i t r hr ℓ h1' h2' hb with h | h
    · have : r = n := by omega
      exact hnot (this ▸ hn)
    · omega

lemma close_term (v a : ℤ) (b : Bool) (ℓ : ℕ)
    (h : v ≤ 0 ∨ (ℓ = 1 ∧ v ≤ 2) ∨ b = false) :
    v * (b.toNat : ℤ) ≤ (if ℓ = 1 then 2 else 0) + |a| := by
  have := abs_nonneg a
  rcases h with h | ⟨h1, h2⟩ | h
  · have := mul_toNat_le v b
    rw [max_eq_right h] at this
    split_ifs <;> linarith
  · rw [if_pos h1]
    cases b <;> simp <;> linarith
  · subst h; simp; split_ifs <;> linarith

lemma inPi_test (m : ℕ) : InPi m (piTest m) := Or.inr (Or.inr (Or.inl (Or.inl rfl)))
lemma inPi_test1 (m : ℕ) : InPi m (piTest m + 1) := Or.inr (Or.inr (Or.inl (Or.inr rfl)))
lemma inPi_out (m j : ℕ) (hj : 1 ≤ j ∧ j ≤ m) : InPi m (piOut m j) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨j, Finset.mem_Icc.2 hj, Or.inl rfl⟩)))
lemma inPi_out1 (m j : ℕ) (hj : 1 ≤ j ∧ j ≤ m) : InPi m (piOut m j + 1) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨j, Finset.mem_Icc.2 hj, Or.inr rfl⟩)))
lemma inPi_ptr (m j : ℕ) (hj : 1 ≤ j ∧ j ≤ m + 1) : InPi m (piPtr m j) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_Icc.2 hj, Or.inl rfl⟩)))
lemma inPi_ptr1 (m j : ℕ) (hj : 1 ≤ j ∧ j ≤ m + 1) : InPi m (piPtr m j + 1) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_Icc.2 hj, Or.inr rfl⟩)))

lemma caseB (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1)
    (i : ℕ) (t r : ℕ) (hr : r < p m) (hnot : ¬ InPi m r)
    (hcase : ¬ (126 * (m + 2) < r ∧ r ≤ 252 * (m + 2))) :
    sigma m θ i t r < 0 := by
  have hpc : (p m : ℤ) = 378 * ((m : ℤ) + 2) := by rw [hp]; push_cast; ring
  have hB := bconst_ge m hm
  have hterm : ∀ ℓ ∈ Finset.Icc 1 (p m + 1),
      aCoef m θ (ℓ : ℤ) * ((Ehat m θ i t ((r : ℤ) - ℓ)).toNat : ℤ) ≤
        (if ℓ = 1 then 2 else 0) + |a0 m θ (ℓ : ℤ)| := by
    intro ℓ _
    rcases aCoef_cases m θ (ℓ : ℤ) with ⟨v, hv, hav⟩ | ⟨_, hav⟩
    · rw [hav]
      apply close_term
      rw [mem_upd] at hv
      simp only [Prod.mk.injEq] at hv
      have hz := e_zero_mid m hm θ i t r hr hnot hcase
      rcases hv with ((⟨hl, hv⟩ | ⟨hl, hv⟩ | ⟨hl, hv⟩ | ⟨hl, hv⟩ | ⟨hl, hv⟩ | ⟨hl, hv⟩) |
        ⟨j, ⟨hj1, hj2⟩, (⟨hl, hv⟩ | ⟨hl, hv⟩)⟩ | ⟨j, ⟨hj1, hj2⟩, (⟨hl, hv⟩ | ⟨hl, hv⟩)⟩ |
        ⟨n, ⟨hn1, hn2⟩, hl, hv⟩)
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inl (by rw [hv]; linarith)
      · refine Or.inr (Or.inr ?_)
        have : (ℓ : ℤ) = p m := hl
        rw [this]
        cases hb : Ehat m θ i t ((r : ℤ) - (p m : ℤ))
        · rfl
        · exact absurd (ehat_p m θ i t r hr hb) hnot
      · exact Or.inl (by rw [hv]; linarith)
      · refine Or.inr (Or.inr (hz _ (piTest m) hl (inPi_test m) ?_ ?_)) <;> simp only [piTest, p] <;> omega
      · refine Or.inr (Or.inr (hz _ (piTest m + 1) (by rw [hl]; push_cast; rfl) (inPi_test1 m) ?_ ?_)) <;>
          simp only [piTest, p] <;> omega
      · refine Or.inr (Or.inr (hz _ (piOut m j) hl (inPi_out m j ⟨hj1, hj2⟩) ?_ ?_)) <;>
          simp only [piOut, p] <;> omega
      · refine Or.inr (Or.inr (hz _ (piOut m j + 1) (by rw [hl]; push_cast; rfl)
          (inPi_out1 m j ⟨hj1, hj2⟩) ?_ ?_)) <;> simp only [piOut, p] <;> omega
      · refine Or.inr (Or.inr (hz _ (piPtr m j) hl (inPi_ptr m j ⟨hj1, hj2⟩) ?_ ?_)) <;>
          simp only [piPtr, p] <;> omega
      · refine Or.inr (Or.inr (hz _ (piPtr m j + 1) (by rw [hl]; push_cast; rfl)
          (inPi_ptr1 m j ⟨hj1, hj2⟩) ?_ ?_)) <;> simp only [piPtr, p] <;> omega
      · exact Or.inl (by rw [hv]; nlinarith)
    · rw [hav]
      have := mul_toNat_le (a0 m θ (ℓ : ℤ)) (Ehat m θ i t ((r : ℤ) - ℓ))
      have h2 : max (a0 m θ (ℓ : ℤ)) 0 ≤ |a0 m θ (ℓ : ℤ)| := max_le (le_abs_self _) (abs_nonneg _)
      split_ifs <;> linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos
    (Finset.mem_Icc.2 ⟨le_refl _, by omega⟩)] at hsum
  have hA := a0_sum m hm θ hθ (Finset.Icc 1 (p m + 1))
  have hAB := a_small m hm
  unfold sigma
  linarith

end AutoregLTF.Dev.Claim3

namespace AutoregLTF
open AutoregLTF.Dev.Claim3 in
theorem chk_claim_3 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t r : ℕ) (hr : r < p m) (hnot : ¬ InPi m r) :
    sigma m θ i t r < 0 := by
  by_cases hc : 126 * (m + 2) < r ∧ r ≤ 252 * (m + 2)
  · exact caseA m hm θ hθ i t r hr hc.1 hc.2
  · exact caseB m hm θ hθ i t r hr hnot hc

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_claim_3 := @AutoregLTF.chk_claim_3
