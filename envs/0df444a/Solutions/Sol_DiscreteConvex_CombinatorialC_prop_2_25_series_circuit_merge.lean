-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.prop_2_25_series_circuit_merge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:46:58.154852+00:00
-- url     : https://prove2.me/submissions/e6a671d2-7b13-44dc-ac2f-df842ce8ef1c

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

set_option autoImplicit false

namespace P225
open DiscreteConvex.CombinatorialC
open Fin.NatCast

lemma fin01 (x y : Fin (0+1)) : x = y := Fin.ext (by have := x.isLt; have := y.isLt; omega)

lemma pair_cases {V : Type*} [DecidableEq V] {p q r s : V} (h : ({p, q} : Finset V) = {r, s}) :
    (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  have hp : p ∈ ({r, s} : Finset V) := h ▸ by simp
  have hq : q ∈ ({r, s} : Finset V) := h ▸ by simp
  have hr : r ∈ ({p, q} : Finset V) := h.symm ▸ by simp
  have hs : s ∈ ({p, q} : Finset V) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr hs
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> tauto

lemma fin_add_nat {k : ℕ} (a : Fin (k+1)) (m : ℕ) (hm : m < k+1) :
    (a + (m : Fin (k+1))).val = if a.val + m < k+1 then a.val + m else a.val + m - (k+1) := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hm]
  have := a.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma fin_sub_nat {k : ℕ} (a : Fin (k+1)) (m : ℕ) (hm : m < k+1) :
    (a - (m : Fin (k+1))).val = if m ≤ a.val then a.val - m else a.val + (k+1) - m := by
  have ha := a.isLt
  have hr : (if m ≤ a.val then a.val - m else a.val + (k+1) - m) < k+1 := by split_ifs <;> omega
  have : a - (m : Fin (k+1)) = ⟨_, hr⟩ := by
    rw [sub_eq_iff_eq_add]
    ext
    rw [fin_add_nat _ _ hm]
    simp only
    split_ifs <;> omega
  rw [this]

lemma fin_natCast_val {k : ℕ} (m : ℕ) (hm : m < k+1) : ((m : Fin (k+1))).val = m := by
  rw [Fin.val_natCast, Nat.mod_eq_of_lt hm]

lemma fin_succ_cases {k : ℕ} (i : Fin (k+1)) :
    (i.val = k ∧ (i + 1 : Fin (k+1)).val = 0) ∨ (i.val < k ∧ (i + 1 : Fin (k+1)).val = i.val + 1) := by
  rw [Fin.val_add_one]
  split_ifs with h
  · left; exact ⟨by rw [h, Fin.val_last], rfl⟩
  · right
    have : i.val ≠ k := fun h' => h (Fin.ext (by rw [h', Fin.val_last]))
    exact ⟨by have := i.isLt; omega, rfl⟩

variable {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]

lemma bdry_eq (src dst : A → V) (x : A → ℝ) (w : V) :
    Boundary src dst x w =
      ∑ a, x a * ((if src a = w then 1 else 0) - (if dst a = w then 1 else 0)) := by
  unfold Boundary
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

lemma sum_cycle {k : ℕ} (arcs : Fin (k+1) → A) (hinj : Function.Injective arcs) (g : A → ℝ)
    (hg : ∀ a, a ∉ Set.range arcs → g a = 0) : ∑ a, g a = ∑ i, g (arcs i) := by
  have h1 : ∑ i, g (arcs i) = ∑ a ∈ Finset.univ.image arcs, g a :=
    (Finset.sum_image (fun i _ j _ h => hinj h)).symm
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  apply hg
  rintro ⟨i, rfl⟩
  exact ha (Finset.mem_image_of_mem _ (Finset.mem_univ _))

/-- sign of the `i`-th arc relative to the traversal. -/
def sg (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A) (i : Fin (k+1)) : ℝ :=
  if src (arcs i) = v i then 1 else -1

lemma sg_sq (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A) (i : Fin (k+1)) :
    sg src v arcs i * sg src v arcs i = 1 := by
  unfold sg; split_ifs <;> norm_num

lemma edge_ident (src dst : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (i : Fin (k+1)) (h : ({src (arcs i), dst (arcs i)} : Finset V) = {v i, v (i+1)}) (w : V) :
    ((if src (arcs i) = w then (1:ℝ) else 0) - (if dst (arcs i) = w then 1 else 0)) =
      sg src v arcs i * ((if v i = w then 1 else 0) - (if v (i+1) = w then 1 else 0)) := by
  unfold sg
  rcases pair_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, h1, h2]; ring
  · by_cases h3 : src (arcs i) = v i
    · have h4 : v (i+1) = v i := h1.symm.trans h3
      rw [if_pos h3, h1, h2, h4]; ring
    · rw [if_neg h3, h1, h2]; ring

/-- the signed indicator vector of a cycle. -/
noncomputable def cvec (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (a : A) : ℝ :=
  ∑ i, if arcs i = a then sg src v arcs i else 0

lemma cvec_arcs (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (hinj : Function.Injective arcs) (i : Fin (k+1)) : cvec src v arcs (arcs i) = sg src v arcs i := by
  unfold cvec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg (fun h => hj (hinj h))]
  · simp

lemma cvec_off (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (a : A) (ha : a ∉ Set.range arcs) : cvec src v arcs a = 0 := by
  unfold cvec
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  exact fun h => ha ⟨i, h⟩

lemma circuit_of_dc (src dst : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (hc : IsSimpleCycle src dst k v arcs) (hinj : Function.Injective arcs) :
    IsCircuit src dst (cvec src v arcs) := by
  refine ⟨?_, ?_, k, v, arcs, hc, ?_⟩
  · intro a
    by_cases ha : a ∈ Set.range arcs
    · obtain ⟨i, rfl⟩ := ha
      rw [cvec_arcs src v arcs hinj]; unfold sg; split_ifs <;> simp
    · right; left; exact cvec_off src v arcs a ha
  · intro w
    rw [bdry_eq, sum_cycle arcs hinj]
    · have : ∀ i, cvec src v arcs (arcs i) *
          ((if src (arcs i) = w then (1:ℝ) else 0) - (if dst (arcs i) = w then 1 else 0)) =
          (if v i = w then 1 else 0) - (if v (i+1) = w then 1 else 0) := by
        intro i
        rw [cvec_arcs src v arcs hinj, edge_ident src dst v arcs i (hc.2 i), ← mul_assoc,
          sg_sq, one_mul]
      simp_rw [this]
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact (Equiv.sum_comp (Equiv.addRight (1 : Fin (k+1)))
        (fun i => if v i = w then (1:ℝ) else 0)).symm
    · intro a ha; rw [cvec_off src v arcs a ha, zero_mul]
  · ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, SuppPosR,
      SuppNegR, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩
      rw [cvec_arcs src v arcs hinj]; unfold sg; split_ifs <;> norm_num
    · intro h
      by_contra h'
      rw [cvec_off src v arcs a (by rintro ⟨i, hi⟩; exact h' ⟨i, hi⟩)] at h
      simp at h

lemma cvec_pos_iff (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (hinj : Function.Injective arcs) (a : A) :
    0 < cvec src v arcs a ↔ ∃ i, arcs i = a ∧ src (arcs i) = v i := by
  constructor
  · intro h
    by_cases ha : a ∈ Set.range arcs
    · obtain ⟨i, rfl⟩ := ha
      rw [cvec_arcs src v arcs hinj] at h
      refine ⟨i, rfl, ?_⟩
      unfold sg at h; split_ifs at h with h1
      · exact h1
      · norm_num at h
    · rw [cvec_off src v arcs a ha] at h; exact absurd h (lt_irrefl _)
  · rintro ⟨i, rfl, hi⟩
    rw [cvec_arcs src v arcs hinj]; unfold sg; rw [if_pos hi]; norm_num

lemma cvec_neg_iff (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (hinj : Function.Injective arcs) (a : A) :
    cvec src v arcs a < 0 ↔ ∃ i, arcs i = a ∧ src (arcs i) ≠ v i := by
  constructor
  · intro h
    by_cases ha : a ∈ Set.range arcs
    · obtain ⟨i, rfl⟩ := ha
      rw [cvec_arcs src v arcs hinj] at h
      refine ⟨i, rfl, ?_⟩
      unfold sg at h; split_ifs at h with h1
      · norm_num at h
      · exact h1
    · rw [cvec_off src v arcs a ha] at h; exact absurd h (lt_irrefl _)
  · rintro ⟨i, rfl, hi⟩
    rw [cvec_arcs src v arcs hinj]; unfold sg; rw [if_neg hi]; norm_num

/-- consecutive-arc ratio from conservation. -/
lemma ratio (src dst : A → V) (pi : A → ℝ) (hbd : ∀ w, Boundary src dst pi w = 0)
    {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (hc : IsSimpleCycle src dst k v arcs) (hinj : Function.Injective arcs)
    (hoff : ∀ a, a ∉ Set.range arcs → pi a = 0) (i : Fin (k+1)) :
    pi (arcs (i+1)) * sg src v arcs (i+1) = pi (arcs i) * sg src v arcs i := by
  have h := hbd (v (i+1))
  rw [bdry_eq, sum_cycle arcs hinj] at h
  swap
  · intro a ha; rw [hoff a ha, zero_mul]
  simp_rw [edge_ident src dst v arcs _ (hc.2 _), hc.1.eq_iff, add_left_inj] at h
  simp_rw [← mul_assoc, mul_sub, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
  simp only [Finset.mem_univ, if_true] at h
  linarith

lemma loop_k0 (src dst : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (hc : IsSimpleCycle src dst k v arcs) (i : Fin (k+1)) (hl : src (arcs i) = dst (arcs i)) :
    k = 0 := by
  by_contra hk
  have h := hc.2 i
  rw [hl, Finset.pair_eq_singleton] at h
  have h1 : v i ∈ ({dst (arcs i)} : Finset V) := h ▸ by simp
  have h2 : v (i+1) ∈ ({dst (arcs i)} : Finset V) := h ▸ by simp
  simp only [Finset.mem_singleton] at h1 h2
  have := hc.1 (h1.trans h2.symm)
  have h3 : ((i + 1 : Fin (k+1))).val = i.val := by rw [← this]
  rw [Fin.val_add_one] at h3
  split_ifs at h3 with h4
  · have := Fin.ext_iff.mp h4; simp at this; omega
  · omega

lemma k0_sg (src dst : A → V) (v : Fin (0+1) → V) (arcs : Fin (0+1) → A)
    (hc : IsSimpleCycle src dst 0 v arcs) (i : Fin (0+1)) : sg src v arcs i = 1 := by
  unfold sg
  have h := hc.2 i
  have : (i + 1 : Fin (0+1)) = i := fin01 _ _
  rw [this, Finset.pair_eq_singleton] at h
  have h1 : src (arcs i) ∈ ({v i} : Finset V) := h ▸ by simp
  simp only [Finset.mem_singleton] at h1
  rw [if_pos h1]

/-- Structure of a circuit: an injective-arc simple cycle oriented along the circuit. -/
lemma dc_of_circuit (src dst : A → V) (pi : A → ℝ) (hpi : IsCircuit src dst pi) (s : A)
    (hs : pi s = 1) :
    ∃ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A), IsSimpleCycle src dst k v arcs ∧
      Function.Injective arcs ∧ (∀ i, pi (arcs i) = sg src v arcs i) ∧
      (∀ a, a ∉ Set.range arcs → pi a = 0) := by
  obtain ⟨hval, hbd, k, v, arcs, hc, himg⟩ := hpi
  have hmem : ∀ a, a ∈ Set.range arcs ↔ pi a ≠ 0 := by
    intro a
    have : a ∈ Finset.univ.image arcs ↔ a ∈ SuppPosR pi ∪ SuppNegR pi := by rw [himg]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, SuppPosR,
      SuppNegR, Finset.mem_filter] at this
    rw [Set.mem_range, this]
    constructor
    · rintro (h | h) <;> [exact ne_of_gt h; exact ne_of_lt h]
    · intro h; rcases lt_or_gt_of_ne h with h | h <;> [right; left] <;> exact h
  have hoff : ∀ a, a ∉ Set.range arcs → pi a = 0 := by
    intro a ha; by_contra h; exact ha ((hmem a).2 h)
  -- injectivity of arcs
  have hinj : Function.Injective arcs := by
    intro i j hij
    by_contra hne
    have h1 := hc.2 i
    rw [hij, hc.2 j] at h1
    rcases pair_cases h1 with ⟨h2, _⟩ | ⟨h2, h3⟩
    · exact hne (hc.1 h2).symm
    · have e1 := hc.1 h2
      have e2 := hc.1 h3
      -- j = i + 1, i = j + 1
      have ei : (i + 1 + 1 : Fin (k+1)) = i := by rw [← e1, e2]
      have hk : k = 1 ∨ k = 0 := by
        have := congrArg Fin.val ei
        have c1 := fin_succ_cases i
        have c2 := fin_succ_cases (i + 1)
        have hj := i.isLt
        omega
      rcases hk with rfl | rfl
      · -- k = 1: arcs i = arcs j, support is a single arc, boundary nonzero
        have hall : ∀ l : Fin (1+1), arcs l = arcs j := by
          intro l
          have hij' : i.val ≠ j.val := fun h => hne (Fin.ext h)
          have : l.val = i.val ∨ l.val = j.val := by
            have := l.isLt; have := i.isLt; have := j.isLt; omega
          rcases this with h | h
          · rw [Fin.ext h]; exact hij
          · rw [Fin.ext h]
        set a := arcs j
        have hnl : src a ≠ dst a := by
          intro hl; have := loop_k0 src dst v arcs hc j hl; omega
        have h := hbd (src a)
        rw [bdry_eq, Finset.sum_eq_single a] at h
        · simp only [if_true, if_neg (Ne.symm hnl)] at h
          have : pi a ≠ 0 := (hmem a).1 ⟨j, rfl⟩
          apply this; linarith
        · intro b _ hb
          rw [hoff b (by rintro ⟨l, rfl⟩; exact hb (hall l)), zero_mul]
        · simp
      · exact hne (fin01 _ _)
  -- constant ratio
  have hconst : ∀ m : ℕ, pi (arcs (m : Fin (k+1))) * sg src v arcs (m : Fin (k+1)) =
      pi (arcs 0) * sg src v arcs 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ, ratio src dst pi hbd v arcs hc hinj hoff, ih]
  have hconst' : ∀ i : Fin (k+1), pi (arcs i) * sg src v arcs i = pi (arcs 0) * sg src v arcs 0 := by
    intro i; have := hconst i.val; rwa [Fin.cast_val_eq_self] at this
  have hval0 : pi (arcs 0) = 1 ∨ pi (arcs 0) = -1 := by
    have := (hmem (arcs 0)).1 ⟨0, rfl⟩
    rcases hval (arcs 0) with h | h | h
    · left; exact h
    · exact absurd h this
    · right; exact h
  have hsg0 : sg src v arcs 0 = 1 ∨ sg src v arcs 0 = -1 := by
    unfold sg; split_ifs <;> simp
  by_cases hε : pi (arcs 0) * sg src v arcs 0 = 1
  · refine ⟨k, v, arcs, hc, hinj, fun i => ?_, hoff⟩
    have := hconst' i
    rw [hε] at this
    have h2 := sg_sq src v arcs i
    have : pi (arcs i) = pi (arcs i) * (sg src v arcs i * sg src v arcs i) := by rw [h2, mul_one]
    nlinarith
  · have hε' : pi (arcs 0) * sg src v arcs 0 = -1 := by
      have : pi (arcs 0) * sg src v arcs 0 = 1 ∨ pi (arcs 0) * sg src v arcs 0 = -1 := by
        rcases hval0 with h | h <;> rcases hsg0 with h' | h' <;> rw [h, h'] <;> norm_num
      exact this.resolve_left hε
    have hk : k ≠ 0 := by
      rintro rfl
      have h0 := k0_sg src dst v arcs hc 0
      have hs' : s ∈ Set.range arcs := (hmem s).2 (by rw [hs]; norm_num)
      obtain ⟨l, hl⟩ := hs'
      have : l = 0 := fin01 _ _
      subst this
      rw [h0, hl, hs] at hε'; norm_num at hε'
    -- reverse
    refine ⟨k, fun i => v (-i), fun i => arcs (-i - 1), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i j h; exact neg_injective (hc.1 h)
    · intro i
      have := hc.2 (-i - 1)
      rw [sub_add_cancel] at this
      rw [this, Finset.pair_comm]
      simp only [neg_add']
    · intro i j h; have := hinj h; simpa using this
    · intro i
      have h1 := hconst' (-i - 1)
      rw [hε'] at h1
      have hne : v (-i - 1) ≠ v (-i) := by
        intro h
        have := hc.1 h
        have h2 : (1 : Fin (k+1)) = 0 := sub_eq_self.mp this
        rw [Fin.one_eq_zero_iff] at h2
        exact hk (by omega)
      have hp := hc.2 (-i - 1)
      rw [sub_add_cancel] at hp
      unfold sg at h1 ⊢
      rcases pair_cases hp with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [if_pos h3] at h1
        rw [if_neg (by rw [h3]; exact hne)]
        linarith
      · rw [if_neg (by rw [h3]; exact hne.symm)] at h1
        rw [if_pos h3]
        linarith
    · intro a ha
      apply hoff
      rintro ⟨j, rfl⟩
      exact ha ⟨-j - 1, by simp⟩

end P225

namespace P225
open DiscreteConvex.CombinatorialC
open Fin.NatCast

variable {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]

lemma cyc_of_periodic (src dst : A → V) (F : V → V) (G : V → A) (x : V) (N : ℕ) (hN : 0 < N)
    (hper : F^[N] x = x)
    (hadj : ∀ m < N, ({src (G (F^[m] x)), dst (G (F^[m] x))} : Finset V) =
      {F^[m] x, F (F^[m] x)}) :
    ∃ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A), IsSimpleCycle src dst k v arcs ∧
      (∀ i : Fin (k+1), v i = F^[i.val] x ∧ arcs i = G (F^[i.val] x) ∧ i.val < N) ∧
      (∀ m, ∃ i : Fin (k+1), F^[m] x = v i) := by
  have hpp : Function.IsPeriodicPt F N x := hper
  have hp := hpp.minimalPeriod_pos hN
  have hpN := hpp.minimalPeriod_le hN
  obtain ⟨k, hk⟩ : ∃ k, Function.minimalPeriod F x = k + 1 := ⟨Function.minimalPeriod F x - 1, by omega⟩
  refine ⟨k, fun i => F^[i.val] x, fun i => G (F^[i.val] x), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j h
    have := Function.iterate_injOn_Iio_minimalPeriod (f := F) (x := x)
      (by rw [Set.mem_Iio, hk]; exact i.isLt) (by rw [Set.mem_Iio, hk]; exact j.isLt) h
    exact Fin.ext this
  · intro i
    have hnext : F^[(i+1 : Fin (k+1)).val] x = F (F^[i.val] x) := by
      rw [Fin.val_add_one]
      split_ifs with h
      · subst h
        have hmp := Function.iterate_minimalPeriod (f := F) (x := x)
        rw [hk, Function.iterate_succ_apply'] at hmp
        rw [Function.iterate_zero_apply, Fin.val_last, hmp]
      · rw [Function.iterate_succ_apply']
    simp only
    rw [hnext]
    exact hadj _ (by have := i.isLt; omega)
  · intro i; exact ⟨rfl, rfl, by have := i.isLt; omega⟩
  · intro m
    refine ⟨⟨m % (k+1), Nat.mod_lt _ (by omega)⟩, ?_⟩
    simp only
    rw [← hk, Function.iterate_mod_minimalPeriod_eq]

lemma step_core (src dst : A → V) (S : Finset A) {kg : ℕ} (vg : Fin (kg+1) → V)
    (ag : Fin (kg+1) → A)
    (hg : IsSimpleCycle src dst kg vg ag) (hgi : Function.Injective ag) (hkg : 1 ≤ kg)
    {kb : ℕ} (vb : Fin (kb+1) → V) (ab : Fin (kb+1) → A)
    (hb : IsSimpleCycle src dst kb vb ab) (hbi : Function.Injective ab)
    (j : Fin (kb+1)) (htS : ab j ∈ S) (htg : ab j ∉ Set.range ag) (htf : src (ab j) = vb j)
    (hx : vb 0 ∈ Set.range vg)
    (hoff : ∀ m : Fin (kb+1), 0 < m.val → m.val ≤ j.val → vb m ∉ Set.range vg)
    (hother : ∃ m : Fin (kb+1), 0 < m.val ∧ vb m ∈ Set.range vg)
    (hser : ∀ u ∈ S, u ≠ ab j → IsSeriesArcs src dst u (ab j))
    (hgS : ∀ i, ag i ∈ S → src (ag i) = vg i) :
    ∃ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A), IsSimpleCycle src dst k v arcs ∧
      Function.Injective arcs ∧
      (∀ i, (∃ i', arcs i = ag i' ∧ (src (arcs i) = v i ↔ src (ag i') = vg i')) ∨
            (∃ i', arcs i = ab i' ∧ (src (arcs i) = v i ↔ src (ab i') = vb i'))) ∧
      ab j ∈ Set.range arcs ∧ (∀ i, ag i ∈ S → ag i ∈ Set.range arcs) := by
  classical
  have hex : ∃ e : ℕ, 0 < e ∧ e < kb + 1 ∧ vb (e : Fin (kb+1)) ∈ Set.range vg := by
    obtain ⟨m, hm0, hm⟩ := hother
    exact ⟨m.val, hm0, m.isLt, by rwa [Fin.cast_val_eq_self]⟩
  obtain ⟨he0, heb, hey⟩ := Nat.find_spec hex
  have hemin' : ∀ m < Nat.find hex, ¬ (0 < m ∧ m < kb + 1 ∧ vb (m : Fin (kb+1)) ∈ Set.range vg) :=
    fun m hm => Nat.find_min hex hm
  set e := Nat.find hex with he_def
  have hemin : ∀ m, 0 < m → m < e → vb (m : Fin (kb+1)) ∉ Set.range vg := by
    intro m hm0 hme hm
    exact hemin' m hme ⟨hm0, by omega, hm⟩
  have hje : j.val < e := by
    by_contra hcon
    push_neg at hcon
    have hv := fin_natCast_val (k := kb) e heb
    exact hoff (e : Fin (kb+1)) (by rw [hv]; exact he0) (by rw [hv]; exact hcon) hey
  obtain ⟨b, hbx⟩ := hx
  obtain ⟨a, hay⟩ := hey
  have hab : a.val ≠ b.val := by
    intro h
    rw [Fin.ext h, hbx] at hay
    have h2 := hb.1 hay
    have := congrArg Fin.val h2
    rw [Fin.val_zero, fin_natCast_val e heb] at this
    omega
  have ha := a.isLt
  have hb' := b.isLt
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (if a.val ≤ b.val then b.val - a.val else b.val + (kg+1) - a.val) :=
    ⟨_, rfl⟩
  obtain ⟨L', hL'⟩ : ∃ L' : ℕ, L' = (if b.val ≤ a.val then a.val - b.val else a.val + (kg+1) - b.val) :=
    ⟨_, rfl⟩
  have hLc : (a.val ≤ b.val ∧ L = b.val - a.val) ∨ (b.val < a.val ∧ L = b.val + (kg+1) - a.val) := by
    split_ifs at hL <;> omega
  have hL'c : (b.val ≤ a.val ∧ L' = a.val - b.val) ∨ (a.val < b.val ∧ L' = a.val + (kg+1) - b.val) := by
    split_ifs at hL' <;> omega
  have hLlt : L < kg + 1 := by omega
  have hL'lt : L' < kg + 1 := by omega
  have haL : ∀ m, m < kg+1 → (a + (m : Fin (kg+1)) = b ↔ m = L) := by
    intro m hm
    rw [Fin.ext_iff, fin_add_nat a m hm]
    split_ifs <;> omega
  have haL' : ∀ m, m < kg+1 → (a - (m : Fin (kg+1)) = b ↔ m = L') := by
    intro m hm
    rw [Fin.ext_iff, fin_sub_nat a m hm]
    split_ifs <;> omega
  set x := vb 0 with hxdef
  let gi := Function.invFun vg
  let bi := Function.invFun vb
  have hgi' : ∀ i, gi (vg i) = i := Function.leftInverse_invFun hg.1
  have hbi' : ∀ i, bi (vb i) = i := Function.leftInverse_invFun hb.1
  let isG : V → Prop := fun w => w ∈ Set.range vg ∧ w ≠ x
  let F : V → V := fun w => if isG w then vg (gi w + 1) else vb (bi w + 1)
  let G : V → A := fun w => if isG w then ag (gi w) else ab (bi w)
  let F' : V → V := fun w => if isG w then vg (gi w - 1) else vb (bi w + 1)
  let G' : V → A := fun w => if isG w then ag (gi w - 1) else ab (bi w)
  have hnotG_b : ∀ m, m < e → ¬ isG (vb (m : Fin (kb+1))) := by
    rintro m hm ⟨hr, hne⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hne (by rw [Nat.cast_zero])
    · exact hemin m hm0 hm hr
  have hG_g : ∀ m, m < L → isG (vg (a + (m : Fin (kg+1)))) := by
    intro m hm
    refine ⟨⟨_, rfl⟩, fun h => ?_⟩
    rw [← hbx] at h
    have := (haL m (by omega)).1 (hg.1 h)
    omega
  have hG_g' : ∀ m, m < L' → isG (vg (a - (m : Fin (kg+1)))) := by
    intro m hm
    refine ⟨⟨_, rfl⟩, fun h => ?_⟩
    rw [← hbx] at h
    have := (haL' m (by omega)).1 (hg.1 h)
    omega
  have hR : ∀ m, m ≤ e → F^[m] x = vb (m : Fin (kb+1)) := by
    intro m hm
    induction m with
    | zero => rw [Function.iterate_zero_apply, Nat.cast_zero]
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      dsimp only [F]
      rw [if_neg (hnotG_b m (by omega)), hbi', Nat.cast_succ]
  have hR' : ∀ m, m ≤ e → F'^[m] x = vb (m : Fin (kb+1)) := by
    intro m hm
    induction m with
    | zero => rw [Function.iterate_zero_apply, Nat.cast_zero]
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      dsimp only [F']
      rw [if_neg (hnotG_b m (by omega)), hbi', Nat.cast_succ]
  have hC : ∀ m, m ≤ L → F^[e + m] x = vg (a + (m : Fin (kg+1))) := by
    intro m hm
    induction m with
    | zero => rw [Nat.add_zero, hR e le_rfl, Nat.cast_zero, add_zero, hay]
    | succ m ih =>
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega)]
      dsimp only [F]
      rw [if_pos (hG_g m (by omega)), hgi', Nat.cast_succ, add_assoc]
  have hC' : ∀ m, m ≤ L' → F'^[e + m] x = vg (a - (m : Fin (kg+1))) := by
    intro m hm
    induction m with
    | zero => rw [Nat.add_zero, hR' e le_rfl, Nat.cast_zero, sub_zero, hay]
    | succ m ih =>
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega)]
      dsimp only [F']
      rw [if_pos (hG_g' m (by omega)), hgi', Nat.cast_succ, sub_add_eq_sub_sub]
  have hper : F^[e + L] x = x := by rw [hC L le_rfl, (haL L hLlt).2 rfl, hbx]
  have hper' : F'^[e + L'] x = x := by rw [hC' L' le_rfl, (haL' L' hL'lt).2 rfl, hbx]
  have hdesc : ∀ m, m < e + L → (m < e ∧ F^[m] x = vb (m : Fin (kb+1))) ∨
      (∃ p, p < L ∧ m = e + p ∧ F^[m] x = vg (a + (p : Fin (kg+1)))) := by
    intro m hm
    by_cases h : m < e
    · left; exact ⟨h, hR m h.le⟩
    · right
      refine ⟨m - e, by omega, by omega, ?_⟩
      rw [← hC (m - e) (by omega), show e + (m - e) = m by omega]
  have hdesc' : ∀ m, m < e + L' → (m < e ∧ F'^[m] x = vb (m : Fin (kb+1))) ∨
      (∃ p, p < L' ∧ m = e + p ∧ F'^[m] x = vg (a - (p : Fin (kg+1)))) := by
    intro m hm
    by_cases h : m < e
    · left; exact ⟨h, hR' m h.le⟩
    · right
      refine ⟨m - e, by omega, by omega, ?_⟩
      rw [← hC' (m - e) (by omega), show e + (m - e) = m by omega]
  have hadj : ∀ m < e + L, ({src (G (F^[m] x)), dst (G (F^[m] x))} : Finset V) =
      {F^[m] x, F (F^[m] x)} := by
    intro m hm
    rcases hdesc m hm with ⟨hme, hFm⟩ | ⟨p, hp, rfl, hFm⟩
    · rw [hFm]; dsimp only [F, G]
      rw [if_neg (hnotG_b m hme), if_neg (hnotG_b m hme), hbi']
      exact hb.2 _
    · rw [hFm]; dsimp only [F, G]
      rw [if_pos (hG_g p hp), if_pos (hG_g p hp), hgi']
      exact hg.2 _
  have hadj' : ∀ m < e + L', ({src (G' (F'^[m] x)), dst (G' (F'^[m] x))} : Finset V) =
      {F'^[m] x, F' (F'^[m] x)} := by
    intro m hm
    rcases hdesc' m hm with ⟨hme, hFm⟩ | ⟨p, hp, rfl, hFm⟩
    · rw [hFm]; dsimp only [F', G']
      rw [if_neg (hnotG_b m hme), if_neg (hnotG_b m hme), hbi']
      exact hb.2 _
    · rw [hFm]; dsimp only [F', G']
      rw [if_pos (hG_g' p hp), if_pos (hG_g' p hp), hgi', hg.2, sub_add_cancel, Finset.pair_comm]
  obtain ⟨k, v, arcs, hc, hvdef, hall⟩ :=
    cyc_of_periodic src dst F G x (e + L) (by omega) hper hadj
  obtain ⟨k', v', arcs', hc', hvdef', hall'⟩ :=
    cyc_of_periodic src dst F' G' x (e + L') (by omega) hper' hadj'
  have hend : ∀ m i, ab m = ag i → vb m ∈ Set.range vg ∧ vb (m+1) ∈ Set.range vg := by
    intro m i h
    have h1 := hb.2 m
    rw [h, hg.2 i] at h1
    have p1 : vb m ∈ ({vg i, vg (i+1)} : Finset V) := h1 ▸ by simp
    have p2 : vb (m+1) ∈ ({vg i, vg (i+1)} : Finset V) := h1 ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at p1 p2
    exact ⟨by rcases p1 with h | h <;> exact ⟨_, h.symm⟩,
      by rcases p2 with h | h <;> exact ⟨_, h.symm⟩⟩
  have hRarc : ∀ m, m < e → ab (m : Fin (kb+1)) ∉ Set.range ag := by
    rintro m hm ⟨i, hi⟩
    by_cases hmj : m = j.val
    · subst hmj; rw [Fin.cast_val_eq_self] at hi; exact htg ⟨i, hi⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have h2 := (hend _ i hi.symm).2
        rw [Nat.cast_zero, zero_add] at h2
        have hj1 : 1 ≤ j.val := by omega
        have hkb : 1 < kb + 1 := by have := j.isLt; omega
        apply hoff ((1:ℕ) : Fin (kb+1)) (by rw [fin_natCast_val 1 hkb]; omega)
          (by rw [fin_natCast_val 1 hkb]; omega)
        rw [Nat.cast_one]; exact h2
      · exact hemin m hm0 hm (hend _ i hi.symm).1
  have hGinj : ∀ m1 m2, m1 < e + L → m2 < e + L → G (F^[m1] x) = G (F^[m2] x) →
      F^[m1] x = F^[m2] x := by
    intro m1 m2 h1 h2 h
    rcases hdesc m1 h1 with ⟨hm1, hF1⟩ | ⟨p1, hp1, rfl, hF1⟩ <;>
    rcases hdesc m2 h2 with ⟨hm2, hF2⟩ | ⟨p2, hp2, rfl, hF2⟩
    · rw [hF1, hF2] at h; rw [hF1, hF2]; dsimp only [G] at h
      rw [if_neg (hnotG_b _ hm1), if_neg (hnotG_b _ hm2), hbi', hbi'] at h
      rw [hbi h]
    · rw [hF1, hF2] at h; dsimp only [G] at h
      rw [if_neg (hnotG_b _ hm1), if_pos (hG_g _ hp2), hbi', hgi'] at h
      exact absurd ⟨_, h.symm⟩ (hRarc _ hm1)
    · rw [hF1, hF2] at h; dsimp only [G] at h
      rw [if_pos (hG_g _ hp1), if_neg (hnotG_b _ hm2), hbi', hgi'] at h
      exact absurd ⟨_, h⟩ (hRarc _ hm2)
    · rw [hF1, hF2] at h; rw [hF1, hF2]; dsimp only [G] at h
      rw [if_pos (hG_g _ hp1), if_pos (hG_g _ hp2), hgi', hgi'] at h
      rw [hgi h]
  have hinj : Function.Injective arcs := by
    intro i1 i2 h
    obtain ⟨hv1, ha1, hl1⟩ := hvdef i1
    obtain ⟨hv2, ha2, hl2⟩ := hvdef i2
    rw [ha1, ha2] at h
    apply hc.1
    rw [hv1, hv2]
    exact hGinj _ _ hl1 hl2 h
  have horig : ∀ i, (∃ i', arcs i = ag i' ∧ (src (arcs i) = v i ↔ src (ag i') = vg i')) ∨
      (∃ i', arcs i = ab i' ∧ (src (arcs i) = v i ↔ src (ab i') = vb i')) := by
    intro i
    obtain ⟨hv, ha, hl⟩ := hvdef i
    rcases hdesc _ hl with ⟨hm, hF⟩ | ⟨p, hp, _, hF⟩
    · right
      have hai : arcs i = ab ((i.val : ℕ) : Fin (kb+1)) := by
        rw [ha, hF]; dsimp only [G]; rw [if_neg (hnotG_b _ hm), hbi']
      refine ⟨_, hai, ?_⟩
      rw [hai, hv, hF]
    · left
      have hai : arcs i = ag (a + (p : Fin (kg+1))) := by
        rw [ha, hF]; dsimp only [G]; rw [if_pos (hG_g _ hp), hgi']
      refine ⟨_, hai, ?_⟩
      rw [hai, hv, hF]
  have ht : ab j ∈ Set.range arcs := by
    obtain ⟨i, hi⟩ := hall j.val
    refine ⟨i, ?_⟩
    obtain ⟨hv, ha, _⟩ := hvdef i
    rw [ha, ← hv, ← hi, hR j.val hje.le]
    dsimp only [G]; rw [if_neg (hnotG_b _ hje), hbi', Fin.cast_val_eq_self]
  refine ⟨k, v, arcs, hc, hinj, horig, ht, ?_⟩
  intro i hiS
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = (if a.val ≤ i.val then i.val - a.val else i.val + (kg+1) - a.val) :=
    ⟨_, rfl⟩
  have hi := i.isLt
  have hpc : (a.val ≤ i.val ∧ p = i.val - a.val) ∨ (i.val < a.val ∧ p = i.val + (kg+1) - a.val) := by
    split_ifs at hp <;> omega
  have hpl : p < kg + 1 := by omega
  have hap : a + (p : Fin (kg+1)) = i := by
    ext; rw [fin_add_nat a p hpl]; split_ifs <;> omega
  by_cases hpL : p < L
  · obtain ⟨i0, hi0⟩ := hall (e + p)
    refine ⟨i0, ?_⟩
    obtain ⟨hv, ha, _⟩ := hvdef i0
    rw [ha, ← hv, ← hi0, hC p hpL.le]
    dsimp only [G]; rw [if_pos (hG_g p hpL), hgi', hap]
  · exfalso
    have hipc := fin_succ_cases i
    set ip := i + 1 with hip
    have hipl := ip.isLt
    obtain ⟨q, hq⟩ : ∃ q : ℕ, q = (if ip.val ≤ a.val then a.val - ip.val else a.val + (kg+1) - ip.val) :=
      ⟨_, rfl⟩
    have hqc : (ip.val ≤ a.val ∧ q = a.val - ip.val) ∨ (a.val < ip.val ∧ q = a.val + (kg+1) - ip.val) := by
      split_ifs at hq <;> omega
    have hql : q < kg + 1 := by omega
    have haq : a - (q : Fin (kg+1)) = ip := by
      ext; rw [fin_sub_nat a q hql]; split_ifs <;> omega
    have hqL : q < L' := by omega
    obtain ⟨iu, hiu⟩ := hall' (e + q)
    obtain ⟨it, hit⟩ := hall' j.val
    obtain ⟨hvu, hau, _⟩ := hvdef' iu
    obtain ⟨hvt, hat, _⟩ := hvdef' it
    have hu : arcs' iu = ag i := by
      rw [hau, ← hvu, ← hiu, hC' q hqL.le]
      dsimp only [G']; rw [if_pos (hG_g' q hqL), hgi', haq, hip, add_sub_cancel_right]
    have hfu : ¬ (src (arcs' iu) = v' iu) := by
      rw [hu, ← hiu, hC' q hqL.le, haq, hgS i hiS]
      intro h
      have := congrArg Fin.val (hg.1 h)
      omega
    have htv : arcs' it = ab j := by
      rw [hat, ← hvt, ← hit, hR' j.val hje.le]
      dsimp only [G']; rw [if_neg (hnotG_b _ hje), hbi', Fin.cast_val_eq_self]
    have hft : src (arcs' it) = v' it := by
      rw [htv, ← hit, hR' j.val hje.le, Fin.cast_val_eq_self, htf]
    have hne : ag i ≠ ab j := fun h => htg ⟨i, h⟩
    have := hser (ag i) hiS hne k' v' arcs' hc' iu it hu htv
    exact hfu (this.2 hft)

end P225

namespace P225
open DiscreteConvex.CombinatorialC
open Fin.NatCast

variable {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]

lemma k0_loop (src dst : A → V) (v : Fin (0+1) → V) (arcs : Fin (0+1) → A)
    (hc : IsSimpleCycle src dst 0 v arcs) (i : Fin (0+1)) : src (arcs i) = dst (arcs i) := by
  have h := hc.2 i
  have : (i + 1 : Fin (0+1)) = i := fin01 _ _
  rw [this, Finset.pair_eq_singleton] at h
  have h1 : src (arcs i) ∈ ({v i} : Finset V) := h ▸ by simp
  have h2 : dst (arcs i) ∈ ({v i} : Finset V) := h ▸ by simp
  simp only [Finset.mem_singleton] at h1 h2
  rw [h1, h2]

lemma ends_mem (src dst : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A)
    (hc : IsSimpleCycle src dst k v arcs) (i : Fin (k+1)) :
    src (arcs i) ∈ Set.range v ∧ dst (arcs i) ∈ Set.range v := by
  have h := hc.2 i
  have h1 : src (arcs i) ∈ ({v i, v (i+1)} : Finset V) := h ▸ by simp
  have h2 : dst (arcs i) ∈ ({v i, v (i+1)} : Finset V) := h ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  exact ⟨by rcases h1 with h | h <;> exact ⟨_, h.symm⟩, by rcases h2 with h | h <;> exact ⟨_, h.symm⟩⟩

lemma step (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S)
    {kg : ℕ} (vg : Fin (kg+1) → V) (ag : Fin (kg+1) → A)
    (hg : IsSimpleCycle src dst kg vg ag) (hgi : Function.Injective ag)
    {kb : ℕ} (vb : Fin (kb+1) → V) (ab : Fin (kb+1) → A)
    (hb : IsSimpleCycle src dst kb vb ab) (hbi : Function.Injective ab)
    (s : A) (hsl : src s ≠ dst s) (hsg : s ∈ Set.range ag) (hsb : s ∈ Set.range ab)
    (j0 : Fin (kb+1)) (htS : ab j0 ∈ S) (htg : ab j0 ∉ Set.range ag) (htf : src (ab j0) = vb j0)
    (hgS : ∀ i, ag i ∈ S → src (ag i) = vg i) :
    ∃ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A), IsSimpleCycle src dst k v arcs ∧
      Function.Injective arcs ∧
      (∀ i, (∃ i', arcs i = ag i' ∧ (src (arcs i) = v i ↔ src (ag i') = vg i')) ∨
            (∃ i', arcs i = ab i' ∧ (src (arcs i) = v i ↔ src (ab i') = vb i'))) ∧
      ab j0 ∈ Set.range arcs ∧ (∀ i, ag i ∈ S → ag i ∈ Set.range arcs) := by
  classical
  obtain ⟨is, his⟩ := hsg
  have hkg : 1 ≤ kg := by
    rcases Nat.eq_zero_or_pos kg with h | h
    · subst h; exact absurd (his ▸ k0_loop src dst vg ag hg is) hsl
    · exact h
  obtain ⟨hsrc_g, hdst_g⟩ := ends_mem src dst vg ag hg is
  rw [his] at hsrc_g hdst_g
  obtain ⟨ib, hib⟩ := hsb
  obtain ⟨hsrc_b, hdst_b⟩ := ends_mem src dst vb ab hb ib
  rw [hib] at hsrc_b hdst_b
  have hexd : ∃ d : ℕ, d ≤ kb ∧ vb (j0 - (d : Fin (kb+1))) ∈ Set.range vg := by
    obtain ⟨c, hc⟩ := hsrc_b
    refine ⟨(j0 - c).val, by have := (j0 - c).isLt; omega, ?_⟩
    rw [Fin.cast_val_eq_self, sub_sub_cancel, hc]; exact hsrc_g
  obtain ⟨hdk, hdR⟩ := Nat.find_spec hexd
  have hdmin : ∀ m < Nat.find hexd, ¬ (m ≤ kb ∧ vb (j0 - (m : Fin (kb+1))) ∈ Set.range vg) :=
    fun m hm => Nat.find_min hexd hm
  set d := Nat.find hexd with hd_def
  set c : Fin (kb+1) := j0 - (d : Fin (kb+1)) with hc_def
  have hdv : ((d : Fin (kb+1))).val = d := fin_natCast_val d (by omega)
  have hrot : IsSimpleCycle src dst kb (fun i => vb (i + c)) (fun i => ab (i + c)) := by
    refine ⟨fun i j h => add_right_cancel (hb.1 h), fun i => ?_⟩
    simp only
    rw [hb.2 (i + c), add_right_comm]
  have hroti : Function.Injective (fun i => ab (i + c)) := fun i j h => add_right_cancel (hbi h)
  have hjt : ab ((d : Fin (kb+1)) + c) = ab j0 := by rw [hc_def, add_sub_cancel]
  have hjv : vb ((d : Fin (kb+1)) + c) = vb j0 := by rw [hc_def, add_sub_cancel]
  obtain ⟨k, v, arcs, hc', hinj, horig, ht, hSg⟩ := step_core src dst S vg ag hg hgi hkg
    (fun i => vb (i + c)) (fun i => ab (i + c)) hrot hroti (d : Fin (kb+1))
    (by rw [hjt]; exact htS) (by rw [hjt]; exact htg)
    (by rw [hjt, hjv]; exact htf)
    (by rw [zero_add]; exact hdR)
    (by
      intro m hm0 hmd
      rw [hdv] at hmd
      have h1 : m + c = j0 - (((d - m.val : ℕ)) : Fin (kb+1)) := by
        have h2 : (((d - m.val : ℕ) : Fin (kb+1)) + ((m.val : ℕ) : Fin (kb+1))) =
            (d : Fin (kb+1)) := by rw [← Nat.cast_add, Nat.sub_add_cancel hmd]
        rw [Fin.cast_val_eq_self] at h2
        rw [eq_sub_iff_add_eq, hc_def, ← h2]; abel
      rw [h1]
      intro hm
      exact hdmin (d - m.val) (by omega) ⟨by omega, hm⟩)
    (by
      have hne : ∀ w, w ∈ Set.range vb → ∃ m : Fin (kb+1), vb (m + c) = w := by
        rintro w ⟨c', rfl⟩; exact ⟨c' - c, by rw [sub_add_cancel]⟩
      by_cases h0 : src s = vb (0 + c)
      · obtain ⟨m, hm⟩ := hne _ hdst_b
        refine ⟨m, ?_, by rw [hm]; exact hdst_g⟩
        rcases Nat.eq_zero_or_pos m.val with h | h
        · exfalso; apply hsl
          rw [h0, ← hm, show m = 0 from Fin.ext h]
        · exact h
      · obtain ⟨m, hm⟩ := hne _ hsrc_b
        refine ⟨m, ?_, by rw [hm]; exact hsrc_g⟩
        rcases Nat.eq_zero_or_pos m.val with h | h
        · exfalso; apply h0
          rw [← hm, show m = 0 from Fin.ext h]
        · exact h)
    (by
      intro u hu hne
      rw [hjt] at hne ⊢
      exact hS u hu (ab j0) htS hne)
    hgS
  refine ⟨k, v, arcs, hc', hinj, fun i => ?_, by simpa only [hjt] using ht, hSg⟩
  rcases horig i with h | ⟨i', h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨i' + c, h1, h2⟩

lemma mem_pos {W : Type*} [Fintype W] [DecidableEq W] (x : W → ℝ) (a : W) :
    a ∈ SuppPosR x ↔ 0 < x a := by simp [SuppPosR]

lemma mem_neg {W : Type*} [Fintype W] [DecidableEq W] (x : W → ℝ) (a : W) :
    a ∈ SuppNegR x ↔ x a < 0 := by simp [SuppNegR]

lemma sg_pos_iff (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A) (i : Fin (k+1)) :
    0 < sg src v arcs i ↔ src (arcs i) = v i := by
  unfold sg; split_ifs with h <;> simp [h]

lemma sg_one (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A) (i : Fin (k+1))
    (h : src (arcs i) = v i) : sg src v arcs i = 1 := by
  unfold sg; rw [if_pos h]

lemma sg_neg_one (src : A → V) {k : ℕ} (v : Fin (k+1) → V) (arcs : Fin (k+1) → A) (i : Fin (k+1))
    (h : src (arcs i) ≠ v i) : sg src v arcs i = -1 := by
  unfold sg; rw [if_neg h]

def Good (src dst : A → V) (P N : Finset A) (R : Set A) (s : A) {k : ℕ} (v : Fin (k+1) → V)
    (arcs : Fin (k+1) → A) : Prop :=
  IsSimpleCycle src dst k v arcs ∧ Function.Injective arcs ∧
    (∀ i, (src (arcs i) = v i → arcs i ∈ P) ∧ (src (arcs i) ≠ v i → arcs i ∈ N)) ∧
    (∀ i, arcs i ∈ R) ∧ s ∈ Set.range arcs

theorem main_thm (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S)
    (pi1 pi2 : A → ℝ) (hpi1 : IsCircuit src dst pi1) (hpi2 : IsCircuit src dst pi2)
    (hne : (SuppPosR pi1 ∩ SuppPosR pi2 ∩ S).Nonempty) :
    ∃ pi : A → ℝ, IsCircuit src dst pi ∧ SuppPosR pi ⊆ SuppPosR pi1 ∪ SuppPosR pi2 ∧
      SuppNegR pi ⊆ SuppNegR pi1 ∪ SuppNegR pi2 ∧
      SuppPosR pi ∩ S = (SuppPosR pi1 ∪ SuppPosR pi2) ∩ S := by
  classical
  obtain ⟨s, hs⟩ := hne
  simp only [Finset.mem_inter, mem_pos] at hs
  obtain ⟨⟨hs1, hs2⟩, hsS⟩ := hs
  have val1 : ∀ pi : A → ℝ, IsCircuit src dst pi → 0 < pi s → pi s = 1 := by
    intro pi h hp
    rcases h.1 s with h' | h' | h'
    · exact h'
    · rw [h'] at hp; exact absurd hp (lt_irrefl _)
    · rw [h'] at hp; norm_num at hp
  obtain ⟨k1, v1, a1, hc1, hi1, hsg1, hoff1⟩ := dc_of_circuit src dst pi1 hpi1 s (val1 _ hpi1 hs1)
  obtain ⟨k2, v2, a2, hc2, hi2, hsg2, hoff2⟩ := dc_of_circuit src dst pi2 hpi2 s (val1 _ hpi2 hs2)
  have fact : ∀ (pi : A → ℝ) (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A),
      IsSimpleCycle src dst k v arcs → (∀ i, pi (arcs i) = sg src v arcs i) →
      (∀ a, a ∉ Set.range arcs → pi a = 0) → 0 < pi s →
      (∀ a, a ∈ Set.range arcs ↔ pi a ≠ 0) ∧ (∀ a ∈ S, pi a ≠ 0 → pi a = 1) ∧
      (∀ i, (src (arcs i) = v i → 0 < pi (arcs i)) ∧ (src (arcs i) ≠ v i → pi (arcs i) < 0)) := by
    intro pi k v arcs hc hsg hoff hps
    have hmem : ∀ a, a ∈ Set.range arcs ↔ pi a ≠ 0 := by
      intro a; constructor
      · rintro ⟨i, rfl⟩; rw [hsg]; unfold sg; split_ifs <;> norm_num
      · intro h; by_contra h'; exact h (hoff a h')
    refine ⟨hmem, ?_, ?_⟩
    · intro a ha hpa
      obtain ⟨i, rfl⟩ := (hmem a).2 hpa
      obtain ⟨i0, hi0⟩ := (hmem s).2 (ne_of_gt hps)
      have hf0 : src (arcs i0) = v i0 := by rw [← sg_pos_iff, ← hsg, hi0]; exact hps
      by_cases has : arcs i = s
      · rw [has, ← hi0, hsg, sg_one src v arcs i0 hf0]
      · have := hS (arcs i) ha s hsS has k v arcs hc i i0 rfl hi0
        rw [hsg, sg_one src v arcs i (this.2 hf0)]
    · intro i
      rw [hsg]
      exact ⟨fun h => by rw [sg_one src v arcs i h]; norm_num,
        fun h => by rw [sg_neg_one src v arcs i h]; norm_num⟩
  obtain ⟨hm1, hS1, hd1⟩ := fact pi1 k1 v1 a1 hc1 hsg1 hoff1 hs1
  obtain ⟨hm2, hS2, hd2⟩ := fact pi2 k2 v2 a2 hc2 hsg2 hoff2 hs2
  set P := SuppPosR pi1 ∪ SuppPosR pi2 with hP
  set N := SuppNegR pi1 ∪ SuppNegR pi2 with hN
  set R : Set A := Set.range a1 ∪ Set.range a2 with hR
  have hSN : ∀ a ∈ S, a ∉ N := by
    intro a ha hn
    rw [hN, Finset.mem_union, mem_neg, mem_neg] at hn
    rcases hn with h | h
    · have := hS1 a ha (ne_of_lt h); linarith
    · have := hS2 a ha (ne_of_lt h); linarith
  -- finishing from a good cycle containing P ∩ S
  have finish : ∀ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A),
      Good src dst P N R s v arcs → (∀ a ∈ P ∩ S, a ∈ Set.range arcs) →
      ∃ pi : A → ℝ, IsCircuit src dst pi ∧ SuppPosR pi ⊆ P ∧ SuppNegR pi ⊆ N ∧
        SuppPosR pi ∩ S = P ∩ S := by
    intro k v arcs hG hT
    obtain ⟨hc, hinj, hconf, _, _⟩ := hG
    have hpos : SuppPosR (cvec src v arcs) ⊆ P := by
      intro a ha
      rw [mem_pos, cvec_pos_iff src v arcs hinj] at ha
      obtain ⟨i, rfl, hf⟩ := ha
      exact (hconf i).1 hf
    refine ⟨cvec src v arcs, circuit_of_dc src dst v arcs hc hinj, hpos, ?_, ?_⟩
    · intro a ha
      rw [mem_neg, cvec_neg_iff src v arcs hinj] at ha
      obtain ⟨i, rfl, hf⟩ := ha
      exact (hconf i).2 hf
    · ext a
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨hpos h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        obtain ⟨i, rfl⟩ := hT a (Finset.mem_inter.2 ⟨h1, h2⟩)
        rw [mem_pos, cvec_pos_iff src v arcs hinj]
        refine ⟨i, rfl, ?_⟩
        by_contra hf
        exact hSN _ h2 ((hconf i).2 hf)
  have good1 : Good src dst P N R s v1 a1 := by
    refine ⟨hc1, hi1, fun i => ⟨fun h => ?_, fun h => ?_⟩, fun i => Or.inl ⟨i, rfl⟩,
      (hm1 s).2 (ne_of_gt hs1)⟩
    · rw [hP, Finset.mem_union, mem_pos]; exact Or.inl ((hd1 i).1 h)
    · rw [hN, Finset.mem_union, mem_neg]; exact Or.inl ((hd1 i).2 h)
  have good2 : Good src dst P N R s v2 a2 := by
    refine ⟨hc2, hi2, fun i => ⟨fun h => ?_, fun h => ?_⟩, fun i => Or.inr ⟨i, rfl⟩,
      (hm2 s).2 (ne_of_gt hs2)⟩
    · rw [hP, Finset.mem_union, mem_pos, mem_pos]; exact Or.inr ((hd2 i).1 h)
    · rw [hN, Finset.mem_union, mem_neg, mem_neg]; exact Or.inr ((hd2 i).2 h)
  have hPR : ∀ a ∈ P, a ∈ R := by
    intro a ha
    rw [hP, Finset.mem_union, mem_pos, mem_pos] at ha
    rcases ha with h | h
    · exact Or.inl ((hm1 a).2 (ne_of_gt h))
    · exact Or.inr ((hm2 a).2 (ne_of_gt h))
  by_cases hsl : src s = dst s
  · apply finish k1 v1 a1 good1
    have hk0 : ∀ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A),
        IsSimpleCycle src dst k v arcs → s ∈ Set.range arcs → ∀ a ∈ Set.range arcs, a = s := by
      rintro k v arcs hc ⟨i0, hi0⟩ a ⟨i, rfl⟩
      have := loop_k0 src dst v arcs hc i0 (by rw [hi0]; exact hsl)
      subst this
      rw [← hi0, fin01 i i0]
    intro a ha
    have hs' : s ∈ Set.range a1 := (hm1 s).2 (ne_of_gt hs1)
    rcases hPR a (Finset.mem_inter.1 ha).1 with h | h
    · exact h
    · rw [hk0 k2 v2 a2 hc2 ((hm2 s).2 (ne_of_gt hs2)) a h]; exact hs'
  have key : ∀ n : ℕ, ∀ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A),
      Good src dst P N R s v arcs →
      ((P ∩ S).filter (fun a => a ∉ Set.range arcs)).card ≤ n →
      ∃ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A),
        Good src dst P N R s v arcs ∧ ∀ a ∈ P ∩ S, a ∈ Set.range arcs := by
    intro n
    induction n with
    | zero =>
      intro k v arcs hG hn
      refine ⟨k, v, arcs, hG, fun a ha => ?_⟩
      by_contra h
      have hmem : a ∈ (P ∩ S).filter (fun a => a ∉ Set.range arcs) := Finset.mem_filter.2 ⟨ha, h⟩
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hn)] at hmem
      simp at hmem
    | succ n ih =>
      intro k v arcs hG hn
      by_cases hall : ∀ a ∈ P ∩ S, a ∈ Set.range arcs
      · exact ⟨k, v, arcs, hG, hall⟩
      push_neg at hall
      obtain ⟨t, htT, htn⟩ := hall
      obtain ⟨htP, htS⟩ := Finset.mem_inter.1 htT
      have hβ : ∃ (kb : ℕ) (vb : Fin (kb+1) → V) (ab : Fin (kb+1) → A),
          Good src dst P N R s vb ab ∧ t ∈ Set.range ab := by
        rcases hPR t htP with h | h
        · exact ⟨k1, v1, a1, good1, h⟩
        · exact ⟨k2, v2, a2, good2, h⟩
      obtain ⟨kb, vb, ab, hGb, j0, hj0⟩ := hβ
      obtain ⟨hc, hinj, hconf, hRg, hsg⟩ := hG
      obtain ⟨hcb, hinjb, hconfb, hRb, hsb⟩ := hGb
      have hfwd : ∀ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A),
          (∀ i, (src (arcs i) = v i → arcs i ∈ P) ∧ (src (arcs i) ≠ v i → arcs i ∈ N)) →
          ∀ i, arcs i ∈ S → src (arcs i) = v i := by
        intro k v arcs hcf i hi
        by_contra hf
        exact hSN _ hi ((hcf i).2 hf)
      obtain ⟨k', v', arcs', hc', hinj', horig, ht', hS'⟩ :=
        step src dst S hS v arcs hc hinj vb ab hcb hinjb s hsl hsg hsb j0
          (by rw [hj0]; exact htS) (by rw [hj0]; exact htn)
          (hfwd kb vb ab hconfb j0 (by rw [hj0]; exact htS)) (hfwd k v arcs hconf)
      apply ih k' v' arcs'
      · refine ⟨hc', hinj', fun i => ?_, fun i => ?_, ?_⟩
        · rcases horig i with ⟨i', h1, h2⟩ | ⟨i', h1, h2⟩
          · rw [ne_eq, h2, h1]; exact hconf i'
          · rw [ne_eq, h2, h1]; exact hconfb i'
        · rcases horig i with ⟨i', h1, _⟩ | ⟨i', h1, _⟩
          · rw [h1]; exact hRg i'
          · rw [h1]; exact hRb i'
        · obtain ⟨i0, hi0⟩ := hsg
          rw [← hi0]; exact hS' i0 (by rw [hi0]; exact hsS)
      · have hsub : (P ∩ S).filter (fun a => a ∉ Set.range arcs') ⊂
            (P ∩ S).filter (fun a => a ∉ Set.range arcs) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨t, Finset.mem_filter.2 ⟨htT, htn⟩, fun h => ?_⟩
            exact (Finset.mem_filter.1 h).2 (by rw [← hj0]; exact ht')
          · intro a ha
            rw [Finset.mem_filter] at ha ⊢
            refine ⟨ha.1, fun h => ha.2 ?_⟩
            obtain ⟨i, rfl⟩ := h
            exact hS' i (Finset.mem_inter.1 ha.1).2
        have := Finset.card_lt_card hsub
        omega
  obtain ⟨k, v, arcs, hG, hT⟩ := key _ k1 v1 a1 good1 le_rfl
  exact finish k v arcs hG hT

end P225

open DiscreteConvex.CombinatorialC in
theorem solution {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V]
    [DecidableEq A] (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S)
    (pi1 pi2 : A → ℝ) (hpi1 : IsCircuit src dst pi1) (hpi2 : IsCircuit src dst pi2)
    (hne : (SuppPosR pi1 ∩ SuppPosR pi2 ∩ S).Nonempty) :
    ∃ pi : A → ℝ, IsCircuit src dst pi ∧ SuppPosR pi ⊆ SuppPosR pi1 ∪ SuppPosR pi2 ∧
      SuppNegR pi ⊆ SuppNegR pi1 ∪ SuppNegR pi2 ∧
      SuppPosR pi ∩ S = (SuppPosR pi1 ∪ SuppPosR pi2) ∩ S := by
  exact P225.main_thm src dst S hS pi1 pi2 hpi1 hpi2 hne
