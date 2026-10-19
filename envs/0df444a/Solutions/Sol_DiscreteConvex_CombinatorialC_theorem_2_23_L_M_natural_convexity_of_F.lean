-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.theorem_2_23_L_M_natural_convexity_of_F
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T20:05:20.180195+00:00
-- url     : https://prove2.me/submissions/19ce7644-ee6b-4ecc-a90c-7bbe7dfc5ed3

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_FVal
import Definitions.Def_DiscreteConvex_CombinatorialC_NonnegOrthant
import Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodularOn
import Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeROn
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_ExtendOn
import Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodular
import Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeR
import Definitions.Def_DiscreteConvex_CombinatorialC_IsOptimalCirc
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcs
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcs
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
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

namespace Q1d71

open DiscreteConvex.CombinatorialC

theorem bdry_lin {V A : Type*} [Fintype A] [DecidableEq V] (src dst : A → V)
    (a b : ℝ) (x y : A → ℝ) (v : V) :
    Boundary src dst (a • x + b • y) v = a * Boundary src dst x v + b * Boundary src dst y v := by
  unfold Boundary
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem bdry_add {V A : Type*} [Fintype A] [DecidableEq V] (src dst : A → V)
    (x y : A → ℝ) (v : V) :
    Boundary src dst (x + y) v = Boundary src dst x v + Boundary src dst y v := by
  have := bdry_lin src dst 1 1 x y v
  simpa using this

theorem bdry_sub {V A : Type*} [Fintype A] [DecidableEq V] (src dst : A → V)
    (x y : A → ℝ) (v : V) :
    Boundary src dst (x - y) v = Boundary src dst x v - Boundary src dst y v := by
  have := bdry_lin src dst 1 (-1) x y v
  simp only [one_smul, neg_smul, one_mul, neg_mul] at this
  rw [sub_eq_add_neg, this]; ring

theorem bdry_smul {V A : Type*} [Fintype A] [DecidableEq V] (src dst : A → V)
    (a : ℝ) (x : A → ℝ) (v : V) :
    Boundary src dst (a • x) v = a * Boundary src dst x v := by
  have := bdry_lin src dst a 0 x x v
  simpa using this

theorem bdd {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) :
    BddAbove {t : ℝ | ∃ xi : A → ℝ, IsFeasibleCirc src dst c xi ∧ t = dotProduct w xi} := by
  refine ⟨∑ e, |w e| * |c e|, ?_⟩
  rintro t ⟨xi, hxi, rfl⟩
  unfold dotProduct
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨h1, h2⟩ := hxi.1 e
  calc w e * xi e ≤ |w e * xi e| := le_abs_self _
    _ = |w e| * |xi e| := abs_mul _ _
    _ ≤ |w e| * |c e| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2

theorem le_F {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c xi : A → ℝ) (h : IsFeasibleCirc src dst c xi) :
    dotProduct w xi ≤ FVal src dst w c :=
  le_csSup (bdd src dst w c) ⟨xi, h, rfl⟩

theorem exists_opt {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) (hc : 0 ≤ c) :
    ∃ xi, IsFeasibleCirc src dst c xi ∧ FVal src dst w c = dotProduct w xi ∧
      ∀ xi', IsFeasibleCirc src dst c xi' → dotProduct w xi' ≤ dotProduct w xi := by
  set K : Set (A → ℝ) := Set.Icc 0 c ∩ {x | ∀ v, Boundary src dst x v = 0} with hK
  have hcont : ∀ v, Continuous (fun x : A → ℝ => Boundary src dst x v) := by
    intro v; unfold Boundary
    exact (continuous_finsetSum _ fun a _ => continuous_apply a).sub
      (continuous_finsetSum _ fun a _ => continuous_apply a)
  have hclosed : IsClosed {x : A → ℝ | ∀ v, Boundary src dst x v = 0} := by
    have : {x : A → ℝ | ∀ v, Boundary src dst x v = 0} =
        ⋂ v, {x | Boundary src dst x v = 0} := by ext; simp
    rw [this]; exact isClosed_iInter fun v => isClosed_eq (hcont v) continuous_const
  have hKc : IsCompact K := isCompact_Icc.inter_right hclosed
  have hmem : ∀ x, x ∈ K ↔ IsFeasibleCirc src dst c x := by
    intro x
    simp only [hK, Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, IsFeasibleCirc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun a => ⟨h1 a, h2 a⟩, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨fun a => (h1 a).1, fun a => (h1 a).2⟩, h3⟩
  have hne : K.Nonempty := ⟨0, (hmem 0).2 ⟨fun a => ⟨le_refl _, hc a⟩, fun v => by simp [Boundary]⟩⟩
  have hdc : Continuous (fun x : A → ℝ => dotProduct w x) := by
    unfold dotProduct
    exact continuous_finsetSum _ fun a _ => continuous_const.mul (continuous_apply a)
  obtain ⟨xi, hxiK, hmax⟩ := hKc.exists_isMaxOn hne hdc.continuousOn
  have hxi := (hmem xi).1 hxiK
  have hall : ∀ xi', IsFeasibleCirc src dst c xi' → dotProduct w xi' ≤ dotProduct w xi :=
    fun xi' h => hmax ((hmem xi').2 h)
  refine ⟨xi, hxi, le_antisymm ?_ (le_F src dst w c xi hxi), hall⟩
  apply csSup_le (⟨dotProduct w xi, xi, hxi, rfl⟩ :
    {t : ℝ | ∃ xi : A → ℝ, IsFeasibleCirc src dst c xi ∧ t = dotProduct w xi}.Nonempty)
  rintro t ⟨xi', h', rfl⟩
  exact hall xi' h'


theorem bdry_add' {V A : Type*} [Fintype A] [DecidableEq V] (src dst : A → V)
    (x y : A → ℝ) (v : V) :
    Boundary src dst (x + y) v = Boundary src dst x v + Boundary src dst y v := by
  unfold Boundary
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem bdry_sum {V A ι : Type*} [Fintype A] [DecidableEq V] (src dst : A → V)
    (s : Finset ι) (f : ι → A → ℝ) (v : V) :
    Boundary src dst (∑ t ∈ s, f t) v = ∑ t ∈ s, Boundary src dst (f t) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Boundary]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bdry_add', ih]

theorem bdry_smul_char {V A : Type*} [Fintype A] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (r : ℝ) (a : A) (u : V) :
    Boundary src dst (r • CharVec a) u =
      r * ((if src a = u then 1 else 0) - (if dst a = u then 1 else 0)) := by
  unfold Boundary CharVec
  simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> ring

/-- residual tail and head of an arc with respect to the sign of `d`. -/
noncomputable def tl {V A : Type*} (src dst : A → V) (d : A → ℝ) (a : A) : V :=
  if 0 < d a then src a else dst a

noncomputable def hdv {V A : Type*} (src dst : A → V) (d : A → ℝ) (a : A) : V :=
  if 0 < d a then dst a else src a

theorem out_exists {V A : Type*} [Fintype A] [DecidableEq V] (src dst : A → V) (d : A → ℝ)
    (hd : ∀ v, Boundary src dst d v = 0) (a : A) (ha : d a ≠ 0) :
    ∃ b, d b ≠ 0 ∧ tl src dst d b = hdv src dst d a := by
  by_contra hcon
  push_neg at hcon
  set u := hdv src dst d a with hu
  have h1 : ∀ b ∈ Finset.univ.filter (fun b => src b = u), d b ≤ 0 := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    by_contra hpos; push_neg at hpos
    exact hcon b hpos.ne' (by simp [tl, hpos, hb])
  have h2 : ∀ b ∈ Finset.univ.filter (fun b => dst b = u), 0 ≤ d b := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    by_contra hneg; push_neg at hneg
    exact hcon b hneg.ne (by simp [tl, not_lt.mpr hneg.le, hb])
  have hb := hd u
  unfold Boundary at hb
  have s1 := Finset.sum_nonpos h1
  have s2 := Finset.sum_nonneg h2
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hsrc : src a = u := by simp [hu, hdv, not_lt.mpr hneg.le]
    have := Finset.single_le_sum (f := fun b => -d b) (fun b hb => neg_nonneg.mpr (h1 b hb))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hsrc⟩)
    simp only [Finset.sum_neg_distrib] at this
    linarith
  · have hdst : dst a = u := by simp [hu, hdv, hpos]
    have := Finset.single_le_sum h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hdst⟩)
    linarith

theorem exists_cycle {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (d : A → ℝ) (hd : ∀ v, Boundary src dst d v = 0) (a0 : A)
    (ha0 : d a0 ≠ 0) :
    ∃ (k : ℕ) (v : Fin (k+1) → V) (arcs : Fin (k+1) → A),
      IsSimpleCycle src dst k v arcs ∧ Function.Injective arcs ∧
      (∀ t, d (arcs t) ≠ 0) ∧
      (∀ t, tl src dst d (arcs t) = v t ∧ hdv src dst d (arcs t) = v (t+1)) := by
  classical
  let good : V → Prop := fun u => ∃ b, d b ≠ 0 ∧ tl src dst d b = u
  let arcOf : V → A := fun u => if h : good u then h.choose else a0
  have arcOf_spec : ∀ u, good u → d (arcOf u) ≠ 0 ∧ tl src dst d (arcOf u) = u := by
    intro u hu; simp only [arcOf, dif_pos hu]; exact hu.choose_spec
  let nxt : V → V := fun u => hdv src dst d (arcOf u)
  have good_nxt : ∀ u, good u → good (nxt u) := fun u hu =>
    out_exists src dst d hd (arcOf u) (arcOf_spec u hu).1
  let x : ℕ → V := fun n => nxt^[n] (tl src dst d a0)
  have xsucc : ∀ n, x (n+1) = nxt (x n) := fun n => Function.iterate_succ_apply' _ _ _
  have xgood : ∀ n, good (x n) := by
    intro n; induction n with
    | zero => exact ⟨a0, ha0, rfl⟩
    | succ n ih => rw [xsucc]; exact good_nxt _ ih
  have hP : ∃ j, ∃ i < j, x i = x j := by
    obtain ⟨p, q, hpq, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun t : Fin (Fintype.card V + 1) => x t) (by simp)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hpq) with h | h
    · exact ⟨q, p, h, he⟩
    · exact ⟨p, q, h, he.symm⟩
  obtain ⟨i, hij, hxij⟩ := Nat.find_spec hP
  have hmin : ∀ j' < Nat.find hP, ¬ ∃ i < j', x i = x j' := fun j' h => Nat.find_min hP h
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hP = i + k + 1 := ⟨Nat.find hP - i - 1, by omega⟩
  rw [hk] at hxij
  have hwrap : ∀ t : Fin (k+1), x (i + ((t+1 : Fin (k+1)) : ℕ)) = nxt (x (i + t)) := by
    intro t
    rw [← xsucc, Fin.val_add_one]
    split_ifs with ht
    · subst ht; simp only [Fin.val_last, add_zero]; rw [hxij]
    · rfl
  have vinj : Function.Injective (fun t : Fin (k+1) => x (i + t)) := by
    intro s t hst
    simp only at hst
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact hmin (i + t) (by omega) ⟨i + s, by omega, hst⟩
    · exact hmin (i + s) (by omega) ⟨i + t, by omega, hst.symm⟩
  refine ⟨k, fun t => x (i + t), fun t => arcOf (x (i + t)), ⟨vinj, fun t => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨_, h2⟩ := arcOf_spec _ (xgood (i + t))
    simp only
    rw [hwrap t]
    simp only [nxt]
    unfold tl at h2; unfold hdv
    by_cases hp : 0 < d (arcOf (x (i + ↑t)))
    · rw [if_pos hp] at h2 ⊢; rw [h2]
    · rw [if_neg hp] at h2 ⊢; rw [h2, Finset.pair_comm]
  · intro s t hst
    simp only at hst
    apply vinj
    simp only
    rw [← (arcOf_spec _ (xgood (i + s))).2, ← (arcOf_spec _ (xgood (i + t))).2, hst]
  · intro t; exact (arcOf_spec _ (xgood (i + t))).1
  · intro t
    exact ⟨(arcOf_spec _ (xgood (i + t))).2, (hwrap t).symm⟩

noncomputable def sg {A : Type*} (d : A → ℝ) (a : A) : ℝ := if 0 < d a then 1 else -1

theorem exists_cvec {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (d : A → ℝ) (hd : ∀ v, Boundary src dst d v = 0) (a0 : A)
    (ha0 : d a0 ≠ 0) : ∃ γ : A → ℝ,
      (∀ v, Boundary src dst γ v = 0) ∧
      (∀ b, γ b = 0 ∨ (γ b = 1 ∧ 0 < d b) ∨ (γ b = -1 ∧ d b < 0)) ∧
      (∃ b, γ b ≠ 0) ∧
      (∀ a b, a ≠ b → γ a ≠ 0 → γ b ≠ 0 → IsParallelArcs src dst a b → γ a ≠ γ b) ∧
      (∀ a b, a ≠ b → γ a ≠ 0 → γ b ≠ 0 → IsSeriesArcs src dst a b → γ a = γ b) := by
  obtain ⟨k, v, arcs, hcyc, hinj, hnz, htl⟩ := exists_cycle src dst d hd a0 ha0
  set γ : A → ℝ := ∑ t, sg d (arcs t) • CharVec (arcs t) with hγ
  have hval : ∀ t, γ (arcs t) = sg d (arcs t) := by
    intro t
    rw [hγ, Finset.sum_apply, Finset.sum_eq_single t]
    · simp [CharVec]
    · intro s _ hs
      simp only [Pi.smul_apply, CharVec, smul_eq_mul]
      rw [if_neg (fun h => hs (hinj h).symm)]; ring
    · simp
  have hval0 : ∀ b, (∀ t, arcs t ≠ b) → γ b = 0 := by
    intro b hb
    rw [hγ, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro s _
    simp only [Pi.smul_apply, CharVec, smul_eq_mul]
    rw [if_neg (fun h => hb s h.symm)]; ring
  have hsg : ∀ t, (sg d (arcs t) = 1 ∧ 0 < d (arcs t)) ∨ (sg d (arcs t) = -1 ∧ d (arcs t) < 0) := by
    intro t
    unfold sg
    by_cases hp : 0 < d (arcs t)
    · left; exact ⟨if_pos hp, hp⟩
    · right; exact ⟨if_neg hp, lt_of_le_of_ne (not_lt.mp hp) (hnz t)⟩
  have hsupp : ∀ b, γ b ≠ 0 → ∃ t, arcs t = b := by
    intro b hb; by_contra h; push_neg at h; exact hb (hval0 b h)
  -- orientation: for k ≥ 1, Forward t ↔ γ (arcs t) = 1
  have hfwd : ∀ s t : Fin (k+1), s ≠ t → ∀ r : Fin (k+1),
      (Forward src v arcs r ↔ γ (arcs r) = 1) := by
    intro s t hst r
    have hk1 : (1 : Fin (k+1)) ≠ 0 := by
      intro h1
      rw [Fin.one_eq_zero_iff] at h1
      have hk0 : k = 0 := by omega
      subst hk0
      exact hst (Fin.ext (by have := s.isLt; have := t.isLt; omega))
    have hr1 : v (r + 1) ≠ v r := by
      intro h; have := hcyc.1 h
      exact hk1 (by simpa using this)
    obtain ⟨h1, h2⟩ := htl r
    rw [hval r]
    unfold Forward
    unfold tl at h1; unfold hdv at h2; unfold sg
    by_cases hp : 0 < d (arcs r)
    · rw [if_pos hp] at h1 ⊢; simp [h1]
    · rw [if_neg hp] at h1 h2 ⊢
      constructor
      · intro h; exact absurd (h2.symm.trans h) hr1
      · intro h; norm_num at h
  refine ⟨γ, fun u => ?_, fun b => ?_, ⟨arcs 0, ?_⟩, ?_, ?_⟩
  · rw [hγ, bdry_sum]
    simp only [bdry_smul_char]
    have key : ∀ t, sg d (arcs t) * ((if src (arcs t) = u then (1:ℝ) else 0) -
        (if dst (arcs t) = u then 1 else 0)) =
        (if v t = u then 1 else 0) - (if v (t+1) = u then 1 else 0) := by
      intro t
      obtain ⟨h1, h2⟩ := htl t
      unfold tl at h1; unfold hdv at h2; unfold sg
      by_cases hp : 0 < d (arcs t)
      · rw [if_pos hp] at h1 h2 ⊢; rw [← h1, ← h2]; ring
      · rw [if_neg hp] at h1 h2 ⊢; rw [← h1, ← h2]; ring
    simp only [key, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin (k+1))) _ _ (fun t => rfl)).symm
  · by_cases hb : ∃ t, arcs t = b
    · obtain ⟨t, rfl⟩ := hb
      rw [hval t]
      rcases hsg t with h | h
      · right; left; exact h
      · right; right; exact h
    · push_neg at hb; left; exact hval0 b hb
  · rw [hval 0]; unfold sg; split_ifs <;> norm_num
  · intro a b hab ha hb hpar
    obtain ⟨s, rfl⟩ := hsupp a ha
    obtain ⟨t, rfl⟩ := hsupp b hb
    have hst : s ≠ t := fun h => hab (by rw [h])
    have := hpar k v arcs hcyc s t rfl rfl
    rw [hfwd s t hst s, hfwd s t hst t] at this
    rw [hval s, hval t] at this ⊢
    rcases hsg s with h1 | h1 <;> rcases hsg t with h2 | h2 <;>
      simp_all <;> norm_num
  · intro a b hab ha hb hser
    obtain ⟨s, rfl⟩ := hsupp a ha
    obtain ⟨t, rfl⟩ := hsupp b hb
    have hst : s ≠ t := fun h => hab (by rw [h])
    have := hser k v arcs hcyc s t rfl rfl
    rw [hfwd s t hst s, hfwd s t hst t] at this
    rw [hval s, hval t] at this ⊢
    rcases hsg s with h1 | h1 <;> rcases hsg t with h2 | h2 <;>
      simp_all <;> norm_num

def Btw (x y : ℝ) : Prop := (0 ≤ x ∧ x ≤ y) ∨ (y ≤ x ∧ x ≤ 0)

theorem btw_trans {x y z : ℝ} (h1 : Btw x y) (h2 : Btw y z) : Btw x z := by
  unfold Btw at *
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; constructor <;> linarith
  · right; constructor <;> linarith
  · left; constructor <;> linarith
  · right; constructor <;> linarith

theorem btw_zero (y : ℝ) : Btw 0 y := by
  unfold Btw; rcases le_total 0 y with h | h
  · left; exact ⟨le_refl _, h⟩
  · right; exact ⟨h, le_refl _⟩

theorem btw_add {x y' g y : ℝ} (hx : Btw x y') (hg : Btw g y) (hy : y = y' + g) (hy' : Btw y' y) :
    Btw (x + g) y := by
  unfold Btw at *
  rcases le_total 0 y with h | h
  · left
    rcases hx with hx | hx <;> rcases hg with hg | hg <;> rcases hy' with hy' | hy' <;>
      constructor <;> linarith
  · right
    rcases hx with hx | hx <;> rcases hg with hg | hg <;> rcases hy' with hy' | hy' <;>
      constructor <;> linarith

/-- structural cycle-vector property -/
def Struct {V A : Type*} [DecidableEq V] (src dst : A → V) (γ : A → ℝ) : Prop :=
  (∀ b, γ b = 0 ∨ γ b = 1 ∨ γ b = -1) ∧
  (∀ a b, a ≠ b → γ a ≠ 0 → γ b ≠ 0 → IsParallelArcs src dst a b → γ a ≠ γ b) ∧
  (∀ a b, a ≠ b → γ a ≠ 0 → γ b ≠ 0 → IsSeriesArcs src dst a b → γ a = γ b)

noncomputable def supp {A : Type*} [Fintype A] (d : A → ℝ) : Finset A :=
  Finset.univ.filter (fun a => d a ≠ 0)

theorem peel {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (d : A → ℝ) (hd : ∀ v, Boundary src dst d v = 0) (a0 : A)
    (ha0 : d a0 ≠ 0) : ∃ (γ : A → ℝ) (l : ℝ), Struct src dst γ ∧
      (∀ v, Boundary src dst γ v = 0) ∧ 0 < l ∧
      (∀ b, (γ b = 1 → 0 < d b) ∧ (γ b = -1 → d b < 0)) ∧
      (∀ b, Btw (l * γ b) (d b)) ∧
      (supp (d - l • γ)).card < (supp d).card := by
  classical
  obtain ⟨γ, hb, hval, ⟨b1, hb1⟩, hpar, hser⟩ := exists_cvec src dst d hd a0 ha0
  have hconf : ∀ b, (γ b = 1 → 0 < d b) ∧ (γ b = -1 → d b < 0) := by
    intro b
    rcases hval b with h | h | h
    · rw [h]; norm_num
    · refine ⟨fun _ => h.2, fun h' => ?_⟩; rw [h.1] at h'; norm_num at h'
    · refine ⟨fun h' => ?_, fun _ => h.2⟩; rw [h.1] at h'; norm_num at h'
  have hdne : ∀ b, γ b ≠ 0 → d b ≠ 0 := by
    intro b hb
    rcases hval b with h | h | h
    · exact absurd h hb
    · exact h.2.ne'
    · exact h.2.ne
  set T := Finset.univ.filter (fun b => γ b ≠ 0) with hT
  have hTne : T.Nonempty := ⟨b1, by simp [hT, hb1]⟩
  obtain ⟨b0, hb0T, hmin⟩ := T.exists_min_image (fun b => |d b|) hTne
  have hb0 : γ b0 ≠ 0 := by simpa [hT] using hb0T
  refine ⟨γ, |d b0|, ⟨fun b => ?_, hpar, hser⟩, hb, abs_pos.mpr (hdne b0 hb0), hconf, ?_, ?_⟩
  · rcases hval b with h | h | h
    · left; exact h
    · right; left; exact h.1
    · right; right; exact h.1
  · intro b
    rcases hval b with h | h | h
    · rw [h, mul_zero]; exact btw_zero _
    · have hm := hmin b (by simp [hT, h.1])
      rw [h.1, mul_one]; left
      rw [abs_of_pos h.2] at hm
      exact ⟨abs_nonneg _, hm⟩
    · have hm := hmin b (by simp [hT, h.1])
      rw [h.1]; right
      rw [abs_of_neg h.2] at hm
      constructor <;> linarith [abs_nonneg (d b0)]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨b0, ?_, ?_⟩
      · simp [supp, hdne b0 hb0]
      · simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rcases hval b0 with h | h | h
        · exact absurd h.symm (Ne.symm hb0)
        · rw [h.1, abs_of_pos h.2]; ring
        · rw [h.1, abs_of_neg h.2]; ring
    · intro b hbm
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hbm ⊢
      intro hdb
      apply hbm
      have : γ b = 0 := by
        by_contra hg; exact hdne b hg hdb
      rw [hdb, this]; ring

theorem select {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (m1 m2 : A → ℝ)
    (hyp : ∀ γ, Struct src dst γ → 0 ≤ dotProduct m1 γ ∨ 0 ≤ dotProduct m2 γ) :
    ∀ d : A → ℝ, (∀ v, Boundary src dst d v = 0) → ∃ δ : A → ℝ,
      (∀ v, Boundary src dst δ v = 0) ∧ (∀ b, Btw (δ b) (d b)) ∧
      0 ≤ dotProduct m1 (d - δ) + dotProduct m2 δ := by
  classical
  suffices H : ∀ n, ∀ d : A → ℝ, (supp d).card = n → (∀ v, Boundary src dst d v = 0) →
      ∃ δ : A → ℝ, (∀ v, Boundary src dst δ v = 0) ∧ (∀ b, Btw (δ b) (d b)) ∧
        0 ≤ dotProduct m1 (d - δ) + dotProduct m2 δ from fun d hd => H _ d rfl hd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hn hd
  by_cases hz : ∃ a, d a ≠ 0
  · obtain ⟨a0, ha0⟩ := hz
    obtain ⟨γ, l, hst, hγb, hl, hconf, hbtw, hcard⟩ := peel src dst d hd a0 ha0
    set d' := d - l • γ with hd'
    have hd'b : ∀ v, Boundary src dst d' v = 0 := by
      intro v
      have := bdry_add' src dst d ((-l) • γ) v
      have e : d' = d + (-l) • γ := by rw [hd', neg_smul, ← sub_eq_add_neg]
      rw [e, this, hd v]
      unfold Boundary at hγb ⊢
      have := hγb v
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [← mul_sub, this, mul_zero, add_zero]
    obtain ⟨δ', hδ'b, hδ'btw, hδ'v⟩ := ih _ (by rw [← hn]; exact hcard) d' rfl hd'b
    have hd'btw : ∀ b, Btw (d' b) (d b) := by
      intro b
      have h := hbtw b
      simp only [hd', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      unfold Btw at h ⊢
      rcases h with h | h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    rcases hyp γ hst with h1 | h2
    · refine ⟨δ', hδ'b, fun b => btw_trans (hδ'btw b) (hd'btw b), ?_⟩
      have e : d - δ' = (d' - δ') + l • γ := by rw [hd']; abel
      rw [e, dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith
    · refine ⟨δ' + l • γ, fun v => ?_, fun b => ?_, ?_⟩
      · rw [bdry_add', hδ'b v]
        unfold Boundary at hγb ⊢
        have := hγb v
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [← mul_sub, this, mul_zero, add_zero]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact btw_add (hδ'btw b) (hbtw b) (by simp [hd']) (hd'btw b)
      · have e : d - (δ' + l • γ) = d' - δ' := by rw [hd']; abel
        rw [e, dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith
  · push_neg at hz
    refine ⟨0, fun v => by simp [Boundary], fun b => btw_zero _, ?_⟩
    have : d = 0 := funext hz
    simp [this]

theorem through {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (i : A) :
    ∀ d : A → ℝ, (∀ v, Boundary src dst d v = 0) → d i ≠ 0 → ∃ γ : A → ℝ,
      Struct src dst γ ∧ (∀ v, Boundary src dst γ v = 0) ∧
      (∀ b, (γ b = 1 → 0 < d b) ∧ (γ b = -1 → d b < 0)) ∧ γ i ≠ 0 := by
  classical
  suffices H : ∀ n, ∀ d : A → ℝ, (supp d).card = n → (∀ v, Boundary src dst d v = 0) →
      d i ≠ 0 → ∃ γ : A → ℝ, Struct src dst γ ∧ (∀ v, Boundary src dst γ v = 0) ∧
      (∀ b, (γ b = 1 → 0 < d b) ∧ (γ b = -1 → d b < 0)) ∧ γ i ≠ 0 from
    fun d hd hi => H _ d rfl hd hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hn hd hi
  obtain ⟨γ, l, hst, hγb, hl, hconf, hbtw, hcard⟩ := peel src dst d hd i hi
  by_cases hγi : γ i ≠ 0
  · exact ⟨γ, hst, hγb, hconf, hγi⟩
  · push_neg at hγi
    set d' := d - l • γ with hd'
    have hd'b : ∀ v, Boundary src dst d' v = 0 := by
      intro v
      have := bdry_add' src dst d ((-l) • γ) v
      have e : d' = d + (-l) • γ := by rw [hd', neg_smul, ← sub_eq_add_neg]
      rw [e, this, hd v]
      unfold Boundary at hγb ⊢
      have := hγb v
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [← mul_sub, this, mul_zero, add_zero]
    have hd'i : d' i ≠ 0 := by simp [hd', hγi, hi]
    obtain ⟨γ', h1, h2, h3, h4⟩ := ih _ (by rw [← hn]; exact hcard) d' rfl hd'b hd'i
    refine ⟨γ', h1, h2, fun b => ⟨fun h => ?_, fun h => ?_⟩, h4⟩
    · have := (h3 b).1 h
      have hb := hbtw b
      simp only [hd', Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      unfold Btw at hb
      rcases hb with hb | hb <;> linarith [hb.1, hb.2]
    · have := (h3 b).2 h
      have hb := hbtw b
      simp only [hd', Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      unfold Btw at hb
      rcases hb with hb | hb <;> linarith [hb.1, hb.2]


theorem sum_le_one {A : Type*} (s : Finset A) (hs : s.card ≤ 1) (g : ℝ → ℝ) (hg : g 0 = 0)
    (D : A → ℝ) : ∑ a ∈ s, g (D a) = g (∑ a ∈ s, D a) := by
  classical
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · subst h; simp [hg]
  · have h : s = {x} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun y hy => Finset.card_le_one.mp hs y hy x hx⟩
    subst h; simp

theorem split_P {V A : Type*} [Fintype A] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (P : Finset A)
    (hP : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → IsParallelArcs src dst a b)
    (γ : A → ℝ) (hγ : Struct src dst γ) :
    (P.filter (fun a => γ a = 1)).card ≤ 1 ∧ (P.filter (fun a => γ a = -1)).card ≤ 1 ∧
    ∀ f : A → ℝ, (∀ a, a ∉ P → f a = 0) →
      dotProduct f γ = ∑ a ∈ P.filter (fun a => γ a = 1), f a -
        ∑ a ∈ P.filter (fun a => γ a = -1), f a := by
  obtain ⟨hv, hpar, -⟩ := hγ
  refine ⟨Finset.card_le_one.mpr ?_, Finset.card_le_one.mpr ?_, fun f hf => ?_⟩
  · intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hab
    exact hpar a b hab (by rw [ha.2]; norm_num) (by rw [hb.2]; norm_num)
      (hP a ha.1 b hb.1 hab) (by rw [ha.2, hb.2])
  · intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hab
    exact hpar a b hab (by rw [ha.2]; norm_num) (by rw [hb.2]; norm_num)
      (hP a ha.1 b hb.1 hab) (by rw [ha.2, hb.2])
  · rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    unfold dotProduct
    rw [← Finset.sum_subset (Finset.subset_univ P)]
    · apply Finset.sum_congr rfl
      intro a _
      rcases hv a with h | h | h <;> rw [h] <;> norm_num
    · intro a _ ha
      rw [hf a ha, zero_mul]

theorem C1 {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (P : Finset A) (hP : IsParallelArcSet src dst P) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    TranslationSubmodular (fun wP : P → ℝ => FVal src dst (ExtendOn w0 P wP) c0) := by
  intro p q α hα
  obtain ⟨ξ1, hf1, hF1, -⟩ := exists_opt src dst
    (ExtendOn w0 P ((p - α • (fun _ => (1:ℝ))) ⊔ q)) c0 hc0
  obtain ⟨ξ2, hf2, hF2, -⟩ := exists_opt src dst
    (ExtendOn w0 P (p ⊓ (q + α • (fun _ => (1:ℝ))))) c0 hc0
  set D : A → ℝ := fun a => if h : a ∈ P then p ⟨a, h⟩ - q ⟨a, h⟩ else 0 with hD
  set m1 : A → ℝ := fun a => if a ∈ P then min α (D a) else 0 with hm1
  set m2 : A → ℝ := fun a => m1 a - D a with hm2
  have hcirc : ∀ v, Boundary src dst (ξ1 - ξ2) v = 0 := by
    intro v; rw [bdry_sub, hf1.2 v, hf2.2 v, sub_zero]
  have hyp : ∀ γ, Struct src dst γ → 0 ≤ dotProduct m1 γ ∨ 0 ≤ dotProduct m2 γ := by
    intro γ hγ
    obtain ⟨hcp, hcn, hspl⟩ := split_P src dst P hP γ hγ
    have hz1 : ∀ a, a ∉ P → m1 a = 0 := fun a ha => by simp [hm1, ha]
    have hz2 : ∀ a, a ∉ P → m2 a = 0 := fun a ha => by simp [hm2, hm1, hD, ha]
    have hzD : ∀ a, a ∉ P → D a = 0 := fun a ha => by simp [hD, ha]
    rw [hspl m1 hz1, hspl m2 hz2]
    have e1 : ∀ s : Finset A, s ⊆ P → ∑ a ∈ s, m1 a = ∑ a ∈ s, min α (D a) := by
      intro s hs; apply Finset.sum_congr rfl; intro a ha; simp [hm1, hs ha]
    have e2 : ∀ s : Finset A, s ⊆ P → ∑ a ∈ s, m2 a = ∑ a ∈ s, min α (D a) - ∑ a ∈ s, D a := by
      intro s hs; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro a ha
      simp [hm2, hm1, hs ha]
    have hsp : P.filter (fun a => γ a = 1) ⊆ P := Finset.filter_subset _ _
    have hsn : P.filter (fun a => γ a = -1) ⊆ P := Finset.filter_subset _ _
    have hg0 : min α 0 = 0 := min_eq_right hα
    rw [e1 _ hsp, e1 _ hsn, e2 _ hsp, e2 _ hsn,
      sum_le_one _ hcp (fun x => min α x) hg0, sum_le_one _ hcn (fun x => min α x) hg0]
    set sp := ∑ a ∈ P.filter (fun a => γ a = 1), D a
    set sn := ∑ a ∈ P.filter (fun a => γ a = -1), D a
    rcases lt_or_ge (min α sp) (min α sn) with h | h
    · right
      have h1 : min α sp = sp := by
        rcases le_total α sp with h' | h'
        · rw [min_eq_left h'] at h ⊢; linarith [min_le_left α sn]
        · exact min_eq_right h'
      have h2 : min α sn ≤ sn := min_le_right _ _
      linarith [min_le_right α sn]
    · left; linarith
  obtain ⟨δ, hδb, hδbtw, hδv⟩ := select src dst m1 m2 hyp (ξ1 - ξ2) hcirc
  have hη1 : IsFeasibleCirc src dst c0 (ξ1 - δ) := by
    refine ⟨fun a => ?_, fun v => by rw [bdry_sub, hf1.2 v, hδb v, sub_zero]⟩
    have h := hδbtw a
    obtain ⟨h1, h2⟩ := hf1.1 a
    obtain ⟨h3, h4⟩ := hf2.1 a
    simp only [Pi.sub_apply] at h ⊢
    unfold Btw at h
    rcases h with h | h <;> constructor <;> linarith [h.1, h.2]
  have hη2 : IsFeasibleCirc src dst c0 (ξ2 + δ) := by
    refine ⟨fun a => ?_, fun v => by rw [bdry_add, hf2.2 v, hδb v, add_zero]⟩
    have h := hδbtw a
    obtain ⟨h1, h2⟩ := hf1.1 a
    obtain ⟨h3, h4⟩ := hf2.1 a
    simp only [Pi.sub_apply, Pi.add_apply] at h ⊢
    unfold Btw at h
    rcases h with h | h <;> constructor <;> linarith [h.1, h.2]
  have l1 := le_F src dst (ExtendOn w0 P p) c0 _ hη1
  have l2 := le_F src dst (ExtendOn w0 P q) c0 _ hη2
  have key : dotProduct (ExtendOn w0 P p) (ξ1 - δ) + dotProduct (ExtendOn w0 P q) (ξ2 + δ) -
      dotProduct (ExtendOn w0 P ((p - α • (fun _ => (1:ℝ))) ⊔ q)) ξ1 -
      dotProduct (ExtendOn w0 P (p ⊓ (q + α • (fun _ => (1:ℝ))))) ξ2 =
      dotProduct m1 ((ξ1 - ξ2) - δ) + dotProduct m2 δ := by
    simp only [dotProduct, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    simp only [Pi.sub_apply, Pi.add_apply]
    by_cases ha : a ∈ P
    · simp only [ExtendOn, dif_pos ha, hm2, hm1, hD, if_pos ha, Pi.sup_apply, Pi.inf_apply,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      rcases le_total (p ⟨a, ha⟩ - α) (q ⟨a, ha⟩) with h | h
      · rw [max_eq_right h, min_eq_left (by linarith : p ⟨a, ha⟩ ≤ q ⟨a, ha⟩ + α),
          min_eq_right (by linarith : p ⟨a, ha⟩ - q ⟨a, ha⟩ ≤ α)]
        ring
      · rw [max_eq_left h, min_eq_right (by linarith : q ⟨a, ha⟩ + α ≤ p ⟨a, ha⟩),
          min_eq_left (by linarith : α ≤ p ⟨a, ha⟩ - q ⟨a, ha⟩)]
        ring
    · simp only [ExtendOn, dif_neg ha, hm2, hm1, hD, if_neg ha]
      ring
  show FVal src dst (ExtendOn w0 P p) c0 + FVal src dst (ExtendOn w0 P q) c0 ≥
    FVal src dst (ExtendOn w0 P ((p - α • (fun _ => (1:ℝ))) ⊔ q)) c0 +
      FVal src dst (ExtendOn w0 P (p ⊓ (q + α • (fun _ => (1:ℝ))))) c0
  rw [hF1, hF2]
  linarith

theorem ext_cap2 {A : Type*} [DecidableEq A] (c0 : A → ℝ) (P : Finset A) (x : P → ℝ) (α s : ℝ)
    (i j : P) (a : A) :
    ExtendOn c0 P (x + (s * α) • (CharVec i - CharVec j)) a = ExtendOn c0 P x a +
      s * α * ((if a = (i : A) then 1 else 0) - (if a = (j : A) then 1 else 0)) := by
  unfold ExtendOn CharVec
  by_cases ha : a ∈ P
  · simp only [dif_pos ha, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have e1 : (⟨a, ha⟩ : P) = i ↔ a = (i : A) := Subtype.ext_iff
    have e2 : (⟨a, ha⟩ : P) = j ↔ a = (j : A) := Subtype.ext_iff
    by_cases h1 : a = (i : A) <;> by_cases h2 : a = (j : A) <;> simp [e1, e2, h1, h2]
  · have h1 : a ≠ (i : A) := fun h => ha (h ▸ i.2)
    have h2 : a ≠ (j : A) := fun h => ha (h ▸ j.2)
    simp [ha, h1, h2]

theorem ext_cap1 {A : Type*} [DecidableEq A] (c0 : A → ℝ) (P : Finset A) (x : P → ℝ) (α s : ℝ)
    (i : P) (a : A) :
    ExtendOn c0 P (x + (s * α) • CharVec i) a = ExtendOn c0 P x a +
      s * α * (if a = (i : A) then 1 else 0) := by
  unfold ExtendOn CharVec
  by_cases ha : a ∈ P
  · simp only [dif_pos ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : (⟨a, ha⟩ : P) = i ↔ a = (i : A) := Subtype.ext_iff
    by_cases h1 : a = (i : A) <;> simp [e1, h1]
  · have h1 : a ≠ (i : A) := fun h => ha (h ▸ i.2)
    simp [ha, h1]

theorem move {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V]
    (src dst : A → V) (ξ1 ξ2 γ X' Y' : A → ℝ) (h1 : ∀ a, 0 ≤ ξ1 a) (h2 : ∀ a, 0 ≤ ξ2 a)
    (hb1 : ∀ v, Boundary src dst ξ1 v = 0) (hb2 : ∀ v, Boundary src dst ξ2 v = 0)
    (hγb : ∀ v, Boundary src dst γ v = 0)
    (hconf : ∀ b, (γ b = 1 → 0 < ξ1 b - ξ2 b) ∧ (γ b = -1 → ξ1 b - ξ2 b < 0))
    (hv : ∀ b, γ b = 0 ∨ γ b = 1 ∨ γ b = -1)
    (α : ℝ) (hα : 0 ≤ α) (hαle : ∀ a, γ a ≠ 0 → α ≤ |ξ1 a - ξ2 a|)
    (hX : ∀ a, ξ1 a - α * γ a ≤ X' a) (hY : ∀ a, ξ2 a + α * γ a ≤ Y' a) :
    IsFeasibleCirc src dst X' (ξ1 - α • γ) ∧ IsFeasibleCirc src dst Y' (ξ2 + α • γ) := by
  refine ⟨⟨fun a => ⟨?_, ?_⟩, fun v => ?_⟩, ⟨fun a => ⟨?_, ?_⟩, fun v => ?_⟩⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rcases hv a with h | h | h
    · rw [h, mul_zero, sub_zero]; exact h1 a
    · have := (hconf a).1 h
      have hl := hαle a (by rw [h]; norm_num)
      rw [abs_of_pos this] at hl
      rw [h, mul_one]; linarith [h2 a]
    · rw [h]; linarith [h1 a]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; exact hX a
  · rw [bdry_sub, hb1 v, bdry_smul, hγb v]; ring
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hv a with h | h | h
    · rw [h, mul_zero, add_zero]; exact h2 a
    · rw [h]; linarith [h2 a]
    · have := (hconf a).2 h
      have hl := hαle a (by rw [h]; norm_num)
      rw [abs_of_neg this] at hl
      rw [h]; linarith [h1 a]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hY a
  · rw [bdry_add, hb2 v, bdry_smul, hγb v]; ring

theorem C2 {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (P : Finset A) (hP : IsParallelArcSet src dst P) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    MNatExchangeROn NonnegOrthant
      (fun cP : P → ℝ => -(FVal src dst w0 (ExtendOn c0 P cP))) := by
  intro x hx y hy i hi
  have hxa : ∀ a, 0 ≤ ExtendOn c0 P x a := by
    intro a; unfold ExtendOn; split_ifs with h
    · exact hx ⟨a, h⟩
    · exact hc0 a
  have hya : ∀ a, 0 ≤ ExtendOn c0 P y a := by
    intro a; unfold ExtendOn; split_ifs with h
    · exact hy ⟨a, h⟩
    · exact hc0 a
  have hXY : ∀ a, a ∉ P → ExtendOn c0 P x a = ExtendOn c0 P y a := by
    intro a ha; simp [ExtendOn, ha]
  obtain ⟨ξ1, hf1, hF1, -⟩ := exists_opt src dst w0 (ExtendOn c0 P x) hxa
  obtain ⟨ξ2, hf2, hF2, -⟩ := exists_opt src dst w0 (ExtendOn c0 P y) hya
  have hi' : 0 < x i - y i := by
    simpa [SuppPosR] using hi
  have hXi : ExtendOn c0 P x (i : A) = x i := by simp [ExtendOn]
  have hYi : ExtendOn c0 P y (i : A) = y i := by simp [ExtendOn]
  -- the generic lower bound
  have lowb : ∀ X' Y' : A → ℝ, ∀ η1 η2 : A → ℝ, IsFeasibleCirc src dst X' η1 →
      IsFeasibleCirc src dst Y' η2 → dotProduct w0 η1 + dotProduct w0 η2 =
        dotProduct w0 ξ1 + dotProduct w0 ξ2 →
      FVal src dst w0 (ExtendOn c0 P x) + FVal src dst w0 (ExtendOn c0 P y) ≤
        FVal src dst w0 X' + FVal src dst w0 Y' := by
    intro X' Y' η1 η2 h1 h2 he
    have := le_F src dst w0 X' η1 h1
    have := le_F src dst w0 Y' η2 h2
    rw [hF1, hF2]; linarith
  by_cases hA : ξ1 (i : A) < x i
  · right
    refine ⟨x i - ξ1 (i : A), by linarith, fun α hα0 hα1 => ?_⟩
    show -(FVal src dst w0 (ExtendOn c0 P x)) + -(FVal src dst w0 (ExtendOn c0 P y)) ≥
      -(FVal src dst w0 (ExtendOn c0 P (x - α • CharVec i))) +
        -(FVal src dst w0 (ExtendOn c0 P (y + α • CharVec i)))
    have e1 : x - α • CharVec i = x + ((-1) * α) • CharVec i := by
      rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
    have e2 : y + α • CharVec i = y + (1 * α) • CharVec i := by rw [one_mul]
    rw [e1, e2]
    have := lowb (ExtendOn c0 P (x + ((-1) * α) • CharVec i))
      (ExtendOn c0 P (y + (1 * α) • CharVec i)) ξ1 ξ2 ⟨fun a => ⟨(hf1.1 a).1, ?_⟩, hf1.2⟩
      ⟨fun a => ⟨(hf2.1 a).1, ?_⟩, hf2.2⟩ rfl
    · linarith
    · rw [ext_cap1]
      by_cases ha : a = (i : A)
      · subst ha; rw [if_pos rfl, hXi]; linarith
      · rw [if_neg ha]; linarith [(hf1.1 a).2]
    · rw [ext_cap1]
      by_cases ha : a = (i : A)
      · subst ha; rw [if_pos rfl]; linarith [(hf2.1 (i : A)).2]
      · rw [if_neg ha]; linarith [(hf2.1 a).2]
  · have hξ1i : ξ1 (i : A) = x i := le_antisymm (hXi ▸ (hf1.1 (i : A)).2) (not_lt.mp hA)
    have hdi : 0 < ξ1 (i : A) - ξ2 (i : A) := by
      have := (hf2.1 (i : A)).2; rw [hYi] at this; linarith
    have hcirc : ∀ v, Boundary src dst (ξ1 - ξ2) v = 0 := by
      intro v; rw [bdry_sub, hf1.2 v, hf2.2 v, sub_zero]
    obtain ⟨γ, hst, hγb, hconf, hγi⟩ := through src dst (i : A) (ξ1 - ξ2) hcirc hdi.ne'
    obtain ⟨hcp, hcn, -⟩ := split_P src dst P hP γ hst
    have hv := hst.1
    have hγi1 : γ (i : A) = 1 := by
      rcases hv (i : A) with h | h | h
      · exact absurd h hγi
      · exact h
      · have := (hconf (i : A)).2 h; simp only [Pi.sub_apply] at this; linarith
    have hconf' : ∀ b, (γ b = 1 → 0 < ξ1 b - ξ2 b) ∧ (γ b = -1 → ξ1 b - ξ2 b < 0) := by
      intro b; have := hconf b; simpa using this
    -- step size
    set T := Finset.univ.filter (fun b => γ b ≠ 0) with hT
    have hTne : T.Nonempty := ⟨(i : A), by simp [hT, hγi]⟩
    obtain ⟨b0, hb0T, hmin⟩ := T.exists_min_image (fun b => |ξ1 b - ξ2 b|) hTne
    have hb0 : γ b0 ≠ 0 := by simpa [hT] using hb0T
    have hpos : 0 < |ξ1 b0 - ξ2 b0| := by
      rcases hv b0 with h | h | h
      · exact absurd h hb0
      · exact abs_pos.mpr ((hconf' b0).1 h).ne'
      · exact abs_pos.mpr ((hconf' b0).2 h).ne
    have hαle : ∀ α, α ≤ |ξ1 b0 - ξ2 b0| → ∀ a, γ a ≠ 0 → α ≤ |ξ1 a - ξ2 a| :=
      fun α h a ha => h.trans (hmin a (by simp [hT, ha]))
    -- P-arcs with γ = 1 is only i
    have honly : ∀ a, a ∈ P → γ a = 1 → a = (i : A) := by
      intro a ha h1
      exact Finset.card_le_one.mp hcp a (by simp [ha, h1]) (i : A) (by simp [hγi1, i.2])
    have hfeas_lo1 : ∀ a, 0 ≤ ξ1 a := fun a => (hf1.1 a).1
    have hfeas_lo2 : ∀ a, 0 ≤ ξ2 a := fun a => (hf2.1 a).1
    by_cases hB : ∃ b ∈ P.filter (fun a => γ a = -1), ∃ hb : b ∈ P, x ⟨b, hb⟩ < y ⟨b, hb⟩
    · obtain ⟨b, hbN, hbP, hxyb⟩ := hB
      have hγb1 : γ b = -1 := (Finset.mem_filter.mp hbN).2
      have honlyN : ∀ a, a ∈ P → γ a = -1 → a = b := by
        intro a ha h1
        exact Finset.card_le_one.mp hcn a (by simp [ha, h1]) b hbN
      left
      refine ⟨⟨b, hbP⟩, ?_, |ξ1 b0 - ξ2 b0|, hpos, fun α hα0 hα1 => ?_⟩
      · simp [SuppNegR, hxyb]
      show -(FVal src dst w0 (ExtendOn c0 P x)) + -(FVal src dst w0 (ExtendOn c0 P y)) ≥
        -(FVal src dst w0 (ExtendOn c0 P (x - α • (CharVec i - CharVec ⟨b, hbP⟩)))) +
          -(FVal src dst w0 (ExtendOn c0 P (y + α • (CharVec i - CharVec ⟨b, hbP⟩))))
      have e1 : x - α • (CharVec i - CharVec ⟨b, hbP⟩) =
          x + ((-1) * α) • (CharVec i - CharVec (⟨b, hbP⟩ : P)) := by
        rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
      have e2 : y + α • (CharVec i - CharVec ⟨b, hbP⟩) =
          y + (1 * α) • (CharVec i - CharVec (⟨b, hbP⟩ : P)) := by rw [one_mul]
      rw [e1, e2]
      have hib : (i : A) ≠ b := fun h => by rw [h, hγb1] at hγi1; norm_num at hγi1
      have hm := move src dst ξ1 ξ2 γ
        (ExtendOn c0 P (x + ((-1) * α) • (CharVec i - CharVec (⟨b, hbP⟩ : P))))
        (ExtendOn c0 P (y + (1 * α) • (CharVec i - CharVec (⟨b, hbP⟩ : P))))
        hfeas_lo1 hfeas_lo2 hf1.2 hf2.2 hγb hconf' hv α hα0 (hαle α hα1) ?_ ?_
      · have := lowb _ _ _ _ hm.1 hm.2
          (by simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]; ring)
        linarith
      · intro a
        rw [ext_cap2]
        try simp only [Subtype.coe_mk]
        rcases hv a with h | h | h
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          have h2 : a ≠ b := fun e => by rw [e, hγb1] at h; norm_num at h
          rw [h, if_neg h1, if_neg h2]; linarith [(hf1.1 a).2]
        · by_cases h1 : a = (i : A)
          · have h2 : a ≠ b := fun e => hib (h1 ▸ e)
            rw [h, if_pos h1, if_neg h2]; linarith [(hf1.1 a).2]
          · have h2 : a ≠ b := fun e => by rw [e, hγb1] at h; norm_num at h
            rw [h, if_neg h1, if_neg h2]; linarith [(hf1.1 a).2]
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          by_cases h2 : a = b
          · rw [h, if_neg h1, if_pos h2]; linarith [(hf1.1 a).2]
          · rw [h, if_neg h1, if_neg h2]
            have haP : a ∉ P := fun haP => h2 (honlyN a haP h)
            have hc := (hconf' a).2 h
            have hl := hαle α hα1 a (by rw [h]; norm_num)
            rw [abs_of_neg hc] at hl
            rw [hXY a haP]; linarith [(hf2.1 a).2]
      · intro a
        rw [ext_cap2]
        try simp only [Subtype.coe_mk]
        rcases hv a with h | h | h
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          have h2 : a ≠ b := fun e => by rw [e, hγb1] at h; norm_num at h
          rw [h, if_neg h1, if_neg h2]; linarith [(hf2.1 a).2]
        · have h2 : a ≠ b := fun e => by rw [e, hγb1] at h; norm_num at h
          by_cases h1 : a = (i : A)
          · rw [h, if_pos h1, if_neg h2]; linarith [(hf2.1 a).2]
          · have haP : a ∉ P := fun haP => h1 (honly a haP h)
            have hc := (hconf' a).1 h
            have hl := hαle α hα1 a (by rw [h]; norm_num)
            rw [abs_of_pos hc] at hl
            rw [h, if_neg h1, if_neg h2, ← hXY a haP]; linarith [(hf1.1 a).2]
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          by_cases h2 : a = b
          · rw [h, if_neg h1, if_pos h2]; linarith [(hf2.1 a).2]
          · rw [h, if_neg h1, if_neg h2]; linarith [(hf2.1 a).2]
    · right
      push_neg at hB
      refine ⟨|ξ1 b0 - ξ2 b0|, hpos, fun α hα0 hα1 => ?_⟩
      show -(FVal src dst w0 (ExtendOn c0 P x)) + -(FVal src dst w0 (ExtendOn c0 P y)) ≥
        -(FVal src dst w0 (ExtendOn c0 P (x - α • CharVec i))) +
          -(FVal src dst w0 (ExtendOn c0 P (y + α • CharVec i)))
      have e1 : x - α • CharVec i = x + ((-1) * α) • CharVec i := by
        rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
      have e2 : y + α • CharVec i = y + (1 * α) • CharVec i := by rw [one_mul]
      rw [e1, e2]
      have hm := move src dst ξ1 ξ2 γ
        (ExtendOn c0 P (x + ((-1) * α) • CharVec i))
        (ExtendOn c0 P (y + (1 * α) • CharVec i))
        hfeas_lo1 hfeas_lo2 hf1.2 hf2.2 hγb hconf' hv α hα0 (hαle α hα1) ?_ ?_
      · have := lowb _ _ _ _ hm.1 hm.2
          (by simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]; ring)
        linarith
      · intro a
        rw [ext_cap1]
        rcases hv a with h | h | h
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          rw [h, if_neg h1]; linarith [(hf1.1 a).2]
        · by_cases h1 : a = (i : A)
          · rw [h, if_pos h1]; linarith [(hf1.1 a).2]
          · rw [h, if_neg h1]; linarith [(hf1.1 a).2]
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          rw [h, if_neg h1]
          have hc := (hconf' a).2 h
          have hl := hαle α hα1 a (by rw [h]; norm_num)
          rw [abs_of_neg hc] at hl
          have hYX : ExtendOn c0 P y a ≤ ExtendOn c0 P x a := by
            by_cases haP : a ∈ P
            · have := hB a (by simp [haP, h]) haP
              simpa [ExtendOn, haP] using this
            · rw [hXY a haP]
          linarith [(hf2.1 a).2]
      · intro a
        rw [ext_cap1]
        rcases hv a with h | h | h
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          rw [h, if_neg h1]; linarith [(hf2.1 a).2]
        · by_cases h1 : a = (i : A)
          · rw [h, if_pos h1]; linarith [(hf2.1 a).2]
          · have haP : a ∉ P := fun haP => h1 (honly a haP h)
            have hc := (hconf' a).1 h
            have hl := hαle α hα1 a (by rw [h]; norm_num)
            rw [abs_of_pos hc] at hl
            rw [h, if_neg h1, ← hXY a haP]; linarith [(hf1.1 a).2]
        · have h1 : a ≠ (i : A) := fun e => by rw [e, hγi1] at h; norm_num at h
          rw [h, if_neg h1]; linarith [(hf2.1 a).2]


/-! ### C4: truncation lemma for series arc sets and L-natural concavity in `c_S` -/

/-- `γ` is sign-conformal to `D`. -/
def Conf {A : Type*} (D γ : A → ℝ) : Prop := ∀ b, (γ b = 1 → 0 < D b) ∧ (γ b = -1 → D b < 0)

/-- support of `γ` inside `S`. -/
noncomputable def SS {A : Type*} (S : Finset A) (γ : A → ℝ) : Finset A :=
  S.filter (fun a => γ a ≠ 0)

theorem exists_circ {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (d : A → ℝ) (hd : ∀ v, Boundary src dst d v = 0) (a0 : A)
    (ha0 : d a0 ≠ 0) : ∃ γ : A → ℝ, IsCircuit src dst γ ∧ Conf d γ := by
  obtain ⟨k, v, arcs, hcyc, hinj, hnz, htl⟩ := exists_cycle src dst d hd a0 ha0
  set γ : A → ℝ := ∑ t, sg d (arcs t) • CharVec (arcs t) with hγ
  have hval : ∀ t, γ (arcs t) = sg d (arcs t) := by
    intro t
    rw [hγ, Finset.sum_apply, Finset.sum_eq_single t]
    · simp [CharVec]
    · intro s _ hs
      simp only [Pi.smul_apply, CharVec, smul_eq_mul]
      rw [if_neg (fun h => hs (hinj h).symm)]; ring
    · simp
  have hval0 : ∀ b, (∀ t, arcs t ≠ b) → γ b = 0 := by
    intro b hb
    rw [hγ, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro s _
    simp only [Pi.smul_apply, CharVec, smul_eq_mul]
    rw [if_neg (fun h => hb s h.symm)]; ring
  have hsg : ∀ t, (sg d (arcs t) = 1 ∧ 0 < d (arcs t)) ∨ (sg d (arcs t) = -1 ∧ d (arcs t) < 0) := by
    intro t
    unfold sg
    by_cases hp : 0 < d (arcs t)
    · left; exact ⟨if_pos hp, hp⟩
    · right; exact ⟨if_neg hp, lt_of_le_of_ne (not_lt.mp hp) (hnz t)⟩
  have hsupp : ∀ b, γ b ≠ 0 → ∃ t, arcs t = b := by
    intro b hb; by_contra h; push_neg at h; exact hb (hval0 b h)
  refine ⟨γ, ⟨fun b => ?_, fun u => ?_, k, v, arcs, hcyc, ?_⟩, fun b => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · by_cases hb : ∃ t, arcs t = b
    · obtain ⟨t, rfl⟩ := hb
      rw [hval t]
      rcases hsg t with h | h
      · left; exact h.1
      · right; right; exact h.1
    · push_neg at hb; right; left; exact hval0 b hb
  · rw [hγ, bdry_sum]
    simp only [bdry_smul_char]
    have key : ∀ t, sg d (arcs t) * ((if src (arcs t) = u then (1:ℝ) else 0) -
        (if dst (arcs t) = u then 1 else 0)) =
        (if v t = u then 1 else 0) - (if v (t+1) = u then 1 else 0) := by
      intro t
      obtain ⟨h1, h2⟩ := htl t
      unfold tl at h1; unfold hdv at h2; unfold sg
      by_cases hp : 0 < d (arcs t)
      · rw [if_pos hp] at h1 h2 ⊢; rw [← h1, ← h2]; ring
      · rw [if_neg hp] at h1 h2 ⊢; rw [← h1, ← h2]; ring
    simp only [key, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin (k+1))) _ _ (fun t => rfl)).symm
  · ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, SuppPosR,
      SuppNegR, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      rw [hval t]
      rcases hsg t with h | h
      · left; rw [h.1]; norm_num
      · right; rw [h.1]; norm_num
    · intro h
      apply hsupp
      rcases h with h | h
      · exact h.ne'
      · exact h.ne
  · by_cases hb : ∃ t, arcs t = b
    · obtain ⟨t, rfl⟩ := hb
      rw [hval t] at h1
      rcases hsg t with h | h
      · exact h.2
      · rw [h.1] at h1; norm_num at h1
    · push_neg at hb; rw [hval0 b hb] at h1; norm_num at h1
  · by_cases hb : ∃ t, arcs t = b
    · obtain ⟨t, rfl⟩ := hb
      rw [hval t] at h1
      rcases hsg t with h | h
      · rw [h.1] at h1; norm_num at h1
      · exact h.2
    · push_neg at hb; rw [hval0 b hb] at h1; norm_num at h1

theorem circ_series {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (γ : A → ℝ)
    (hγ : IsCircuit src dst γ) : ∀ a ∈ S, ∀ b ∈ S, γ a ≠ 0 → γ b ≠ 0 → γ a = γ b := by
  intro a ha b hb h1 h2
  by_cases hone : ∃ s, γ s = 1
  · obtain ⟨s, hs⟩ := hone
    obtain ⟨k, v, arcs, hc, hinj, hval, hoff⟩ := P225.dc_of_circuit src dst γ hγ s hs
    have hra : a ∈ Set.range arcs := by
      by_contra h; exact h1 (hoff a h)
    have hrb : b ∈ Set.range arcs := by
      by_contra h; exact h2 (hoff b h)
    obtain ⟨i, rfl⟩ := hra
    obtain ⟨j, rfl⟩ := hrb
    by_cases hab : arcs i = arcs j
    · rw [hab]
    · have hser := hS _ ha _ hb hab k v arcs hc i j rfl rfl
      rw [hval i, hval j]
      unfold P225.sg
      unfold Forward at hser
      by_cases hi : src (arcs i) = v i
      · rw [if_pos hi, if_pos (hser.mp hi)]
      · rw [if_neg hi, if_neg (fun h => hi (hser.mpr h))]
  · push_neg at hone
    have ha' : γ a = -1 := by
      rcases hγ.1 a with h | h | h
      · exact absurd h (hone a)
      · exact absurd h h1
      · exact h
    have hb' : γ b = -1 := by
      rcases hγ.1 b with h | h | h
      · exact absurd h (hone b)
      · exact absurd h h2
      · exact h
    rw [ha', hb']

theorem circ_neg {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (γ : A → ℝ) (hγ : IsCircuit src dst γ) : IsCircuit src dst (-γ) := by
  obtain ⟨hv, hb, k, v, arcs, hc, himg⟩ := hγ
  refine ⟨fun a => ?_, fun u => ?_, k, v, arcs, hc, ?_⟩
  · simp only [Pi.neg_apply]
    rcases hv a with h | h | h <;> rw [h] <;> norm_num
  · have : -γ = (-1 : ℝ) • γ := by ext; simp
    rw [this, bdry_smul, hb u]; ring
  · rw [himg]; ext b
    simp only [SuppPosR, SuppNegR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Pi.neg_apply, neg_pos, neg_lt_zero]
    exact or_comm

theorem conf_neg {A : Type*} {D γ : A → ℝ} (hc : Conf D γ) : Conf (-D) (-γ) := by
  intro b
  simp only [Pi.neg_apply]
  constructor
  · intro h
    have : γ b = -1 := by linarith
    have := (hc b).2 this; linarith
  · intro h
    have : γ b = 1 := by linarith
    have := (hc b).1 this; linarith

theorem SS_neg {A : Type*} (S : Finset A) (γ : A → ℝ) : SS S (-γ) = SS S γ := by
  ext a; simp [SS]

theorem merge_pos {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (D γ γ' : A → ℝ)
    (hγ : IsCircuit src dst γ) (hγ' : IsCircuit src dst γ')
    (hc : Conf D γ) (hc' : Conf D γ') (a : A) (ha : a ∈ S) (h1 : γ a = 1) (h2 : γ' a = 1) :
    ∃ π, IsCircuit src dst π ∧ Conf D π ∧ SS S γ ∪ SS S γ' ⊆ SS S π := by
  obtain ⟨π, hπ, hpos, hneg, hSeq⟩ := P225.main_thm src dst S hS γ γ' hγ hγ'
    ⟨a, by simp [SuppPosR, ha, h1, h2]⟩
  refine ⟨π, hπ, fun b => ⟨fun hb => ?_, fun hb => ?_⟩, ?_⟩
  · have hm : b ∈ SuppPosR π := by simp [SuppPosR, hb]
    have := hpos hm
    simp only [Finset.mem_union, SuppPosR, Finset.mem_filter, Finset.mem_univ, true_and] at this
    rcases this with h | h
    · rcases hγ.1 b with e | e | e
      · exact (hc b).1 e
      · rw [e] at h; exact absurd h (lt_irrefl 0)
      · rw [e] at h; norm_num at h
    · rcases hγ'.1 b with e | e | e
      · exact (hc' b).1 e
      · rw [e] at h; exact absurd h (lt_irrefl 0)
      · rw [e] at h; norm_num at h
  · have hm : b ∈ SuppNegR π := by simp [SuppNegR, hb]
    have := hneg hm
    simp only [Finset.mem_union, SuppNegR, Finset.mem_filter, Finset.mem_univ, true_and] at this
    rcases this with h | h
    · rcases hγ.1 b with e | e | e
      · rw [e] at h; norm_num at h
      · rw [e] at h; exact absurd h (lt_irrefl 0)
      · exact (hc b).2 e
    · rcases hγ'.1 b with e | e | e
      · rw [e] at h; norm_num at h
      · rw [e] at h; exact absurd h (lt_irrefl 0)
      · exact (hc' b).2 e
  · intro b hb
    simp only [SS, Finset.mem_union, Finset.mem_filter] at hb ⊢
    have key : b ∈ SuppPosR π ∩ S := by
      rw [hSeq]
      rcases hb with ⟨hbS, hb0⟩ | ⟨hbS, hb0⟩
      · have := circ_series src dst S hS γ hγ b hbS a ha hb0 (by rw [h1]; norm_num)
        rw [h1] at this
        simp [SuppPosR, hbS, this]
      · have := circ_series src dst S hS γ' hγ' b hbS a ha hb0 (by rw [h2]; norm_num)
        rw [h2] at this
        simp [SuppPosR, hbS, this]
    simp only [Finset.mem_inter, SuppPosR, Finset.mem_filter, Finset.mem_univ, true_and] at key
    exact ⟨key.2, key.1.ne'⟩

theorem merge {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (D γ γ' : A → ℝ)
    (hγ : IsCircuit src dst γ) (hγ' : IsCircuit src dst γ')
    (hc : Conf D γ) (hc' : Conf D γ') (a : A) (ha : a ∈ S) (h1 : γ a ≠ 0) (h2 : γ' a ≠ 0) :
    ∃ π, IsCircuit src dst π ∧ Conf D π ∧ SS S γ ∪ SS S γ' ⊆ SS S π := by
  rcases hγ.1 a with e1 | e1 | e1
  · rcases hγ'.1 a with e2 | e2 | e2
    · exact merge_pos src dst S hS D γ γ' hγ hγ' hc hc' a ha e1 e2
    · exact absurd e2 h2
    · exact absurd ((hc' a).2 e2) (not_lt.mpr ((hc a).1 e1).le)
  · exact absurd e1 h1
  · rcases hγ'.1 a with e2 | e2 | e2
    · exact absurd ((hc a).2 e1) (not_lt.mpr ((hc' a).1 e2).le)
    · exact absurd e2 h2
    · obtain ⟨π, hπ, hπc, hsub⟩ := merge_pos src dst S hS (-D) (-γ) (-γ')
        (circ_neg src dst γ hγ) (circ_neg src dst γ' hγ') (conf_neg hc) (conf_neg hc') a ha
        (by simp [e1]) (by simp [e2])
      refine ⟨-π, circ_neg src dst π hπ, ?_, ?_⟩
      · simpa only [neg_neg] using conf_neg hπc
      · rw [SS_neg, SS_neg] at hsub; rw [SS_neg]; exact hsub

theorem exists_max {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (D : A → ℝ) (h : ∃ γ, IsCircuit src dst γ ∧ Conf D γ) :
    ∃ γ, IsCircuit src dst γ ∧ Conf D γ ∧ ∀ γ', IsCircuit src dst γ' → Conf D γ' →
      (SS S γ').card ≤ (SS S γ).card := by
  classical
  obtain ⟨γ0, h0, hc0⟩ := h
  have hb : ∀ γ : A → ℝ, (SS S γ).card ≤ S.card := fun γ =>
    Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨γ, hγ, hcγ, hcard⟩ := Nat.findGreatest_spec
    (P := fun n => ∃ γ, IsCircuit src dst γ ∧ Conf D γ ∧ (SS S γ).card = n) (hb γ0)
    ⟨γ0, h0, hc0, rfl⟩
  refine ⟨γ, hγ, hcγ, fun γ' h' hc' => ?_⟩
  rw [hcard]
  exact Nat.le_findGreatest
    (P := fun n => ∃ γ, IsCircuit src dst γ ∧ Conf D γ ∧ (SS S γ).card = n) (hb γ')
    ⟨γ', h', hc', rfl⟩

theorem peel_of {A : Type*} [Fintype A] [DecidableEq A] (D γ : A → ℝ)
    (hv : ∀ b, γ b = 1 ∨ γ b = 0 ∨ γ b = -1) (hc : Conf D γ) (b1 : A) (hb1 : γ b1 ≠ 0) :
    ∃ l : ℝ, 0 < l ∧ (∀ b, Btw (l * γ b) (D b)) ∧
      (supp (D - l • γ)).card < (supp D).card := by
  classical
  have hval : ∀ b, γ b = 0 ∨ (γ b = 1 ∧ 0 < D b) ∨ (γ b = -1 ∧ D b < 0) := by
    intro b; rcases hv b with h | h | h
    · right; left; exact ⟨h, (hc b).1 h⟩
    · left; exact h
    · right; right; exact ⟨h, (hc b).2 h⟩
  have hdne : ∀ b, γ b ≠ 0 → D b ≠ 0 := by
    intro b hb
    rcases hval b with h | h | h
    · exact absurd h hb
    · exact h.2.ne'
    · exact h.2.ne
  set T := Finset.univ.filter (fun b => γ b ≠ 0) with hT
  have hTne : T.Nonempty := ⟨b1, by simp [hT, hb1]⟩
  obtain ⟨b0, hb0T, hmin⟩ := T.exists_min_image (fun b => |D b|) hTne
  have hb0 : γ b0 ≠ 0 := by simpa [hT] using hb0T
  refine ⟨|D b0|, abs_pos.mpr (hdne b0 hb0), ?_, ?_⟩
  · intro b
    rcases hval b with h | h | h
    · rw [h, mul_zero]; exact btw_zero _
    · have hm := hmin b (by simp [hT, h.1])
      rw [h.1, mul_one]; left
      rw [abs_of_pos h.2] at hm
      exact ⟨abs_nonneg _, hm⟩
    · have hm := hmin b (by simp [hT, h.1])
      rw [h.1]; right
      rw [abs_of_neg h.2] at hm
      constructor <;> linarith [abs_nonneg (D b0)]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨b0, ?_, ?_⟩
      · simp [supp, hdne b0 hb0]
      · simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rcases hval b0 with h | h | h
        · exact absurd h.symm (Ne.symm hb0)
        · rw [h.1, abs_of_pos h.2]; ring
        · rw [h.1, abs_of_neg h.2]; ring
    · intro b hbm
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hbm ⊢
      intro hdb
      apply hbm
      have : γ b = 0 := by
        by_contra hg; exact hdne b hg hdb
      rw [hdb, this]; ring

theorem conf_sub {A : Type*} (D γ γ' : A → ℝ) (l : ℝ) (hv : ∀ b, γ b = 1 ∨ γ b = 0 ∨ γ b = -1)
    (hc : Conf D γ) (hl : ∀ b, Btw (l * γ b) (D b)) (h : Conf (D - l • γ) γ') : Conf D γ' := by
  intro b
  have hb := hl b
  have h1 := (h b).1
  have h2 := (h b).2
  have c1 := (hc b).1
  have c2 := (hc b).2
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  unfold Btw at hb
  rcases hv b with e | e | e
  · have hD := c1 e
    rw [e] at hb h1 h2
    refine ⟨fun _ => hD, fun h' => ?_⟩
    have := h2 h'
    rcases hb with hb | hb <;> linarith
  · rw [e] at hb h1 h2
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have := h1 h'; linarith
    · have := h2 h'; linarith
  · have hD := c2 e
    rw [e] at hb h1 h2
    refine ⟨fun h' => ?_, fun _ => hD⟩
    have := h1 h'
    rcases hb with hb | hb <;> linarith

theorem btw_step (D l g m δ' : ℝ) (hg : g = 1 ∨ g = 0 ∨ g = -1) (hpos : g = 1 → 0 < D)
    (hneg : g = -1 → D < 0) (hl : Btw (l * g) D) (h1 : Btw δ' (D - l * g)) (hm0 : 0 ≤ m)
    (hml : m ≤ l) : Btw (m * g + δ') D := by
  unfold Btw at *
  rcases hg with rfl | rfl | rfl
  · have := hpos rfl
    rcases hl with hl | hl <;> rcases h1 with h1 | h1
    · left; constructor <;> linarith
    · left; constructor <;> linarith
    · exfalso; linarith
    · exfalso; linarith
  · rcases h1 with h1 | h1
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · have := hneg rfl
    rcases hl with hl | hl <;> rcases h1 with h1 | h1
    · exfalso; linarith
    · exfalso; linarith
    · right; constructor <;> linarith
    · right; constructor <;> linarith

theorem abs_step (D l g m δ' b : ℝ) (hg : g = 1 ∨ g = -1) (hpos : g = 1 → 0 < D)
    (hneg : g = -1 → D < 0) (hl : Btw (l * g) D) (h1 : Btw δ' (D - l * g))
    (habs : |δ'| = min |D - l * g| (b - m)) (hm : m = min l b) (hl0 : 0 < l) (hb0 : 0 ≤ b) :
    |m * g + δ'| = min |D| b := by
  unfold Btw at hl h1
  rcases hg with rfl | rfl
  · have hD := hpos rfl
    simp only [mul_one] at hl h1 habs ⊢
    have hlD : l ≤ D := by rcases hl with h | h <;> linarith
    have hδ0 : 0 ≤ δ' := by rcases h1 with h | h <;> linarith
    rw [abs_of_nonneg hδ0, abs_of_nonneg (by linarith : (0:ℝ) ≤ D - l)] at habs
    rw [abs_of_pos hD]
    rcases le_total l b with hlb | hlb
    · rw [min_eq_left hlb] at hm
      rw [hm] at habs ⊢
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ l + δ'), habs, min_sub_sub_right]; ring
    · rw [min_eq_right hlb] at hm
      rw [hm] at habs ⊢
      rw [sub_self, min_eq_right (by linarith : (0:ℝ) ≤ D - l)] at habs
      rw [habs, add_zero, abs_of_nonneg hb0, min_eq_right (by linarith : b ≤ D)]
  · have hD := hneg rfl
    have e1 : D - l * -1 = D + l := by ring
    have e2 : m * -1 + δ' = -(m - δ') := by ring
    rw [e1] at h1 habs
    rw [e2, abs_neg]
    have hlD : D + l ≤ 0 := by rcases hl with h | h <;> linarith
    have hδ0 : δ' ≤ 0 := by rcases h1 with h | h <;> linarith
    rw [abs_of_nonpos hδ0, abs_of_nonpos hlD] at habs
    rw [abs_of_neg hD]
    rcases le_total l b with hlb | hlb
    · rw [min_eq_left hlb] at hm
      rw [hm] at habs ⊢
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ l - δ')]
      have : -δ' = min (-D) b - l := by
        rw [habs, ← min_sub_sub_right]; congr 1; ring
      linarith
    · rw [min_eq_right hlb] at hm
      rw [hm] at habs ⊢
      rw [sub_self, min_eq_right (by linarith : (0:ℝ) ≤ -(D + l))] at habs
      have hδ : δ' = 0 := by linarith
      rw [hδ, sub_zero, abs_of_nonneg hb0, min_eq_right (by linarith : b ≤ -D)]

theorem trunc {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) :
    ∀ n, ∀ D β : A → ℝ, (supp D).card = n → (∀ v, Boundary src dst D v = 0) →
      (∀ a, 0 ≤ β a) →
      (∀ γ, IsCircuit src dst γ → Conf D γ → ∀ a ∈ SS S γ, ∀ b ∈ SS S γ, β a = β b) →
      ∃ δ : A → ℝ, (∀ v, Boundary src dst δ v = 0) ∧ (∀ b, Btw (δ b) (D b)) ∧
        ∀ a ∈ S, |δ a| = min |D a| (β a) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D β hn hD hβ hconst
  by_cases hz : ∃ a0, D a0 ≠ 0
  swap
  · push_neg at hz
    refine ⟨0, fun v => by simp [Boundary], fun b => by simpa using btw_zero (D b),
      fun a _ => ?_⟩
    simp [hz a, hβ a]
  obtain ⟨a0, ha0⟩ := hz
  obtain ⟨γ, hγ, hcγ, hmax⟩ := exists_max src dst S D (exists_circ src dst D hD a0 ha0)
  have hv := hγ.1
  obtain ⟨b1, hb1⟩ : ∃ b, γ b ≠ 0 := by
    obtain ⟨-, -, k, v, arcs, -, himg⟩ := hγ
    have : arcs 0 ∈ SuppPosR γ ∪ SuppNegR γ := by rw [← himg]; simp
    simp only [Finset.mem_union, SuppPosR, SuppNegR, Finset.mem_filter, Finset.mem_univ,
      true_and] at this
    refine ⟨arcs 0, ?_⟩
    rcases this with h | h
    · exact h.ne'
    · exact h.ne
  obtain ⟨l, hl0, hlb, hcard⟩ := peel_of D γ hv hcγ b1 hb1
  have hlam : ∀ γ', IsCircuit src dst γ' → Conf D γ' → ∀ a ∈ SS S γ', a ∈ SS S γ →
      SS S γ' ⊆ SS S γ := by
    intro γ' h' hc' a ha haγ
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    obtain ⟨π, hπ, hπc, hsub⟩ := merge src dst S hS D γ γ' hγ h' hcγ hc' a haS
      (Finset.mem_filter.mp haγ).2 (Finset.mem_filter.mp ha).2
    have hle : (SS S γ ∪ SS S γ').card ≤ (SS S γ).card :=
      (Finset.card_le_card hsub).trans (hmax π hπ hπc)
    have heq := Finset.eq_of_subset_of_card_le Finset.subset_union_left hle
    rw [heq]; exact Finset.subset_union_right
  obtain ⟨m, hm0, hml, hmeq⟩ : ∃ m : ℝ, 0 ≤ m ∧ m ≤ l ∧ ∀ a ∈ SS S γ, m = min l (β a) := by
    by_cases hne : (SS S γ).Nonempty
    · obtain ⟨a1, ha1⟩ := hne
      refine ⟨min l (β a1), le_min hl0.le (hβ a1), min_le_left _ _, fun a ha => ?_⟩
      rw [hconst γ hγ hcγ a ha a1 ha1]
    · exact ⟨l, hl0.le, le_refl _, fun a ha => absurd ⟨a, ha⟩ hne⟩
  set β' : A → ℝ := fun a => if a ∈ SS S γ then β a - m else β a with hβ'
  have hβ'0 : ∀ a, 0 ≤ β' a := by
    intro a; simp only [hβ']; split_ifs with h
    · rw [hmeq a h]; linarith [min_le_right l (β a)]
    · exact hβ a
  have hD' : ∀ v, Boundary src dst (D - l • γ) v = 0 := by
    intro v; rw [bdry_sub, bdry_smul, hD v, hγ.2.1 v]; ring
  have hconst' : ∀ γ'', IsCircuit src dst γ'' → Conf (D - l • γ) γ'' →
      ∀ a ∈ SS S γ'', ∀ b ∈ SS S γ'', β' a = β' b := by
    intro γ'' h'' hc'' a ha b hb
    have hcD := conf_sub D γ γ'' l hv hcγ hlb hc''
    have hab := hconst γ'' h'' hcD a ha b hb
    simp only [hβ']
    by_cases hia : a ∈ SS S γ
    · have hsub := hlam γ'' h'' hcD a ha hia
      rw [if_pos hia, if_pos (hsub hb), hab]
    · have hib : b ∉ SS S γ := by
        intro hib; exact hia (hlam γ'' h'' hcD b hb hib ha)
      rw [if_neg hia, if_neg hib, hab]
  obtain ⟨δ', hδ'b, hδ'btw, hδ'abs⟩ :=
    ih (supp (D - l • γ)).card (by rw [← hn]; exact hcard) (D - l • γ) β' rfl hD' hβ'0 hconst'
  refine ⟨m • γ + δ', fun v => ?_, fun b => ?_, fun a ha => ?_⟩
  · rw [bdry_add, bdry_smul, hγ.2.1 v, hδ'b v]; ring
  · have h1 := hδ'btw b
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hg : γ b = 1 ∨ γ b = 0 ∨ γ b = -1 := hv b
    exact btw_step (D b) l (γ b) m (δ' b) hg (hcγ b).1 (hcγ b).2 (hlb b) h1 hm0 hml
  · by_cases hia : a ∈ SS S γ
    · have hga : γ a ≠ 0 := (Finset.mem_filter.mp hia).2
      have hg : γ a = 1 ∨ γ a = -1 := by
        rcases hv a with e | e | e
        · left; exact e
        · exact absurd e hga
        · right; exact e
      have h2 := hδ'abs a ha
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hβ', if_pos hia] at h2
      have h1 := hδ'btw a
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact abs_step (D a) l (γ a) m (δ' a) (β a) hg (hcγ a).1 (hcγ a).2 (hlb a) h1 h2
        (hmeq a hia) hl0 (hβ a)
    · have hga : γ a = 0 := by
        by_contra h; exact hia (Finset.mem_filter.mpr ⟨ha, h⟩)
      have h2 := hδ'abs a ha
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hβ', if_neg hia, hga, mul_zero,
        sub_zero] at h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hga, mul_zero, zero_add]
      exact h2

theorem scal_S (x y δ P Q α M : ℝ) (hx : 0 ≤ x) (hxP : x ≤ P) (hy : 0 ≤ y) (hyQ : y ≤ Q)
    (hα : 0 ≤ α) (hM : |x - y| ≤ M) (hδ : Btw δ (x - y))
    (habs : |δ| = min |x - y| (if 0 < x - y then α else M)) :
    0 ≤ x - δ ∧ x - δ ≤ max (P - α) Q ∧ 0 ≤ y + δ ∧ y + δ ≤ min P (Q + α) := by
  unfold Btw at hδ
  rcases lt_trichotomy 0 (x - y) with h | h | h
  · rw [if_pos h, abs_of_pos h] at habs
    have hδ0 : 0 ≤ δ := by rcases hδ with hδ | hδ <;> linarith
    rw [abs_of_nonneg hδ0] at habs
    have h1 : δ ≤ x - y := habs ▸ min_le_left _ _
    have h2 : δ ≤ α := habs ▸ min_le_right _ _
    rcases min_choice (x - y) α with e | e
    · rw [e] at habs
      refine ⟨by linarith, le_max_iff.mpr (Or.inr (by linarith)), by linarith,
        le_min (by linarith) (by linarith)⟩
    · rw [e] at habs
      refine ⟨by linarith, le_max_iff.mpr (Or.inl (by linarith)), by linarith,
        le_min (by linarith) (by linarith)⟩
  · have hδ0 : δ = 0 := by
      rcases hδ with hδ | hδ
      · exact le_antisymm (by linarith) hδ.1
      · exact le_antisymm hδ.2 (by linarith)
    subst hδ0
    refine ⟨by linarith, le_max_iff.mpr (Or.inr (by linarith)), by linarith,
      le_min (by linarith) (by linarith)⟩
  · rw [if_neg (not_lt.mpr h.le), min_eq_left hM] at habs
    have hδ0 : δ ≤ 0 := by rcases hδ with hδ | hδ <;> linarith
    rw [abs_of_nonpos hδ0, abs_of_neg h] at habs
    refine ⟨by linarith, le_max_iff.mpr (Or.inr (by linarith)), by linarith,
      le_min (by linarith) (by linarith)⟩

theorem scal_off (x y δ C : ℝ) (hx : 0 ≤ x) (hxC : x ≤ C) (hy : 0 ≤ y) (hyC : y ≤ C)
    (hδ : Btw δ (x - y)) : 0 ≤ x - δ ∧ x - δ ≤ C ∧ 0 ≤ y + δ ∧ y + δ ≤ C := by
  unfold Btw at hδ
  rcases hδ with hδ | hδ <;> refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem C4 {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    TranslationSubmodularOn NonnegOrthant
      (fun cS : S → ℝ => -(FVal src dst w0 (ExtendOn c0 S cS))) := by
  classical
  intro p hp q hq α hα
  simp only [NonnegOrthant, Set.mem_setOf_eq] at hp hq
  have hcap : ∀ r : S → ℝ, 0 ≤ r → 0 ≤ ExtendOn c0 S r := by
    intro r hr a; unfold ExtendOn; split_ifs with h
    · exact hr _
    · exact hc0 a
  obtain ⟨ξ1, hf1, hF1, -⟩ := exists_opt src dst w0 _ (hcap p hp)
  obtain ⟨ξ2, hf2, hF2, -⟩ := exists_opt src dst w0 _ (hcap q hq)
  have hD : ∀ v, Boundary src dst (ξ1 - ξ2) v = 0 := fun v => by
    rw [bdry_sub, hf1.2 v, hf2.2 v]; ring
  have hM : ∀ b, |(ξ1 - ξ2) b| ≤ ∑ c, |(ξ1 - ξ2) c| := fun b =>
    Finset.single_le_sum (f := fun c => |(ξ1 - ξ2) c|) (fun c _ => abs_nonneg _)
      (Finset.mem_univ b)
  have hβ0 : ∀ a, 0 ≤ (fun a => if 0 < (ξ1 - ξ2) a then α else ∑ c, |(ξ1 - ξ2) c|) a := by
    intro a; simp only []; split_ifs
    · exact hα
    · exact (abs_nonneg _).trans (hM a)
  have hconst : ∀ γ, IsCircuit src dst γ → Conf (ξ1 - ξ2) γ → ∀ a ∈ SS S γ, ∀ b ∈ SS S γ,
      (fun a => if 0 < (ξ1 - ξ2) a then α else ∑ c, |(ξ1 - ξ2) c|) a =
      (fun a => if 0 < (ξ1 - ξ2) a then α else ∑ c, |(ξ1 - ξ2) c|) b := by
    intro γ hγ hc a ha b hb
    have haS := Finset.mem_filter.mp ha
    have hbS := Finset.mem_filter.mp hb
    have he := circ_series src dst S hS γ hγ a haS.1 b hbS.1 haS.2 hbS.2
    simp only []
    rcases hγ.1 a with e | e | e
    · have h1 := (hc a).1 e
      have h2 := (hc b).1 (he ▸ e)
      rw [if_pos h1, if_pos h2]
    · exact absurd e haS.2
    · have h1 := (hc a).2 e
      have h2 := (hc b).2 (he ▸ e)
      rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le)]
  obtain ⟨δ, hδb, hδbtw, hδabs⟩ := trunc src dst S hS _ (ξ1 - ξ2) _ rfl hD hβ0 hconst
  have key : ∀ a, (0 ≤ (ξ1 - δ) a ∧
        (ξ1 - δ) a ≤ ExtendOn c0 S ((p - α • (fun _ => (1:ℝ))) ⊔ q) a) ∧
      (0 ≤ (ξ2 + δ) a ∧ (ξ2 + δ) a ≤ ExtendOn c0 S (p ⊓ (q + α • (fun _ => (1:ℝ)))) a) := by
    intro a
    have h1 := hf1.1 a
    have h2 := hf2.1 a
    have hb := hδbtw a
    simp only [Pi.sub_apply] at hb
    simp only [Pi.sub_apply, Pi.add_apply]
    by_cases ha : a ∈ S
    · have hab := hδabs a ha
      simp only [Pi.sub_apply] at hab
      simp only [ExtendOn, dif_pos ha, Pi.sup_apply, Pi.inf_apply, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_one] at h1 h2 ⊢
      have := scal_S (ξ1 a) (ξ2 a) (δ a) (p ⟨a, ha⟩) (q ⟨a, ha⟩) α _ h1.1 h1.2 h2.1 h2.2 hα
        (hM a) hb hab
      exact ⟨⟨this.1, this.2.1⟩, this.2.2.1, this.2.2.2⟩
    · simp only [ExtendOn, dif_neg ha] at h1 h2 ⊢
      have := scal_off (ξ1 a) (ξ2 a) (δ a) (c0 a) h1.1 h1.2 h2.1 h2.2 hb
      exact ⟨⟨this.1, this.2.1⟩, this.2.2.1, this.2.2.2⟩
  have hfe1 : IsFeasibleCirc src dst (ExtendOn c0 S ((p - α • (fun _ => (1:ℝ))) ⊔ q))
      (ξ1 - δ) :=
    ⟨fun a => (key a).1, fun v => by rw [bdry_sub, hf1.2 v, hδb v]; ring⟩
  have hfe2 : IsFeasibleCirc src dst (ExtendOn c0 S (p ⊓ (q + α • (fun _ => (1:ℝ)))))
      (ξ2 + δ) :=
    ⟨fun a => (key a).2, fun v => by rw [bdry_add, hf2.2 v, hδb v]; ring⟩
  have e1 := le_F src dst w0 _ _ hfe1
  have e2 := le_F src dst w0 _ _ hfe2
  rw [dotProduct_sub] at e1
  rw [dotProduct_add] at e2
  show -(FVal src dst w0 (ExtendOn c0 S p)) + -(FVal src dst w0 (ExtendOn c0 S q)) ≥
    -(FVal src dst w0 (ExtendOn c0 S ((p - α • (fun _ => (1:ℝ))) ⊔ q))) +
    -(FVal src dst w0 (ExtendOn c0 S (p ⊓ (q + α • (fun _ => (1:ℝ))))))
  linarith


/-! ### C3: M-natural convexity of F in `w_S` -/

theorem circ_ne {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (γ : A → ℝ) (hγ : IsCircuit src dst γ) : ∃ b, γ b ≠ 0 := by
  obtain ⟨-, -, k, v, arcs, -, himg⟩ := hγ
  have : arcs 0 ∈ SuppPosR γ ∪ SuppNegR γ := by rw [← himg]; simp
  simp only [Finset.mem_union, SuppPosR, SuppNegR, Finset.mem_filter, Finset.mem_univ,
    true_and] at this
  refine ⟨arcs 0, ?_⟩
  rcases this with h | h
  · exact h.ne'
  · exact h.ne

theorem scal_T (x y δ t M : ℝ) (ht : 0 ≤ t) (hM : |x - y| ≤ M) (hδ : Btw δ (x - y))
    (habs : |δ| = min |x - y| (if 0 < x - y then t else M)) :
    x - δ = max y (x - t) ∧ y + δ = min x (y + t) := by
  unfold Btw at hδ
  rcases lt_trichotomy 0 (x - y) with h | h | h
  · rw [if_pos h, abs_of_pos h] at habs
    have hδ0 : 0 ≤ δ := by rcases hδ with hδ | hδ <;> linarith
    rw [abs_of_nonneg hδ0] at habs
    rcases min_choice (x - y) t with e | e
    · rw [e] at habs
      have : x - y ≤ t := min_eq_left_iff.mp e
      rw [max_eq_left (by linarith), min_eq_left (by linarith)]
      constructor <;> linarith
    · rw [e] at habs
      have : t ≤ x - y := min_eq_right_iff.mp e
      rw [max_eq_right (by linarith), min_eq_right (by linarith)]
      constructor <;> linarith
  · have hδ0 : δ = 0 := by
      rcases hδ with hδ | hδ
      · exact le_antisymm (by linarith) hδ.1
      · exact le_antisymm hδ.2 (by linarith)
    subst hδ0
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    constructor <;> linarith
  · rw [if_neg (not_lt.mpr h.le), min_eq_left hM] at habs
    have hδ0 : δ ≤ 0 := by rcases hδ with hδ | hδ <;> linarith
    rw [abs_of_nonpos hδ0, abs_of_neg h] at habs
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    constructor <;> linarith

theorem tpair {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (ξ1 ξ2 : A → ℝ)
    (h1 : ∀ v, Boundary src dst ξ1 v = 0) (h2 : ∀ v, Boundary src dst ξ2 v = 0) (t : ℝ)
    (ht : 0 ≤ t) :
    ∃ δ : A → ℝ, (∀ v, Boundary src dst δ v = 0) ∧ (∀ b, Btw (δ b) (ξ1 b - ξ2 b)) ∧
      ∀ a ∈ S, ξ1 a - δ a = max (ξ2 a) (ξ1 a - t) ∧ ξ2 a + δ a = min (ξ1 a) (ξ2 a + t) := by
  classical
  have hD : ∀ v, Boundary src dst (ξ1 - ξ2) v = 0 := fun v => by
    rw [bdry_sub, h1 v, h2 v]; ring
  have hM : ∀ b, |(ξ1 - ξ2) b| ≤ ∑ c, |(ξ1 - ξ2) c| := fun b =>
    Finset.single_le_sum (f := fun c => |(ξ1 - ξ2) c|) (fun c _ => abs_nonneg _)
      (Finset.mem_univ b)
  have hβ0 : ∀ a, 0 ≤ (fun a => if 0 < (ξ1 - ξ2) a then t else ∑ c, |(ξ1 - ξ2) c|) a := by
    intro a; simp only []; split_ifs
    · exact ht
    · exact (abs_nonneg _).trans (hM a)
  have hconst : ∀ γ, IsCircuit src dst γ → Conf (ξ1 - ξ2) γ → ∀ a ∈ SS S γ, ∀ b ∈ SS S γ,
      (fun a => if 0 < (ξ1 - ξ2) a then t else ∑ c, |(ξ1 - ξ2) c|) a =
      (fun a => if 0 < (ξ1 - ξ2) a then t else ∑ c, |(ξ1 - ξ2) c|) b := by
    intro γ hγ hc a ha b hb
    have haS := Finset.mem_filter.mp ha
    have hbS := Finset.mem_filter.mp hb
    have he := circ_series src dst S hS γ hγ a haS.1 b hbS.1 haS.2 hbS.2
    simp only []
    rcases hγ.1 a with e | e | e
    · have h1 := (hc a).1 e
      have h2 := (hc b).1 (he ▸ e)
      rw [if_pos h1, if_pos h2]
    · exact absurd e haS.2
    · have h1 := (hc a).2 e
      have h2 := (hc b).2 (he ▸ e)
      rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le)]
  obtain ⟨δ, hδb, hδbtw, hδabs⟩ := trunc src dst S hS _ (ξ1 - ξ2) _ rfl hD hβ0 hconst
  refine ⟨δ, hδb, fun b => hδbtw b, fun a ha => ?_⟩
  exact scal_T (ξ1 a) (ξ2 a) (δ a) t _ ht (hM a) (hδbtw a) (hδabs a ha)

theorem join_feas {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (c ξ1 ξ2 : A → ℝ)
    (h1 : IsFeasibleCirc src dst c ξ1) (h2 : IsFeasibleCirc src dst c ξ2) (t : ℝ)
    (ht : 0 ≤ t) :
    ∃ ζ1 ζ2 : A → ℝ, IsFeasibleCirc src dst c ζ1 ∧ IsFeasibleCirc src dst c ζ2 ∧
      ζ1 + ζ2 = ξ1 + ξ2 ∧
      ∀ a ∈ S, ζ1 a = max (ξ2 a) (ξ1 a - t) ∧ ζ2 a = min (ξ1 a) (ξ2 a + t) := by
  obtain ⟨δ, hδb, hδbtw, hδS⟩ := tpair src dst S hS ξ1 ξ2 h1.2 h2.2 t ht
  have hpt : ∀ a, 0 ≤ ξ1 a - δ a ∧ ξ1 a - δ a ≤ c a ∧ 0 ≤ ξ2 a + δ a ∧ ξ2 a + δ a ≤ c a :=
    fun a => scal_off (ξ1 a) (ξ2 a) (δ a) (c a) (h1.1 a).1 (h1.1 a).2 (h2.1 a).1 (h2.1 a).2
      (hδbtw a)
  refine ⟨ξ1 - δ, ξ2 + δ, ⟨fun a => ⟨(hpt a).1, (hpt a).2.1⟩, fun v => ?_⟩,
    ⟨fun a => ⟨(hpt a).2.2.1, (hpt a).2.2.2⟩, fun v => ?_⟩, ?_, fun a ha => hδS a ha⟩
  · rw [bdry_sub, h1.2 v, hδb v]; ring
  · rw [bdry_add, h2.2 v, hδb v]; ring
  · ext a; simp only [Pi.add_apply, Pi.sub_apply]; ring

theorem cyc_sign {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (m : A → ℝ) :
    ∀ n, ∀ D : A → ℝ, (supp D).card = n → (∀ v, Boundary src dst D v = 0) →
      (∀ γ, IsCircuit src dst γ → Conf D γ → dotProduct m γ ≤ 0) → dotProduct m D ≤ 0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hn hD hneg
  by_cases hz : ∃ a0, D a0 ≠ 0
  swap
  · push_neg at hz
    have : D = 0 := funext hz
    rw [this, dotProduct_zero]
  obtain ⟨a0, ha0⟩ := hz
  obtain ⟨γ, hγ, hcγ⟩ := exists_circ src dst D hD a0 ha0
  obtain ⟨b1, hb1⟩ := circ_ne src dst γ hγ
  obtain ⟨l, hl0, hlb, hcard⟩ := peel_of D γ hγ.1 hcγ b1 hb1
  have hD' : ∀ v, Boundary src dst (D - l • γ) v = 0 := by
    intro v; rw [bdry_sub, bdry_smul, hD v, hγ.2.1 v]; ring
  have h1 := ih _ (by rw [← hn]; exact hcard) (D - l • γ) rfl hD'
    (fun γ' h' hc' => hneg γ' h' (conf_sub D γ γ' l hγ.1 hcγ hlb hc'))
  have hm := hneg γ hγ hcγ
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1
  nlinarith

theorem gap {A : Type*} [Fintype A] [DecidableEq A] (X : A → ℝ) :
    ∃ g : ℝ, 0 < g ∧ ∀ γ : A → ℝ, (∀ b, γ b = 1 ∨ γ b = 0 ∨ γ b = -1) →
      0 < dotProduct X γ → g ≤ dotProduct X γ := by
  classical
  let T : Finset (A → ℝ) := Fintype.piFinset (fun _ => ({1, 0, -1} : Finset ℝ))
  let U : Finset ℝ := (T.image (fun γ => dotProduct X γ)).filter (fun r => 0 < r)
  have hmemU : ∀ γ : A → ℝ, (∀ b, γ b = 1 ∨ γ b = 0 ∨ γ b = -1) → 0 < dotProduct X γ →
      dotProduct X γ ∈ U := by
    intro γ hγ hpos
    simp only [U, T, Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset]
    refine ⟨⟨γ, fun b => ?_, rfl⟩, hpos⟩
    rcases hγ b with h | h | h <;> simp [h]
  by_cases hU : U.Nonempty
  · refine ⟨U.min' hU, ?_, fun γ hγ hpos => U.min'_le _ (hmemU γ hγ hpos)⟩
    have := U.min'_mem hU
    exact (Finset.mem_filter.mp this).2
  · refine ⟨1, one_pos, fun γ hγ hpos => absurd ⟨_, hmemU γ hγ hpos⟩ hU⟩

theorem stab {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (X E c : A → ℝ) :
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α, 0 ≤ α → α ≤ α0 → ∀ ξ', IsFeasibleCirc src dst c ξ' →
      (∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct (X - α • E) ζ ≤ dotProduct (X - α • E) ξ') →
      ∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct X ζ ≤ dotProduct X ξ' := by
  obtain ⟨g, hg, hgap⟩ := gap X
  have hN0 : 0 ≤ ∑ b, |E b| := Finset.sum_nonneg (fun b _ => abs_nonneg _)
  refine ⟨g / (∑ b, |E b| + 1), div_pos hg (by linarith), fun α hα hα0 ξ' hξ' hopt ζ hζ => ?_⟩
  have hα1 : α * (∑ b, |E b| + 1) ≤ g := (le_div_iff₀ (by linarith)).mp hα0
  rw [mul_add, mul_one] at hα1
  have hD : ∀ v, Boundary src dst (ζ - ξ') v = 0 := fun v => by
    rw [bdry_sub, hζ.2 v, hξ'.2 v]; ring
  have key := cyc_sign src dst X _ (ζ - ξ') rfl hD (fun γ hγ hcγ => ?_)
  · rw [dotProduct_sub] at key; linarith
  obtain ⟨b1, hb1⟩ := circ_ne src dst γ hγ
  obtain ⟨l, hl0, hlb, -⟩ := peel_of (ζ - ξ') γ hγ.1 hcγ b1 hb1
  have hfeas : IsFeasibleCirc src dst c (ξ' + l • γ) := by
    refine ⟨fun a => ?_, fun v => by rw [bdry_add, bdry_smul, hξ'.2 v, hγ.2.1 v]; ring⟩
    have h1 := hξ'.1 a
    have h2 := hζ.1 a
    have h3 := hlb a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h3 ⊢
    unfold Btw at h3
    rcases h3 with h3 | h3 <;> constructor <;> linarith
  have h1 := hopt _ hfeas
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
  have h2 : dotProduct (X - α • E) γ ≤ 0 := by
    by_contra hc; push_neg at hc; nlinarith [mul_pos hl0 hc]
  rw [sub_dotProduct, smul_dotProduct, smul_eq_mul] at h2
  have hEγ : dotProduct E γ ≤ ∑ b, |E b| := by
    unfold dotProduct
    apply Finset.sum_le_sum; intro b _
    rcases hγ.1 b with h | h | h <;> rw [h] <;> simp [le_abs_self, neg_le_abs]
  have hαE : α * dotProduct E γ ≤ α * ∑ b, |E b| := mul_le_mul_of_nonneg_left hEγ hα
  by_contra hcon
  push_neg at hcon
  have hgg := hgap γ hγ.1 hcon
  rcases hα.eq_or_lt with h0 | hpos
  · rw [← h0] at h2; simp at h2; linarith
  · linarith

theorem exists_lex {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) (hc : 0 ≤ c) (g : (A → ℝ) → ℝ) (hg : Continuous g) :
    ∃ xi, IsFeasibleCirc src dst c xi ∧
      (∀ xi', IsFeasibleCirc src dst c xi' → dotProduct w xi' ≤ dotProduct w xi) ∧
      ∀ xi', IsFeasibleCirc src dst c xi' → dotProduct w xi' = dotProduct w xi →
        g xi' ≤ g xi := by
  obtain ⟨x0, hx0, -, hall0⟩ := exists_opt src dst w c hc
  set K : Set (A → ℝ) := Set.Icc 0 c ∩ {x | ∀ v, Boundary src dst x v = 0} with hK
  have hcont : ∀ v, Continuous (fun x : A → ℝ => Boundary src dst x v) := by
    intro v; unfold Boundary
    exact (continuous_finsetSum _ fun a _ => continuous_apply a).sub
      (continuous_finsetSum _ fun a _ => continuous_apply a)
  have hclosed : IsClosed {x : A → ℝ | ∀ v, Boundary src dst x v = 0} := by
    have : {x : A → ℝ | ∀ v, Boundary src dst x v = 0} =
        ⋂ v, {x | Boundary src dst x v = 0} := by ext; simp
    rw [this]; exact isClosed_iInter fun v => isClosed_eq (hcont v) continuous_const
  have hKc : IsCompact K := isCompact_Icc.inter_right hclosed
  have hmem : ∀ x, x ∈ K ↔ IsFeasibleCirc src dst c x := by
    intro x
    simp only [hK, Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, IsFeasibleCirc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun a => ⟨h1 a, h2 a⟩, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨fun a => (h1 a).1, fun a => (h1 a).2⟩, h3⟩
  have hdc : Continuous (fun x : A → ℝ => dotProduct w x) := by
    unfold dotProduct
    exact continuous_finsetSum _ fun a _ => continuous_const.mul (continuous_apply a)
  set K' : Set (A → ℝ) := K ∩ {x | dotProduct w x = dotProduct w x0} with hK'
  have hK'c : IsCompact K' := hKc.inter_right (isClosed_eq hdc continuous_const)
  have hne : K'.Nonempty := ⟨x0, (hmem x0).2 hx0, rfl⟩
  obtain ⟨xi, ⟨hxiK, hxiv⟩, hmax⟩ := hK'c.exists_isMaxOn hne hg.continuousOn
  have hxi := (hmem xi).1 hxiK
  have hxiv' : dotProduct w xi = dotProduct w x0 := hxiv
  refine ⟨xi, hxi, fun xi' h => by rw [hxiv']; exact hall0 xi' h, fun xi' h he => ?_⟩
  exact hmax ⟨(hmem xi').2 h, he.trans hxiv'⟩

theorem F_eq {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c ξ : A → ℝ) (hc : 0 ≤ c) (hξ : IsFeasibleCirc src dst c ξ)
    (hopt : ∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct w ζ ≤ dotProduct w ξ) :
    FVal src dst w c = dotProduct w ξ := by
  obtain ⟨ξ0, h0, hF, hall⟩ := exists_opt src dst w c hc
  rw [hF]; exact le_antisymm (hopt ξ0 h0) (hall ξ hξ)

/-- normalized join of two optimal flows -/
theorem join_norm {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (X c ξ ζ : A → ℝ)
    (hξ : IsFeasibleCirc src dst c ξ) (hζ : IsFeasibleCirc src dst c ζ)
    (hopt : ∀ η, IsFeasibleCirc src dst c η → dotProduct X η ≤ dotProduct X ξ)
    (hval : dotProduct X ζ = dotProduct X ξ) (i : A) (hi : i ∈ S) :
    ∃ ζ1 ζ2, IsFeasibleCirc src dst c ζ1 ∧ dotProduct X ζ1 = dotProduct X ξ ∧
      IsFeasibleCirc src dst c ζ2 ∧ dotProduct X ζ2 = dotProduct X ξ ∧
      ζ1 i = min (ξ i) (ζ i) ∧ (∀ j ∈ S, ζ1 j - ζ1 i = max (ξ j - ξ i) (ζ j - ζ i)) ∧
      ζ2 i = max (ξ i) (ζ i) ∧ (∀ j ∈ S, ζ2 i - ζ2 j = max (ξ i - ξ j) (ζ i - ζ j)) := by
  have hopt' : ∀ (u v : A → ℝ), IsFeasibleCirc src dst c u → IsFeasibleCirc src dst c v →
      u + v = ξ + ζ → dotProduct X u = dotProduct X ξ ∧ dotProduct X v = dotProduct X ξ := by
    intro u v hu hv huv
    have e : dotProduct X u + dotProduct X v = dotProduct X ξ + dotProduct X ζ := by
      rw [← dotProduct_add, ← dotProduct_add, huv]
    have := hopt u hu
    have := hopt v hv
    constructor <;> linarith
  rcases le_total (ζ i) (ξ i) with h | h
  · obtain ⟨u, v, hu, hv, huv, hS'⟩ := join_feas src dst S hS c ξ ζ hξ hζ (ξ i - ζ i)
      (by linarith)
    obtain ⟨eu, ev⟩ := hopt' u v hu hv huv
    have hui := (hS' i hi).1
    have hvi := (hS' i hi).2
    refine ⟨u, v, hu, eu, hv, ev, ?_, fun j hj => ?_, ?_, fun j hj => ?_⟩
    · rw [hui, min_eq_right h]; rw [max_eq_left (by linarith)]
    · rw [(hS' j hj).1, hui, max_eq_left (by linarith : ζ i ≥ ξ i - (ξ i - ζ i))]
      rw [max_def, max_def]; split_ifs <;> linarith
    · rw [hvi, max_eq_left h, min_eq_left (by linarith)]
    · rw [(hS' j hj).2, hvi, min_eq_left (by linarith : ξ i ≤ ζ i + (ξ i - ζ i))]
      rw [max_def, min_def]; split_ifs <;> linarith
  · obtain ⟨u, v, hu, hv, huv, hS'⟩ := join_feas src dst S hS c ζ ξ hζ hξ (ζ i - ξ i)
      (by linarith)
    obtain ⟨eu, ev⟩ := hopt' u v hu hv (by rw [huv, add_comm])
    have hui := (hS' i hi).1
    have hvi := (hS' i hi).2
    refine ⟨u, v, hu, eu, hv, ev, ?_, fun j hj => ?_, ?_, fun j hj => ?_⟩
    · rw [hui, min_eq_left h, max_eq_left (by linarith)]
    · rw [(hS' j hj).1, hui, max_eq_left (by linarith : ξ i ≥ ζ i - (ζ i - ξ i))]
      rw [max_def, max_def]; split_ifs <;> linarith
    · rw [hvi, max_eq_right h, min_eq_left (by linarith)]
    · rw [(hS' j hj).2, hvi, min_eq_left (by linarith : ζ i ≤ ξ i + (ζ i - ξ i))]
      rw [max_def, min_def]; split_ifs <;> linarith

theorem ext_join {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (X c : A → ℝ)
    (hc : 0 ≤ c) (i : A) (hi : i ∈ S) :
    ∃ ξ, IsFeasibleCirc src dst c ξ ∧
      (∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct X ζ ≤ dotProduct X ξ) ∧
      ∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct X ζ = dotProduct X ξ →
        ξ i ≤ ζ i ∧ ∀ j ∈ S, ζ j - ζ i ≤ ξ j - ξ i := by
  obtain ⟨ξ, hξ, hopt, hmaxg⟩ := exists_lex src dst X c hc
    (fun ξ => ∑ j ∈ S, (ξ j - ξ i) - ξ i) (by fun_prop)
  refine ⟨ξ, hξ, hopt, fun ζ hζ hval => ?_⟩
  obtain ⟨u, -, hu, eu, -, -, hui, huj, -, -⟩ :=
    join_norm src dst S hS X c ξ ζ hξ hζ hopt hval i hi
  have hle := hmaxg u hu eu
  try simp only [] at hle
  rw [Finset.sum_congr rfl huj, hui] at hle
  have hsum : ∑ j ∈ S, (ξ j - ξ i) ≤ ∑ j ∈ S, max (ξ j - ξ i) (ζ j - ζ i) :=
    Finset.sum_le_sum (fun j _ => le_max_left _ _)
  have hmin := min_le_left (ξ i) (ζ i)
  constructor
  · by_contra h
    push_neg at h
    rw [min_eq_right h.le] at hle
    linarith
  · intro j hj
    by_contra h
    push_neg at h
    have hs := Finset.single_le_sum
      (f := fun k => max (ξ k - ξ i) (ζ k - ζ i) - (ξ k - ξ i))
      (fun k _ => sub_nonneg.mpr (le_max_left _ _)) hj
    try simp only [] at hs
    rw [Finset.sum_sub_distrib, max_eq_right h.le] at hs
    linarith

theorem ext_meet {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (X c : A → ℝ)
    (hc : 0 ≤ c) (i : A) (hi : i ∈ S) :
    ∃ ξ, IsFeasibleCirc src dst c ξ ∧
      (∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct X ζ ≤ dotProduct X ξ) ∧
      ∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct X ζ = dotProduct X ξ →
        ζ i ≤ ξ i ∧ ∀ j ∈ S, ζ i - ζ j ≤ ξ i - ξ j := by
  obtain ⟨ξ, hξ, hopt, hmaxg⟩ := exists_lex src dst X c hc
    (fun ξ => ∑ j ∈ S, (ξ i - ξ j) + ξ i) (by fun_prop)
  refine ⟨ξ, hξ, hopt, fun ζ hζ hval => ?_⟩
  obtain ⟨-, v, -, -, hv, ev, -, -, hvi, hvj⟩ :=
    join_norm src dst S hS X c ξ ζ hξ hζ hopt hval i hi
  have hle := hmaxg v hv ev
  try simp only [] at hle
  rw [Finset.sum_congr rfl hvj, hvi] at hle
  have hsum : ∑ j ∈ S, (ξ i - ξ j) ≤ ∑ j ∈ S, max (ξ i - ξ j) (ζ i - ζ j) :=
    Finset.sum_le_sum (fun j _ => le_max_left _ _)
  have hmax := le_max_left (ξ i) (ζ i)
  constructor
  · by_contra h
    push_neg at h
    rw [max_eq_right h.le] at hle
    linarith
  · intro j hj
    by_contra h
    push_neg at h
    have hs := Finset.single_le_sum
      (f := fun k => max (ξ i - ξ k) (ζ i - ζ k) - (ξ i - ξ k))
      (fun k _ => sub_nonneg.mpr (le_max_left _ _)) hj
    try simp only [] at hs
    rw [Finset.sum_sub_distrib, max_eq_right h.le] at hs
    linarith

theorem eps_gap {A : Type*} [DecidableEq A] (S : Finset A) (Δ : A → ℝ) (d0 r : ℝ)
    (hr : 0 < r) : ∃ ε, 0 < ε ∧ ε ≤ r ∧ ∀ a ∈ S, d0 < Δ a → d0 + ε ≤ Δ a := by
  induction S using Finset.induction_on with
  | empty => exact ⟨r, hr, le_refl _, by simp⟩
  | insert b S hb ih =>
    obtain ⟨ε, hε, hεr, hεS⟩ := ih
    by_cases hbd : d0 < Δ b
    · refine ⟨min ε (Δ b - d0), lt_min hε (by linarith), (min_le_left _ _).trans hεr, ?_⟩
      intro a ha hda
      rcases Finset.mem_insert.mp ha with h | ha
      · rw [h]; linarith [min_le_right ε (Δ b - d0)]
      · linarith [min_le_left ε (Δ b - d0), hεS a ha hda]
    · refine ⟨ε, hε, hεr, ?_⟩
      intro a ha hda
      rcases Finset.mem_insert.mp ha with h | ha
      · rw [h] at hda; exact absurd hda hbd
      · exact hεS a ha hda

theorem dot_ind {A : Type*} [Fintype A] [DecidableEq A] (k : A) (ξ : A → ℝ) :
    dotProduct (fun a => if a = k then (1:ℝ) else 0) ξ = ξ k := by
  unfold dotProduct; simp

theorem dot_E {A : Type*} [Fintype A] [DecidableEq A] (k l : A) (ξ : A → ℝ) :
    dotProduct (fun a => (if a = k then (1:ℝ) else 0) - (if a = l then (1:ℝ) else 0)) ξ =
      ξ k - ξ l := by
  unfold dotProduct; simp [sub_mul, Finset.sum_sub_distrib]

/-- the perturbed value, via stability -/
theorem perturb {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (X E c ξs : A → ℝ) (hc : 0 ≤ c) (hξs : IsFeasibleCirc src dst c ξs)
    (hopt : ∀ ζ, IsFeasibleCirc src dst c ζ → dotProduct X ζ ≤ dotProduct X ξs) :
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α, 0 ≤ α → α ≤ α0 → ∃ ξ', IsFeasibleCirc src dst c ξ' ∧
      dotProduct X ξ' = dotProduct X ξs ∧
      FVal src dst (X - α • E) c = dotProduct X ξs - α * dotProduct E ξ' := by
  obtain ⟨α0, hα0, hst⟩ := stab src dst X E c
  refine ⟨α0, hα0, fun α h0 h1 => ?_⟩
  obtain ⟨ξ', hξ', hF, hall⟩ := exists_opt src dst (X - α • E) c hc
  have hX := hst α h0 h1 ξ' hξ' hall
  have he : dotProduct X ξ' = dotProduct X ξs := le_antisymm (hopt ξ' hξ') (hX ξs hξs)
  refine ⟨ξ', hξ', he, ?_⟩
  rw [hF, sub_dotProduct, smul_dotProduct, smul_eq_mul, he]

theorem ext_eq_in {A : Type*} [DecidableEq A] (base : A → ℝ) (S : Finset A) (v : S → ℝ)
    (a : A) (ha : a ∈ S) : ExtendOn base S v a = v ⟨a, ha⟩ := by
  simp [ExtendOn, ha]

theorem ext_eq_out {A : Type*} [DecidableEq A] (base : A → ℝ) (S : Finset A) (v : S → ℝ)
    (a : A) (ha : a ∉ S) : ExtendOn base S v a = base a := by
  simp [ExtendOn, ha]

theorem C3 {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    MNatExchangeR (fun wS : S → ℝ => FVal src dst (ExtendOn w0 S wS) c0) := by
  classical
  intro x y i hi
  simp only [SuppPosR, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply] at hi
  obtain ⟨ξs, hξs, hoptx, hjx⟩ := ext_join src dst S hS (ExtendOn w0 S x) c0 hc0 (i : A) i.2
  obtain ⟨ξm, hξm, hopty, hjy⟩ := ext_meet src dst S hS (ExtendOn w0 S y) c0 hc0 (i : A) i.2
  have hFx := F_eq src dst _ c0 ξs hc0 hξs hoptx
  have hFy := F_eq src dst _ c0 ξm hc0 hξm hopty
  have hXi : ExtendOn w0 S x (i : A) = x i := by rw [ext_eq_in w0 S x _ i.2]
  have hYi : ExtendOn w0 S y (i : A) = y i := by rw [ext_eq_in w0 S y _ i.2]
  by_cases hcase : ξm (i : A) ≤ ξs (i : A)
  · -- j = 0
    right
    set Ei : A → ℝ := fun a => if a = (i : A) then (1:ℝ) else 0 with hEi
    obtain ⟨α1, hα1, hp1⟩ := perturb src dst (ExtendOn w0 S x) Ei c0 ξs hc0 hξs hoptx
    obtain ⟨α2, hα2, hp2⟩ := perturb src dst (ExtendOn w0 S y) (-Ei) c0 ξm hc0 hξm hopty
    refine ⟨min α1 α2, lt_min hα1 hα2, fun α h0 h1 => ?_⟩
    obtain ⟨ξ', hξ', e1, hF1⟩ := hp1 α h0 (h1.trans (min_le_left _ _))
    obtain ⟨η', hη', e2, hF2⟩ := hp2 α h0 (h1.trans (min_le_right _ _))
    have hx' : ExtendOn w0 S (x - α • CharVec i) = ExtendOn w0 S x - α • Ei := by
      funext a
      have e : x - α • CharVec i = x + ((-1) * α) • CharVec i := by
        rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
      rw [e, ext_cap1]; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hEi]; ring
    have hy' : ExtendOn w0 S (y + α • CharVec i) = ExtendOn w0 S y - α • (-Ei) := by
      funext a
      have e : y + α • CharVec i = y + (1 * α) • CharVec i := by rw [one_mul]
      rw [e, ext_cap1]; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hEi]
      ring
    show FVal src dst (ExtendOn w0 S x) c0 + FVal src dst (ExtendOn w0 S y) c0 ≥
      FVal src dst (ExtendOn w0 S (x - α • CharVec i)) c0 +
        FVal src dst (ExtendOn w0 S (y + α • CharVec i)) c0
    rw [hx', hy', hF1, hF2, hFx, hFy]
    have d1 : dotProduct Ei ξ' = ξ' (i : A) := by rw [hEi]; exact dot_ind _ _
    have d2 : dotProduct (-Ei) η' = - η' (i : A) := by rw [neg_dotProduct, hEi, dot_ind]
    rw [d1, d2]
    have k1 := (hjx ξ' hξ' e1).1
    have k2 := (hjy η' hη' e2).1
    have m1 : α * ξs (i : A) ≤ α * ξ' (i : A) := mul_le_mul_of_nonneg_left k1 h0
    have m2 : α * η' (i : A) ≤ α * ξm (i : A) := mul_le_mul_of_nonneg_left k2 h0
    have m3 : α * ξm (i : A) ≤ α * ξs (i : A) := mul_le_mul_of_nonneg_left hcase h0
    linarith
  · push_neg at hcase
    -- find j
    obtain ⟨j, hjS, hjneg, hjle⟩ : ∃ j ∈ S, ExtendOn w0 S x j < ExtendOn w0 S y j ∧
        ξs j - ξm j ≤ ξs (i : A) - ξm (i : A) := by
      by_contra hno
      push_neg at hno
      obtain ⟨ε, hε, hεr, hεS⟩ := eps_gap S (fun a => ξs a - ξm a) (ξs (i : A) - ξm (i : A))
        (ξm (i : A) - ξs (i : A)) (by linarith)
      obtain ⟨u, v, hu, hv, huv, hS'⟩ := join_feas src dst S hS c0 ξm ξs hξm hξs
        (ξm (i : A) - ξs (i : A) - ε) (by linarith)
      have b1 := hoptx u hu
      have b2 := hopty v hv
      have hv' : v = ξm + ξs - u := by rw [← huv]; abel
      rw [hv', dotProduct_sub, dotProduct_add] at b2
      have hpos : 0 < dotProduct (ExtendOn w0 S x - ExtendOn w0 S y) (u - ξs) := by
        have hterm : ∀ a, 0 ≤ (ExtendOn w0 S x - ExtendOn w0 S y) a * (u - ξs) a := by
          intro a
          simp only [Pi.sub_apply]
          by_cases ha : a ∈ S
          · rw [(hS' a ha).1]
            by_cases hle : ξs a - ξm a ≤ ξs (i : A) - ξm (i : A)
            · have hxy : ExtendOn w0 S y a ≤ ExtendOn w0 S x a := by
                by_contra hc; push_neg at hc; have := hno a ha hc; linarith
              apply mul_nonneg (by linarith)
              linarith [le_max_left (ξs a) (ξm a - (ξm (i : A) - ξs (i : A) - ε))]
            · push_neg at hle
              have := hεS a ha hle
              try simp only [] at this
              rw [max_eq_left (by linarith)]; simp
          · rw [ext_eq_out w0 S x a ha, ext_eq_out w0 S y a ha]; simp
        have hi_term : 0 < (ExtendOn w0 S x - ExtendOn w0 S y) (i : A) * (u - ξs) (i : A) := by
          simp only [Pi.sub_apply]
          rw [(hS' (i : A) i.2).1, hXi, hYi]
          rw [max_eq_right (by linarith)]
          apply mul_pos (by linarith); linarith
        unfold dotProduct
        exact lt_of_lt_of_le hi_term
          (Finset.single_le_sum (f := fun a => (ExtendOn w0 S x - ExtendOn w0 S y) a *
            (u - ξs) a) (fun a _ => hterm a) (Finset.mem_univ _))
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub] at hpos
      linarith
    left
    have hjS' : (⟨j, hjS⟩ : S) ∈ SuppNegR (x - y) := by
      simp only [SuppNegR, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply]
      rw [ext_eq_in w0 S x j hjS, ext_eq_in w0 S y j hjS] at hjneg
      linarith
    refine ⟨⟨j, hjS⟩, hjS', ?_⟩
    set E : A → ℝ := fun a => (if a = (i : A) then (1:ℝ) else 0) - (if a = j then (1:ℝ) else 0)
      with hE
    obtain ⟨α1, hα1, hp1⟩ := perturb src dst (ExtendOn w0 S x) E c0 ξs hc0 hξs hoptx
    obtain ⟨α2, hα2, hp2⟩ := perturb src dst (ExtendOn w0 S y) (-E) c0 ξm hc0 hξm hopty
    refine ⟨min α1 α2, lt_min hα1 hα2, fun α h0 h1 => ?_⟩
    obtain ⟨ξ', hξ', e1, hF1⟩ := hp1 α h0 (h1.trans (min_le_left _ _))
    obtain ⟨η', hη', e2, hF2⟩ := hp2 α h0 (h1.trans (min_le_right _ _))
    have hx' : ExtendOn w0 S (x - α • (CharVec i - CharVec ⟨j, hjS⟩)) =
        ExtendOn w0 S x - α • E := by
      funext a
      have e : x - α • (CharVec i - CharVec ⟨j, hjS⟩) =
          x + ((-1) * α) • (CharVec i - CharVec ⟨j, hjS⟩) := by
        rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
      rw [e, ext_cap2]; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hE]; ring
    have hy' : ExtendOn w0 S (y + α • (CharVec i - CharVec ⟨j, hjS⟩)) =
        ExtendOn w0 S y - α • (-E) := by
      funext a
      have e : y + α • (CharVec i - CharVec ⟨j, hjS⟩) =
          y + (1 * α) • (CharVec i - CharVec ⟨j, hjS⟩) := by rw [one_mul]
      rw [e, ext_cap2]; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hE]
      ring
    beta_reduce
    rw [hx', hy', hF1, hF2, hFx, hFy]
    have d1 : dotProduct E ξ' = ξ' (i : A) - ξ' j := by rw [hE]; exact dot_E _ _ _
    have d2 : dotProduct (-E) η' = -(η' (i : A) - η' j) := by rw [neg_dotProduct, hE, dot_E]
    rw [d1, d2]
    have k1 := (hjx ξ' hξ' e1).2 j hjS
    have k2 := (hjy η' hη' e2).2 j hjS
    have m1 : α * (ξs (i : A) - ξs j) ≤ α * (ξ' (i : A) - ξ' j) :=
      mul_le_mul_of_nonneg_left (by linarith) h0
    have m2 : α * (η' (i : A) - η' j) ≤ α * (ξm (i : A) - ξm j) :=
      mul_le_mul_of_nonneg_left k2 h0
    have m3 : α * (ξm (i : A) - ξm j) ≤ α * (ξs (i : A) - ξs j) :=
      mul_le_mul_of_nonneg_left (by linarith) h0
    linarith

end Q1d71

open DiscreteConvex.CombinatorialC in
theorem solution {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (P S : Finset A)
    (hP : IsParallelArcSet src dst P) (hS : IsSeriesArcSet src dst S) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    (TranslationSubmodular (fun wP : P → ℝ => FVal src dst (ExtendOn w0 P wP) c0) ∧
        MNatExchangeROn NonnegOrthant
          (fun cP : P → ℝ => -(FVal src dst w0 (ExtendOn c0 P cP)))) ∧
      (MNatExchangeR (fun wS : S → ℝ => FVal src dst (ExtendOn w0 S wS) c0) ∧
        TranslationSubmodularOn NonnegOrthant
          (fun cS : S → ℝ => -(FVal src dst w0 (ExtendOn c0 S cS)))) := by
  exact ⟨⟨Q1d71.C1 src dst P hP w0 c0 hc0, Q1d71.C2 src dst P hP w0 c0 hc0⟩,
    ⟨Q1d71.C3 src dst S hS w0 c0 hc0, Q1d71.C4 src dst S hS w0 c0 hc0⟩⟩

