-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.theorem_2_22_submodular_supermodular_in_parallel_series
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:45:35.063142+00:00
-- url     : https://prove2.me/submissions/237be98c-0a48-4080-8446-98cff1a4f1ad

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_FVal
import Definitions.Def_DiscreteConvex_CombinatorialC_NonnegOrthant
import Definitions.Def_DiscreteConvex_CombinatorialC_SubmodularOn
import Definitions.Def_DiscreteConvex_CombinatorialC_SupermodularOn
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_ExtendOn
import Definitions.Def_DiscreteConvex_CombinatorialC_Submodular
import Definitions.Def_DiscreteConvex_CombinatorialC_Supermodular



namespace DiscreteConvex.CombinatorialC

namespace T222Core

open Finset

variable {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]

noncomputable def inc (src dst : A → V) (w : V) (a : A) : ℝ :=
  (if src a = w then 1 else 0) - (if dst a = w then 1 else 0)

lemma boundary_eq (src dst : A → V) (pi : A → ℝ) (w : V) :
    Boundary src dst pi w = ∑ a, pi a * inc src dst w a := by
  unfold Boundary inc
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs <;> ring

def Circ (src dst : A → V) (x : A → ℝ) : Prop := ∀ w, Boundary src dst x w = 0

lemma circ_add {src dst : A → V} {x y : A → ℝ} (hx : Circ src dst x) (hy : Circ src dst y) :
    Circ src dst (x + y) := by
  intro w
  have h1 := hx w; have h2 := hy w
  rw [boundary_eq] at h1 h2 ⊢
  simp only [Pi.add_apply, add_mul, sum_add_distrib]; linarith

lemma circ_sub {src dst : A → V} {x y : A → ℝ} (hx : Circ src dst x) (hy : Circ src dst y) :
    Circ src dst (x - y) := by
  intro w
  have h1 := hx w; have h2 := hy w
  rw [boundary_eq] at h1 h2 ⊢
  simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]; linarith

lemma circ_smul {src dst : A → V} {x : A → ℝ} (c : ℝ) (hx : Circ src dst x) :
    Circ src dst (c • x) := by
  intro w
  have h1 := hx w
  rw [boundary_eq] at h1 ⊢
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, h1, mul_zero]

def Good (src dst : A → V) (π : A → ℝ) : Prop :=
  ∀ a b, a ≠ b → π a ≠ 0 → π b ≠ 0 →
    (IsParallelArcs src dst a b → π a * π b < 0) ∧ (IsSeriesArcs src dst a b → 0 < π a * π b)

def Conf (d π : A → ℝ) : Prop := ∀ a, π a ≠ 0 → 0 < π a * d a

def Out (src dst : A → V) (d : A → ℝ) (u : V) (a : A) : Prop :=
  (src a = u ∧ 0 < d a) ∨ (dst a = u ∧ d a < 0)

def Act (src dst : A → V) (d : A → ℝ) (u : V) : Prop :=
  ∃ a, (src a = u ∨ dst a = u) ∧ d a ≠ 0

noncomputable def head (src dst : A → V) (d : A → ℝ) (a : A) : V :=
  if 0 < d a then dst a else src a

lemma out_pos {src dst : A → V} {d : A → ℝ} {u : V} {a : A} (h : Out src dst d u a)
    (hp : 0 < d a) : src a = u := by
  rcases h with h | h
  · exact h.1
  · linarith [h.2]

lemma out_neg {src dst : A → V} {d : A → ℝ} {u : V} {a : A} (h : Out src dst d u a)
    (hp : ¬ 0 < d a) : dst a = u ∧ d a < 0 := by
  rcases h with h | h
  · exact absurd h.2 hp
  · exact h

lemma exists_cycle (src dst : A → V) (d : A → ℝ) (hd : Circ src dst d) (a0 : A)
    (ha0 : d a0 ≠ 0) :
    ∃ π : A → ℝ, Circ src dst π ∧ Good src dst π ∧ Conf d π ∧ ∃ a, π a ≠ 0 := by
  classical
  have hout : ∀ u, Act src dst d u → ∃ a, Out src dst d u a := by
    rintro u ⟨a, ha, hda⟩
    by_contra hno
    have h1 : ∀ b, src b = u → d b ≤ 0 := fun b hb => by
      by_contra h; exact hno ⟨b, Or.inl ⟨hb, lt_of_not_ge h⟩⟩
    have h2 : ∀ b, dst b = u → 0 ≤ d b := fun b hb => by
      by_contra h; exact hno ⟨b, Or.inr ⟨hb, lt_of_not_ge h⟩⟩
    have hB := hd u
    unfold Boundary at hB
    have s1 : ∑ b ∈ univ.filter (fun b => src b = u), d b ≤ 0 :=
      sum_nonpos (fun b hb => h1 b (mem_filter.1 hb).2)
    have s2 : 0 ≤ ∑ b ∈ univ.filter (fun b => dst b = u), d b :=
      sum_nonneg (fun b hb => h2 b (mem_filter.1 hb).2)
    have e1 : ∑ b ∈ univ.filter (fun b => src b = u), d b = 0 := by linarith
    have e2 : ∑ b ∈ univ.filter (fun b => dst b = u), d b = 0 := by linarith
    rcases ha with ha | ha
    · exact hda ((sum_eq_zero_iff_of_nonpos (fun b hb => h1 b (mem_filter.1 hb).2)).1 e1 a
        (mem_filter.2 ⟨mem_univ _, ha⟩))
    · exact hda ((sum_eq_zero_iff_of_nonneg (fun b hb => h2 b (mem_filter.1 hb).2)).1 e2 a
        (mem_filter.2 ⟨mem_univ _, ha⟩))
  have hhead : ∀ u a, Out src dst d u a → Act src dst d (head src dst d a) := by
    intro u a h
    refine ⟨a, ?_, ?_⟩
    · unfold head; split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rcases h with h | h
      · exact h.2.ne'
      · exact h.2.ne
  obtain ⟨g, hg⟩ : ∃ g : V → A, ∀ u, Act src dst d u → Out src dst d u (g u) :=
    ⟨fun u => if h : Act src dst d u then (hout u h).choose else a0,
     fun u h => by simp only [dif_pos h]; exact (hout u h).choose_spec⟩
  set f : V → V := fun u => head src dst d (g u) with hf
  have hiter : ∀ n, Act src dst d (f^[n] (src a0)) := by
    intro n
    induction n with
    | zero => exact ⟨a0, Or.inl rfl, ha0⟩
    | succ n ih => rw [Function.iterate_succ_apply']; exact hhead _ _ (hg _ ih)
  obtain ⟨x, y, hxy, hfxy⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] (src a0))
  have hex : ∃ j, ∃ i < j, f^[i] (src a0) = f^[j] (src a0) := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h, hfxy⟩
    · exact ⟨x, y, h, hfxy.symm⟩
  obtain ⟨i, hij, hfij⟩ := Nat.find_spec hex
  have hmin : ∀ j' < Nat.find hex, ¬ ∃ i < j', f^[i] (src a0) = f^[j'] (src a0) :=
    fun j' hj' => Nat.find_min hex hj'
  generalize Nat.find hex = j at hij hfij hmin
  obtain ⟨k, hk⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
  subst hk
  set v : Fin (k + 1) → V := fun t => f^[i + t.val] (src a0) with hv
  have hvinj : Function.Injective v := by
    intro s t hst
    simp only [hv] at hst
    by_contra hne
    have hs := s.isLt; have ht := t.isLt
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact hmin (i + t.val) (by omega) ⟨i + s.val, by omega, hst⟩
    · exact hmin (i + s.val) (by omega) ⟨i + t.val, by omega, hst.symm⟩
  have hvsucc : ∀ t : Fin (k + 1), v (t + 1) = f (v t) := by
    intro t
    simp only [hv]
    rw [← Function.iterate_succ_apply' f]
    rw [Fin.val_add_one]
    split_ifs with ht
    · rw [add_zero, hfij]
      congr 1
      simp [ht]; try omega
    · rfl
  set arcs : Fin (k + 1) → A := fun t => g (v t) with harcs
  have hOutT : ∀ t, Out src dst d (v t) (arcs t) := fun t => hg _ (hiter _)
  have hheadT : ∀ t, head src dst d (arcs t) = v (t + 1) := fun t => (hvsucc t).symm
  have harcinj : Function.Injective arcs := by
    intro s t h
    apply hvinj
    by_cases hp : 0 < d (arcs s)
    · have hs := out_pos (hOutT s) hp
      have ht := out_pos (hOutT t) (h ▸ hp)
      rw [← hs, ← ht, h]
    · have hs := (out_neg (hOutT s) hp).1
      have ht := (out_neg (hOutT t) (h ▸ hp)).1
      rw [← hs, ← ht, h]
  have hends : ∀ t, src (arcs t) = (if 0 < d (arcs t) then v t else v (t + 1)) ∧
      dst (arcs t) = (if 0 < d (arcs t) then v (t + 1) else v t) := by
    intro t
    have hh := hheadT t
    unfold head at hh
    by_cases hp : 0 < d (arcs t)
    · simp only [if_pos hp] at hh ⊢
      exact ⟨out_pos (hOutT t) hp, hh⟩
    · simp only [if_neg hp] at hh ⊢
      exact ⟨hh, (out_neg (hOutT t) hp).1⟩
  have hcyc : IsSimpleCycle src dst k v arcs := by
    refine ⟨hvinj, fun t => ?_⟩
    obtain ⟨h1, h2⟩ := hends t
    by_cases hp : 0 < d (arcs t)
    · simp only [if_pos hp] at h1 h2; rw [h1, h2]
    · simp only [if_neg hp] at h1 h2; rw [h1, h2, Finset.pair_comm]
  set σ : Fin (k + 1) → ℝ := fun t => if 0 < d (arcs t) then 1 else -1 with hσ
  set π : A → ℝ := fun a => ∑ t, if arcs t = a then σ t else 0 with hπ
  have hπarc : ∀ t, π (arcs t) = σ t := by
    intro t
    simp only [hπ, harcinj.eq_iff]
    rw [Finset.sum_ite_eq' Finset.univ t]; simp
  have hπcases : ∀ a, π a = 0 ∨ ∃ t, arcs t = a := by
    intro a
    by_cases h : ∃ t, arcs t = a
    · exact Or.inr h
    · push_neg at h
      left
      exact sum_eq_zero (fun t _ => if_neg (h t))
  have hdne : ∀ t, d (arcs t) ≠ 0 := by
    intro t
    rcases hOutT t with h | h
    · exact h.2.ne'
    · exact h.2.ne
  refine ⟨π, ?_, ?_, ?_, ⟨arcs 0, ?_⟩⟩
  · intro w
    rw [boundary_eq]
    have e1 : ∑ a, π a * inc src dst w a = ∑ t, σ t * inc src dst w (arcs t) := by
      simp only [hπ, sum_mul, ite_mul, zero_mul]
      rw [sum_comm]
      refine sum_congr rfl (fun t _ => ?_)
      rw [Finset.sum_ite_eq Finset.univ (arcs t)]; simp
    have e2 : ∀ t, σ t * inc src dst w (arcs t) =
        (if v t = w then 1 else 0) - (if v (t + 1) = w then 1 else 0) := by
      intro t
      obtain ⟨h1, h2⟩ := hends t
      simp only [hσ, inc]
      by_cases hp : 0 < d (arcs t)
      · simp only [if_pos hp] at h1 h2 ⊢; rw [h1, h2]; ring
      · simp only [if_neg hp] at h1 h2 ⊢; rw [h1, h2]; ring
    rw [e1, sum_congr rfl (fun t _ => e2 t), sum_sub_distrib]
    have e3 : ∑ t : Fin (k + 1), (if v (t + 1) = w then (1 : ℝ) else 0) =
        ∑ t : Fin (k + 1), (if v t = w then (1 : ℝ) else 0) :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin (k + 1))) (fun t => if v t = w then (1 : ℝ) else 0)
    rw [e3, sub_self]
  · intro a b hab ha hb
    rcases hπcases a with h | ⟨t, rfl⟩
    · exact absurd h ha
    rcases hπcases b with h | ⟨s, rfl⟩
    · exact absurd h hb
    have hts : t ≠ s := fun h => hab (by rw [h])
    have hsucc : ∀ r : Fin (k + 1), r + 1 ≠ r := by
      intro r hr
      have h1 : (1 : Fin (k + 1)) = 0 := by
        have := congrArg (fun z => z - r) hr; simpa using this
      have hk0 : k = 0 := by have := Fin.one_eq_zero_iff.mp h1; omega
      subst hk0
      exact hts (Fin.ext (by have := t.isLt; have := s.isLt; omega))
    have hfwd : ∀ r : Fin (k + 1), (Forward src v arcs r ↔ 0 < d (arcs r)) := by
      intro r
      obtain ⟨h1, -⟩ := hends r
      unfold Forward
      by_cases hp : 0 < d (arcs r)
      · simp only [if_pos hp] at h1; simp [h1, hp]
      · simp only [if_neg hp] at h1
        simp only [h1, hp, iff_false]
        intro h; exact hsucc r (hvinj h)
    rw [hπarc, hπarc]
    constructor
    · intro hpar
      have := hpar k v arcs hcyc t s rfl rfl
      rw [hfwd, hfwd] at this
      simp only [hσ]
      by_cases h1 : 0 < d (arcs t) <;> by_cases h2 : 0 < d (arcs s) <;>
        simp only [h1, h2, if_true, if_false, not_true, not_false_iff, iff_true, iff_false, true_iff, false_iff] at this ⊢ <;> norm_num at this ⊢
    · intro hser
      have := hser k v arcs hcyc t s rfl rfl
      rw [hfwd, hfwd] at this
      simp only [hσ]
      by_cases h1 : 0 < d (arcs t) <;> by_cases h2 : 0 < d (arcs s) <;>
        simp only [h1, h2, if_true, if_false, not_true, not_false_iff, iff_true, iff_false, true_iff, false_iff] at this ⊢ <;> norm_num at this ⊢
  · intro a ha
    rcases hπcases a with h | ⟨t, rfl⟩
    · exact absurd h ha
    rw [hπarc]
    simp only [hσ]
    by_cases hp : 0 < d (arcs t)
    · simp only [if_pos hp]; linarith
    · simp only [if_neg hp]
      have := hdne t
      have : d (arcs t) < 0 := lt_of_le_of_ne (not_lt.mp hp) this
      linarith
  · rw [hπarc]; simp only [hσ]; split_ifs <;> norm_num

def Box (x ξ η : A → ℝ) : Prop := ∀ a, ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ x a = η a + u * (ξ a - η a)

def Gd (src dst : A → V) (π : A → ℝ) : Prop := Circ src dst π ∧ Good src dst π

def DecompConcl (src dst : A → V) (K : (A → ℝ) → Prop) (ξ η x : A → ℝ) : Prop :=
  Circ src dst x ∧ Box x ξ η ∧
    (∀ a, (∀ π, Gd src dst π → Conf (ξ - η) π → π a ≠ 0 → K π) → x a = ξ a) ∧
    (∀ a, (∀ π, Gd src dst π → Conf (ξ - η) π → π a ≠ 0 → ¬ K π) → x a = η a) ∧
    (∀ r s : A → ℝ, (∀ π, Gd src dst π → Conf (ξ - η) π →
        (K π → dotProduct s π ≤ dotProduct r π) ∧ (¬ K π → dotProduct s π ≤ 0)) →
      dotProduct s (ξ - η) ≤ dotProduct r (x - η))

lemma decomp_base (src dst : A → V) (K : (A → ℝ) → Prop) (ξ η : A → ℝ)
    (hξ : Circ src dst ξ) (hall : ∀ a, ξ a = η a) : DecompConcl src dst K ξ η ξ := by
  have h0 : ξ - η = 0 := funext (fun a => by simp [hall a])
  refine ⟨hξ, fun a => ⟨0, le_rfl, zero_le_one, by simp [hall a]⟩, fun a _ => rfl,
    fun a _ => hall a, fun r s _ => ?_⟩
  rw [h0]; simp

lemma decomp (src dst : A → V) (K : (A → ℝ) → Prop) : ∀ n : ℕ, ∀ ξ η : A → ℝ,
    (univ.filter (fun a => ξ a - η a ≠ 0)).card ≤ n → Circ src dst ξ → Circ src dst η →
    ∃ x, DecompConcl src dst K ξ η x := by
  classical
  intro n
  induction n with
  | zero =>
    intro ξ η hcard hξ hη
    refine ⟨ξ, decomp_base src dst K ξ η hξ (fun a => ?_)⟩
    by_contra h
    have : 0 < (univ.filter (fun a => ξ a - η a ≠ 0)).card :=
      card_pos.2 ⟨a, mem_filter.2 ⟨mem_univ _, sub_ne_zero.2 h⟩⟩
    omega
  | succ n ih =>
    intro ξ η hcard hξ hη
    by_cases hall : ∀ a, ξ a = η a
    · exact ⟨ξ, decomp_base src dst K ξ η hξ hall⟩
    push_neg at hall
    obtain ⟨a0, ha0⟩ := hall
    obtain ⟨π, hπc, hπg, hπconf, a1, ha1⟩ :=
      exists_cycle src dst (ξ - η) (circ_sub hξ hη) a0 (by simpa [sub_ne_zero] using ha0)
    have hdef : ∀ a, (ξ - η) a = ξ a - η a := fun a => rfl
    set T := univ.filter (fun a => π a ≠ 0) with hT
    have hTne : T.Nonempty := ⟨a1, by simp [T, ha1]⟩
    obtain ⟨a2, ha2T, ha2⟩ := exists_mem_eq_inf' hTne (fun a => (ξ a - η a) / π a)
    set lam := T.inf' hTne (fun a => (ξ a - η a) / π a) with hlam
    have hratio : ∀ a, π a ≠ 0 → 0 < (ξ a - η a) / π a := by
      intro a ha
      have := hπconf a ha
      rw [hdef] at this
      rcases lt_or_gt_of_ne ha with h | h
      · exact div_pos_of_neg_of_neg (by nlinarith) h
      · exact div_pos (by nlinarith) h
    have ha2π : π a2 ≠ 0 := (mem_filter.1 ha2T).2
    have hlam_pos : 0 < lam := by rw [ha2]; exact hratio a2 ha2π
    have hlam_le : ∀ a, π a ≠ 0 → lam ≤ (ξ a - η a) / π a :=
      fun a ha => inf'_le _ (by simp [T, ha])
    have hscale : ∀ a, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (ξ a - η a) - lam * π a = t * (ξ a - η a) := by
      intro a
      by_cases ha : π a = 0
      · exact ⟨1, zero_le_one, le_rfl, by rw [ha]; ring⟩
      · have hc := hπconf a ha
        rw [hdef] at hc
        have hd : ξ a - η a ≠ 0 := by intro h; rw [h, mul_zero] at hc; exact lt_irrefl _ hc
        have hr := hratio a ha
        have hl := hlam_le a ha
        have key : lam * π a / (ξ a - η a) = lam / ((ξ a - η a) / π a) := by
          field_simp
        refine ⟨1 - lam * π a / (ξ a - η a), ?_, ?_, ?_⟩
        · rw [key]; have : lam / ((ξ a - η a) / π a) ≤ 1 := div_le_one_of_le₀ hl hr.le
          linarith
        · rw [key]; have : 0 ≤ lam / ((ξ a - η a) / π a) := div_nonneg hlam_pos.le hr.le
          linarith
        · field_simp
    set ξ1 : A → ℝ := ξ - lam • π with hξ1
    have hξ1a : ∀ a, ξ1 a = ξ a - lam * π a := fun a => rfl
    have hsub : univ.filter (fun a => ξ1 a - η a ≠ 0) ⊆ univ.filter (fun a => ξ a - η a ≠ 0) := by
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      obtain ⟨t, -, -, ht⟩ := hscale a
      intro h; apply ha; rw [hξ1a]
      have : ξ a - lam * π a - η a = (ξ a - η a) - lam * π a := by ring
      rw [this, ht, h, mul_zero]
    have hlt : (univ.filter (fun a => ξ1 a - η a ≠ 0)).card <
        (univ.filter (fun a => ξ a - η a ≠ 0)).card := by
      apply card_lt_card
      rw [ssubset_iff_of_subset hsub]
      refine ⟨a2, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        intro h
        have hc := hπconf a2 ha2π
        rw [hdef, h, mul_zero] at hc
        exact lt_irrefl _ hc
      · simp only [mem_filter, mem_univ, true_and, not_not]
        rw [hξ1a, ha2]
        field_simp
        ring
    have hξ1c : Circ src dst ξ1 := circ_sub hξ (circ_smul lam hπc)
    obtain ⟨x, hxc, hxb, hxall, hxnone, hxval⟩ := ih ξ1 η (by omega) hξ1c hη
    have hconf_tr : ∀ π', Conf (ξ1 - η) π' → Conf (ξ - η) π' := by
      intro π' h a ha
      have h1 := h a ha
      obtain ⟨t, ht0, ht1, hte⟩ := hscale a
      have e : (ξ1 - η) a = t * (ξ a - η a) := by
        rw [← hte]; simp only [Pi.sub_apply, hξ1a]; ring
      rw [e] at h1
      rw [hdef]
      by_contra hneg
      push_neg at hneg
      nlinarith
    have hdot : ξ1 - η = (ξ - η) - lam • π := by
      ext a; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hξ1a]; ring
    by_cases hK : K π
    · refine ⟨x + lam • π, circ_add hxc (circ_smul lam hπc), ?_, ?_, ?_, ?_⟩
      · intro a
        obtain ⟨u, hu0, hu1, hu⟩ := hxb a
        obtain ⟨t, ht0, ht1, hte⟩ := hscale a
        refine ⟨u * t + (1 - t), by nlinarith, by nlinarith, ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hu, hξ1a]
        linear_combination (u - 1) * hte
      · intro a H
        have := hxall a (fun π' g c h => H π' g (hconf_tr π' c) h)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [this, hξ1a]; ring
      · intro a H
        have := hxnone a (fun π' g c h => H π' g (hconf_tr π' c) h)
        have hπa : π a = 0 := by
          by_contra hne
          exact H π ⟨hπc, hπg⟩ hπconf hne hK
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [this, hπa]; ring
      · intro r s H
        have h1 := hxval r s (fun π' g c => H π' g (hconf_tr π' c))
        have h2 := (H π ⟨hπc, hπg⟩ hπconf).1 hK
        rw [hdot, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1
        have e : x + lam • π - η = (x - η) + lam • π := by abel
        rw [e, dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith
    · refine ⟨x, hxc, ?_, ?_, ?_, ?_⟩
      · intro a
        obtain ⟨u, hu0, hu1, hu⟩ := hxb a
        obtain ⟨t, ht0, ht1, hte⟩ := hscale a
        refine ⟨u * t, by nlinarith, by nlinarith, ?_⟩
        rw [hu, hξ1a]
        linear_combination u * hte
      · intro a H
        have := hxall a (fun π' g c h => H π' g (hconf_tr π' c) h)
        have hπa : π a = 0 := by
          by_contra hne
          exact hK (H π ⟨hπc, hπg⟩ hπconf hne)
        rw [this, hξ1a, hπa]; ring
      · intro a H
        exact hxnone a (fun π' g c h => H π' g (hconf_tr π' c) h)
      · intro r s H
        have h1 := hxval r s (fun π' g c => H π' g (hconf_tr π' c))
        have h2 := (H π ⟨hπc, hπg⟩ hπconf).2 hK
        rw [hdot, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1
        nlinarith

lemma fval_bdd (src dst : A → V) (w c : A → ℝ) :
    BddAbove {t : ℝ | ∃ xi : A → ℝ, IsFeasibleCirc src dst c xi ∧ t = dotProduct w xi} := by
  refine ⟨∑ a, |w a| * |c a|, ?_⟩
  rintro t ⟨xi, ⟨hb, -⟩, rfl⟩
  unfold dotProduct
  apply sum_le_sum
  intro a _
  obtain ⟨h0, h1⟩ := hb a
  calc w a * xi a ≤ |w a * xi a| := le_abs_self _
    _ = |w a| * |xi a| := abs_mul _ _
    _ ≤ |w a| * |c a| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _)

lemma le_fval (src dst : A → V) (w c xi : A → ℝ) (h : IsFeasibleCirc src dst c xi) :
    dotProduct w xi ≤ FVal src dst w c :=
  le_csSup (fval_bdd src dst w c) ⟨xi, h, rfl⟩

lemma fval_le (src dst : A → V) (w c : A → ℝ) (hc : 0 ≤ c) (M : ℝ)
    (h : ∀ xi, IsFeasibleCirc src dst c xi → dotProduct w xi ≤ M) : FVal src dst w c ≤ M := by
  apply csSup_le
  · exact ⟨_, 0, ⟨fun a => ⟨le_rfl, hc a⟩, fun v => by simp [Boundary]⟩, rfl⟩
  · rintro t ⟨xi, h1, rfl⟩; exact h xi h1

lemma fval_add_le (src dst : A → V) (w1 w2 c1 c2 : A → ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (M : ℝ) (h : ∀ ξ η, IsFeasibleCirc src dst c1 ξ → IsFeasibleCirc src dst c2 η →
      dotProduct w1 ξ + dotProduct w2 η ≤ M) :
    FVal src dst w1 c1 + FVal src dst w2 c2 ≤ M := by
  have h1 : ∀ η, IsFeasibleCirc src dst c2 η → FVal src dst w1 c1 ≤ M - dotProduct w2 η :=
    fun η hη => fval_le src dst w1 c1 hc1 _ (fun ξ hξ => by linarith [h ξ η hξ hη])
  have h2 : FVal src dst w2 c2 ≤ M - FVal src dst w1 c1 :=
    fval_le src dst w2 c2 hc2 _ (fun η hη => by linarith [h1 η hη])
  linarith

/-- the second circulation of the exchanged pair -/
lemma box_y {x ξ η : A → ℝ} (hb : Box x ξ η) (a : A) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ x a = η a + u * (ξ a - η a) ∧
      (ξ + η - x) a = ξ a - u * (ξ a - η a) := by
  obtain ⟨u, h0, h1, h⟩ := hb a
  exact ⟨u, h0, h1, h, by simp only [Pi.add_apply, Pi.sub_apply]; rw [h]; ring⟩

lemma feas_xy (src dst : A → V) (ξ η x c1 c2 : A → ℝ) (hξ : IsFeasibleCirc src dst c1 ξ)
    (hη : IsFeasibleCirc src dst c2 η) (hxc : Circ src dst x) (hb : Box x ξ η)
    (C1 C2 : A → ℝ)
    (hx : ∀ a, x a ≤ C1 a) (hy : ∀ a, (ξ + η - x) a ≤ C2 a) :
    IsFeasibleCirc src dst C1 x ∧ IsFeasibleCirc src dst C2 (ξ + η - x) := by
  refine ⟨⟨fun a => ⟨?_, hx a⟩, hxc⟩, ⟨fun a => ⟨?_, hy a⟩, circ_sub (circ_add hξ.2 hη.2) hxc⟩⟩
  · obtain ⟨u, h0, h1, h, -⟩ := box_y hb a
    have := hξ.1 a; have := hη.1 a
    rw [h]; nlinarith
  · obtain ⟨u, h0, h1, -, h⟩ := box_y hb a
    have := hξ.1 a; have := hη.1 a
    rw [h]; nlinarith

lemma w_sub (src dst : A → V) (W1 W2 c : A → ℝ) (hc : 0 ≤ c)
    (hpar : ∀ a b, W2 a < W1 a → W1 b < W2 b → IsParallelArcs src dst a b) :
    FVal src dst (W1 ⊔ W2) c + FVal src dst (W1 ⊓ W2) c ≤
      FVal src dst W1 c + FVal src dst W2 c := by
  classical
  apply fval_add_le src dst _ _ _ _ hc hc
  intro ξ η hξ hη
  obtain ⟨x, hxc, hxb, -, -, hxv⟩ := decomp src dst (fun π => ∃ a, 0 < π a ∧ W2 a < W1 a) _ ξ η
    le_rfl hξ.2 hη.2
  obtain ⟨hfx, hfy⟩ := feas_xy src dst ξ η x c c hξ hη hxc hxb c c
    (fun a => by obtain ⟨u, h0, h1, h, -⟩ := box_y hxb a; have := hξ.1 a; have := hη.1 a
                 rw [h]; nlinarith)
    (fun a => by obtain ⟨u, h0, h1, -, h⟩ := box_y hxb a; have := hξ.1 a; have := hη.1 a
                 rw [h]; nlinarith)
  have h1 := le_fval src dst W1 c x hfx
  have h2 := le_fval src dst W2 c _ hfy
  have hv := hxv (W1 - W2) (fun a => max (W1 a - W2 a) 0) (by
    intro π ⟨hπc, hπg⟩ hconf
    constructor
    · rintro ⟨a0, hpa0, hr0⟩
      unfold dotProduct
      apply sum_le_sum
      intro a _
      simp only [Pi.sub_apply]
      try dsimp only
      rcases le_or_gt 0 (W1 a - W2 a) with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h.le]
        by_cases hpa : 0 < π a
        · exfalso
          have hne : a0 ≠ a := by rintro rfl; linarith
          have := (hπg a0 a hne hpa0.ne' hpa.ne').1 (hpar a0 a hr0 (by linarith))
          nlinarith
        · nlinarith
    · intro hnK
      unfold dotProduct
      apply sum_nonpos
      intro a _
      dsimp only
      by_cases hpa : 0 < π a
      · have : W1 a - W2 a ≤ 0 := by
          by_contra h; exact hnK ⟨a, hpa, by linarith⟩
        rw [max_eq_right this]; simp
      · exact mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _) (not_lt.mp hpa))
  have key : ∀ a, (W1 ⊔ W2) a * ξ a + (W1 ⊓ W2) a * η a - W1 a * x a - W2 a * (ξ + η - x) a =
      max (W1 a - W2 a) 0 * (ξ - η) a - (W1 - W2) a * (x - η) a := by
    intro a
    simp only [Pi.sup_apply, Pi.inf_apply, Pi.add_apply, Pi.sub_apply]
    rcases le_total (W1 a) (W2 a) with h | h
    · rw [sup_eq_right.2 h, inf_eq_left.2 h, max_eq_right (by linarith)]; ring
    · rw [sup_eq_left.2 h, inf_eq_right.2 h, max_eq_left (by linarith)]; ring
  have hsum := sum_congr rfl (fun a (_ : a ∈ (univ : Finset A)) => key a)
  simp only [sum_sub_distrib, sum_add_distrib] at hsum
  unfold dotProduct at *
  linarith

lemma w_super (src dst : A → V) (W1 W2 c : A → ℝ) (hc : 0 ≤ c)
    (hser : ∀ a b, W2 a < W1 a → W1 b < W2 b → IsSeriesArcs src dst a b) :
    FVal src dst W1 c + FVal src dst W2 c ≤
      FVal src dst (W1 ⊔ W2) c + FVal src dst (W1 ⊓ W2) c := by
  classical
  apply fval_add_le src dst _ _ _ _ hc hc
  intro ξ η hξ hη
  obtain ⟨x, hxc, hxb, -, -, hxv⟩ := decomp src dst (fun π => ∃ a, 0 < π a ∧ W2 a < W1 a) _ ξ η
    le_rfl hξ.2 hη.2
  obtain ⟨hfx, hfy⟩ := feas_xy src dst ξ η x c c hξ hη hxc hxb c c
    (fun a => by obtain ⟨u, h0, h1, h, -⟩ := box_y hxb a; have := hξ.1 a; have := hη.1 a
                 rw [h]; nlinarith)
    (fun a => by obtain ⟨u, h0, h1, -, h⟩ := box_y hxb a; have := hξ.1 a; have := hη.1 a
                 rw [h]; nlinarith)
  have h1 := le_fval src dst (W1 ⊔ W2) c x hfx
  have h2 := le_fval src dst (W1 ⊓ W2) c _ hfy
  have hv := hxv (fun a => |W1 a - W2 a|) (fun a => max (W1 a - W2 a) 0) (by
    intro π ⟨hπc, hπg⟩ hconf
    constructor
    · rintro ⟨a0, hpa0, hr0⟩
      unfold dotProduct
      apply sum_le_sum
      intro a _
      dsimp only
      rcases le_or_gt 0 (W1 a - W2 a) with h | h
      · rw [max_eq_left h, abs_of_nonneg h]
      · rw [max_eq_right h.le, abs_of_neg h]
        by_cases hpa : π a < 0
        · exfalso
          have hne : a0 ≠ a := by rintro rfl; linarith
          have := (hπg a0 a hne hpa0.ne' hpa.ne).2 (hser a0 a hr0 (by linarith))
          nlinarith
        · nlinarith
    · intro hnK
      unfold dotProduct
      apply sum_nonpos
      intro a _
      dsimp only
      by_cases hpa : 0 < π a
      · have : W1 a - W2 a ≤ 0 := by
          by_contra h; exact hnK ⟨a, hpa, by linarith⟩
        rw [max_eq_right this]; simp
      · exact mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _) (not_lt.mp hpa))
  have key : ∀ a, W1 a * ξ a + W2 a * η a - (W1 ⊔ W2) a * x a - (W1 ⊓ W2) a * (ξ + η - x) a =
      max (W1 a - W2 a) 0 * (ξ - η) a - |W1 a - W2 a| * (x - η) a := by
    intro a
    simp only [Pi.sup_apply, Pi.inf_apply, Pi.add_apply, Pi.sub_apply]
    rcases le_total (W1 a) (W2 a) with h | h
    · rw [sup_eq_right.2 h, inf_eq_left.2 h, max_eq_right (by linarith),
        abs_of_nonpos (by linarith)]; ring
    · rw [sup_eq_left.2 h, inf_eq_right.2 h, max_eq_left (by linarith),
        abs_of_nonneg (by linarith)]; ring
  have hsum := sum_congr rfl (fun a (_ : a ∈ (univ : Finset A)) => key a)
  simp only [sum_sub_distrib, sum_add_distrib] at hsum
  unfold dotProduct at *
  linarith

lemma dot_xy (w ξ η x : A → ℝ) :
    dotProduct w x + dotProduct w (ξ + η - x) = dotProduct w ξ + dotProduct w η := by
  rw [dotProduct_sub, dotProduct_add]; ring

lemma c_sub (src dst : A → V) (w C1 C2 : A → ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hpar : ∀ a b, C2 a < C1 a → C1 b < C2 b → IsParallelArcs src dst a b) :
    FVal src dst w (C1 ⊔ C2) + FVal src dst w (C1 ⊓ C2) ≤
      FVal src dst w C1 + FVal src dst w C2 := by
  classical
  apply fval_add_le src dst _ _ _ _ (le_sup_of_le_left hC1) (le_inf hC1 hC2)
  intro ξ η hξ hη
  obtain ⟨x, hxc, hxb, hxall, hxnone, -⟩ :=
    decomp src dst (fun π => ∃ a, 0 < π a ∧ C2 a < C1 a) _ ξ η le_rfl hξ.2 hη.2
  have hξb : ∀ a, 0 ≤ ξ a ∧ ξ a ≤ max (C1 a) (C2 a) := fun a => hξ.1 a
  have hηb : ∀ a, 0 ≤ η a ∧ η a ≤ min (C1 a) (C2 a) := fun a => hη.1 a
  have HX : ∀ a, x a ≤ C1 a := by
    intro a
    obtain ⟨u, h0, h1, h, -⟩ := box_y hxb a
    have := hξb a; have := hηb a
    rcases le_or_gt (C2 a) (C1 a) with hc | hc
    · rw [max_eq_left hc] at *; rw [min_eq_right hc] at *; rw [h]; nlinarith
    · rw [max_eq_right hc.le] at *; rw [min_eq_left hc.le] at *
      rcases le_or_gt (ξ a) (η a) with hd | hd
      · rw [h]; nlinarith
      · rw [hxnone a (by
          rintro π ⟨-, hπg⟩ hconf hπa ⟨a0, hpa0, hr0⟩
          have hc' := hconf a hπa
          simp only [Pi.sub_apply] at hc'
          have hpa : 0 < π a := by nlinarith
          have hne : a0 ≠ a := by rintro rfl; linarith
          have := (hπg a0 a hne hpa0.ne' hπa).1 (hpar a0 a hr0 hc)
          nlinarith)]
        linarith
  have HY : ∀ a, (ξ + η - x) a ≤ C2 a := by
    intro a
    obtain ⟨u, h0, h1, -, h⟩ := box_y hxb a
    have := hξb a; have := hηb a
    rcases le_or_gt (C1 a) (C2 a) with hc | hc
    · rw [max_eq_right hc] at *; rw [min_eq_left hc] at *; rw [h]; nlinarith
    · rw [max_eq_left hc.le] at *; rw [min_eq_right hc.le] at *
      rcases le_or_gt (ξ a) (η a) with hd | hd
      · rw [h]; nlinarith
      · have hx := hxall a (by
          intro π _ hconf hπa
          have hc' := hconf a hπa
          simp only [Pi.sub_apply] at hc'
          exact ⟨a, by nlinarith, hc⟩)
        simp only [Pi.add_apply, Pi.sub_apply, hx]
        linarith
  obtain ⟨hfx, hfy⟩ := feas_xy src dst ξ η x _ _ hξ hη hxc hxb C1 C2 HX HY
  have h1 := le_fval src dst w C1 x hfx
  have h2 := le_fval src dst w C2 _ hfy
  linarith [dot_xy w ξ η x]

lemma c_super (src dst : A → V) (w C1 C2 : A → ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hser : ∀ a b, C2 a < C1 a → C1 b < C2 b → IsSeriesArcs src dst a b) :
    FVal src dst w C1 + FVal src dst w C2 ≤
      FVal src dst w (C1 ⊔ C2) + FVal src dst w (C1 ⊓ C2) := by
  classical
  apply fval_add_le src dst _ _ _ _ hC1 hC2
  intro ξ η hξ hη
  obtain ⟨x, hxc, hxb, hxall, hxnone, -⟩ :=
    decomp src dst (fun π => ∃ a, 0 < π a ∧ C2 a < C1 a) _ ξ η le_rfl hξ.2 hη.2
  have hξb : ∀ a, 0 ≤ ξ a ∧ ξ a ≤ C1 a := fun a => hξ.1 a
  have hηb : ∀ a, 0 ≤ η a ∧ η a ≤ C2 a := fun a => hη.1 a
  have HX : ∀ a, x a ≤ (C1 ⊔ C2) a := by
    intro a
    obtain ⟨u, h0, h1, h, -⟩ := box_y hxb a
    have := hξb a; have := hηb a
    show x a ≤ max (C1 a) (C2 a)
    rw [h]
    rcases le_total (C1 a) (C2 a) with hc | hc
    · rw [max_eq_right hc]; nlinarith
    · rw [max_eq_left hc]; nlinarith
  have HY : ∀ a, (ξ + η - x) a ≤ (C1 ⊓ C2) a := by
    intro a
    obtain ⟨u, h0, h1, -, h⟩ := box_y hxb a
    have := hξb a; have := hηb a
    show (ξ + η - x) a ≤ min (C1 a) (C2 a)
    rcases lt_trichotomy (C1 a) (C2 a) with hc | hc | hc
    · rw [min_eq_left hc.le]
      rcases le_or_gt (η a) (ξ a) with hd | hd
      · rw [h]; nlinarith
      · rw [show (ξ + η - x) a = ξ a + η a - x a from rfl, hxnone a (by
          rintro π ⟨-, hπg⟩ hconf hπa ⟨a0, hpa0, hr0⟩
          have hc' := hconf a hπa
          simp only [Pi.sub_apply] at hc'
          have hpa : π a < 0 := by nlinarith
          have hne : a0 ≠ a := by rintro rfl; linarith
          have := (hπg a0 a hne hpa0.ne' hπa).2 (hser a0 a hr0 hc)
          nlinarith)]
        linarith
    · rw [← hc, min_self, h]; nlinarith
    · rw [min_eq_right hc.le]
      rcases le_or_gt (ξ a) (η a) with hd | hd
      · rw [h]; nlinarith
      · have hx := hxall a (by
          intro π _ hconf hπa
          have hc' := hconf a hπa
          simp only [Pi.sub_apply] at hc'
          exact ⟨a, by nlinarith, hc⟩)
        simp only [Pi.add_apply, Pi.sub_apply, hx]
        linarith
  obtain ⟨hfx, hfy⟩ := feas_xy src dst ξ η x _ _ hξ hη hxc hxb (C1 ⊔ C2) (C1 ⊓ C2) HX HY
  have h1 := le_fval src dst w _ x hfx
  have h2 := le_fval src dst w _ _ hfy
  linarith [dot_xy w ξ η x]

end T222Core

open T222Core in
theorem t222_core {V A : Type*} [Fintype A]
    [Fintype V] [DecidableEq V] [DecidableEq A] (src dst : A → V) (P S : Finset A)
    (hP : IsParallelArcSet src dst P) (hS : IsSeriesArcSet src dst S) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    (Submodular (fun wP : P → ℝ => FVal src dst (ExtendOn w0 P wP) c0) ∧
        SubmodularOn NonnegOrthant (fun cP : P → ℝ => FVal src dst w0 (ExtendOn c0 P cP))) ∧
      (Supermodular (fun wS : S → ℝ => FVal src dst (ExtendOn w0 S wS) c0) ∧
        SupermodularOn NonnegOrthant
          (fun cS : S → ℝ => FVal src dst w0 (ExtendOn c0 S cS))) := by
  have extsup : ∀ (b : A → ℝ) (X : Finset A) (p q : X → ℝ),
      ExtendOn b X (p ⊔ q) = ExtendOn b X p ⊔ ExtendOn b X q := by
    intro b X p q; funext a; unfold ExtendOn
    by_cases h : a ∈ X <;> simp [h]
  have extinf : ∀ (b : A → ℝ) (X : Finset A) (p q : X → ℝ),
      ExtendOn b X (p ⊓ q) = ExtendOn b X p ⊓ ExtendOn b X q := by
    intro b X p q; funext a; unfold ExtendOn
    by_cases h : a ∈ X <;> simp [h]
  have extnn : ∀ (b : A → ℝ) (X : Finset A) (p : X → ℝ), 0 ≤ b → 0 ≤ p →
      0 ≤ ExtendOn b X p := by
    intro b X p hb hp a; unfold ExtendOn
    split_ifs
    · exact hp _
    · exact hb a
  have extmem : ∀ (b : A → ℝ) (X : Finset A) (p q : X → ℝ) (a : A),
      ExtendOn b X p a ≠ ExtendOn b X q a → a ∈ X := by
    intro b X p q a h
    by_contra ha
    unfold ExtendOn at h
    simp [ha] at h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro p q
    show _ + _ ≥ _ + _
    dsimp only
    rw [extsup, extinf]
    refine w_sub src dst _ _ c0 hc0 (fun a b ha hb => ?_)
    exact hP a (extmem _ _ _ _ a ha.ne') b (extmem _ _ _ _ b hb.ne)
      (by rintro rfl; linarith)
  · intro p hp q hq
    show _ + _ ≥ _ + _
    dsimp only
    rw [extsup, extinf]
    refine c_sub src dst w0 _ _ (extnn _ _ _ hc0 hp) (extnn _ _ _ hc0 hq) (fun a b ha hb => ?_)
    exact hP a (extmem _ _ _ _ a ha.ne') b (extmem _ _ _ _ b hb.ne)
      (by rintro rfl; linarith)
  · intro p q
    show _ + _ ≤ _ + _
    dsimp only
    rw [extsup, extinf]
    refine w_super src dst _ _ c0 hc0 (fun a b ha hb => ?_)
    exact hS a (extmem _ _ _ _ a ha.ne') b (extmem _ _ _ _ b hb.ne)
      (by rintro rfl; linarith)
  · intro p hp q hq
    show _ + _ ≤ _ + _
    dsimp only
    rw [extsup, extinf]
    refine c_super src dst w0 _ _ (extnn _ _ _ hc0 hp) (extnn _ _ _ hc0 hq) (fun a b ha hb => ?_)
    exact hS a (extmem _ _ _ _ a ha.ne') b (extmem _ _ _ _ b hb.ne)
      (by rintro rfl; linarith)

end DiscreteConvex.CombinatorialC

open DiscreteConvex.CombinatorialC


theorem solution {V A : Type*} [Fintype A]
    [Fintype V] [DecidableEq V] [DecidableEq A] (src dst : A → V) (P S : Finset A)
    (hP : IsParallelArcSet src dst P) (hS : IsSeriesArcSet src dst S) (w0 c0 : A → ℝ)
    (hc0 : 0 ≤ c0) :
    (Submodular (fun wP : P → ℝ => FVal src dst (ExtendOn w0 P wP) c0) ∧
        SubmodularOn NonnegOrthant (fun cP : P → ℝ => FVal src dst w0 (ExtendOn c0 P cP))) ∧
      (Supermodular (fun wS : S → ℝ => FVal src dst (ExtendOn w0 S wS) c0) ∧
        SupermodularOn NonnegOrthant
          (fun cS : S → ℝ => FVal src dst w0 (ExtendOn c0 S cS))) := by
  exact t222_core src dst P S hP hS w0 c0 hc0
