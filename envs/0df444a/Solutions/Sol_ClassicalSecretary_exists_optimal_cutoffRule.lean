-- Prove2me | solution 1 for ClassicalSecretary.exists_optimal_cutoffRule
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T15:51:04.828393+00:00
-- url     : https://prove2.me/submissions/1b0d9342-e1a8-4863-b269-cb9008b6549c

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

set_option autoImplicit false

open Finset Filter Topology

namespace ClassicalSecretary.SecCore
open ClassicalSecretary

variable {n : ℕ}

/-- The space of Lehmer codes. -/
def A (n : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun j : Fin n => range (j.val + 1)

lemma mem_A {a : Fin n → ℕ} : a ∈ A n ↔ ∀ j, a j ≤ j.val := by
  simp [A, Fintype.mem_piFinset]

lemma card_A : #(A n) = Nat.factorial n := by
  rw [A, Fintype.card_piFinset]
  simp only [card_range]
  rw [Fin.prod_univ_eq_prod_range (fun i => i + 1) n, prod_range_add_one_eq_factorial]

lemma card_lt_val (σ : Equiv.Perm (Fin n)) (v : Fin n) : #{k | σ k < v} = v.val := by
  have : #{k | σ k < v} = #(Iio v) := by
    apply Finset.card_equiv σ
    intro k; simp
  rw [this, Fin.card_Iio]

lemma relRank_le (σ : Equiv.Perm (Fin n)) (j : Fin n) : relRank σ j ≤ j.val := by
  unfold relRank
  calc #{k | k < j ∧ σ k < σ j} ≤ #(Iio j) := by
        apply card_le_card; intro k; simp only [mem_filter, mem_univ, true_and, mem_Iio]; tauto
    _ = j.val := Fin.card_Iio j

lemma relRank_eq_iff (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    relRank σ j = j.val ↔ ∀ k, k < j → σ k < σ j := by
  unfold relRank
  have hsub : ({k | k < j ∧ σ k < σ j} : Finset (Fin n)) ⊆ Iio j := by
    intro k; simp only [mem_filter, mem_univ, true_and, mem_Iio]; tauto
  constructor
  · intro h k hk
    have := eq_of_subset_of_card_le hsub (by rw [Fin.card_Iio, h])
    have hk' : k ∈ Iio j := by simpa using hk
    rw [← this] at hk'
    simp only [mem_filter, mem_univ, true_and] at hk'
    exact hk'.2
  · intro h
    have : ({k | k < j ∧ σ k < σ j} : Finset (Fin n)) = Iio j := by
      ext k; simp only [mem_filter, mem_univ, true_and, mem_Iio]
      exact ⟨fun h' => h'.1, fun hk => ⟨hk, h k hk⟩⟩
    rw [this, Fin.card_Iio]

lemma lt_iff_card (σ : Equiv.Perm (Fin n)) {k m : Fin n} (hkm : k < m) :
    σ k < σ m ↔ #{l | l < m ∧ σ l < σ k} < relRank σ m := by
  unfold relRank
  constructor
  · intro h
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨k, by simp [hkm, h], by simp⟩
    · intro l; simp only [mem_filter, mem_univ, true_and]
      exact fun h' => ⟨h'.1, h'.2.trans h⟩
  · intro h
    by_contra hc
    have hne : σ m ≠ σ k := fun e => (ne_of_lt hkm) (σ.injective e).symm
    have hlt : σ m < σ k := lt_of_le_of_ne (not_lt.mp hc) hne
    have : #{l | l < m ∧ σ l < σ m} ≤ #{l | l < m ∧ σ l < σ k} := by
      apply card_le_card; intro l; simp only [mem_filter, mem_univ, true_and]
      exact fun h' => ⟨h'.1, h'.2.trans hlt⟩
    omega

lemma lt_iff_not_lt_of_ne (σ : Equiv.Perm (Fin n)) {j k : Fin n} (hjk : j ≠ k) :
    σ j < σ k ↔ ¬ σ k < σ j := by
  have : σ j ≠ σ k := fun e => hjk (σ.injective e)
  constructor
  · intro h h'; exact lt_asymm h h'
  · intro h; exact lt_of_le_of_ne (not_lt.mp h) this

lemma relRank_injective : Function.Injective (fun σ : Equiv.Perm (Fin n) => relRank σ) := by
  intro σ τ hστ
  have hst : ∀ j, relRank σ j = relRank τ j := fun j => congrFun hστ j
  have key : ∀ m : ℕ, ∀ j k : Fin n, j.val < m → k.val < m → (σ j < σ k ↔ τ j < τ k) := by
    intro m
    induction m with
    | zero => intro j k hj; omega
    | succ m ih =>
      have half : ∀ j k : Fin n, j.val < m → k.val = m → (σ j < σ k ↔ τ j < τ k) := by
        intro j k hj hk
        have hjk : j < k := by rw [Fin.lt_def]; omega
        rw [lt_iff_card σ hjk, lt_iff_card τ hjk, hst k]
        have : (univ.filter fun l : Fin n => l < k ∧ σ l < σ j) =
            univ.filter fun l : Fin n => l < k ∧ τ l < τ j := by
          apply filter_congr; intro l _
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, (ih l j (by rw [Fin.lt_def] at h1; omega) hj).1 h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, (ih l j (by rw [Fin.lt_def] at h1; omega) hj).2 h2⟩
        rw [this]
      intro j k hj hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact ih j k hj hk
      · exact half j k hj hk
      · have hne : j ≠ k := by intro e; subst e; omega
        rw [lt_iff_not_lt_of_ne σ hne, lt_iff_not_lt_of_ne τ hne, half k j hk hj]
      · have : j = k := Fin.ext (by omega)
        subst this; simp
  have hall : ∀ j k : Fin n, σ j < σ k ↔ τ j < τ k := fun j k => key n j k j.isLt k.isLt
  apply Equiv.ext
  intro j
  apply Fin.ext
  rw [← card_lt_val σ (σ j), ← card_lt_val τ (τ j)]
  congr 1
  apply filter_congr
  intro k _
  exact hall k j

lemma image_relRank :
    (univ : Finset (Equiv.Perm (Fin n))).image (fun σ => relRank σ) = A n := by
  apply eq_of_subset_of_card_le
  · intro a ha
    simp only [mem_image, mem_univ, true_and] at ha
    obtain ⟨σ, rfl⟩ := ha
    rw [mem_A]; exact relRank_le σ
  · rw [card_A, card_image_of_injective _ relRank_injective, card_univ, Fintype.card_perm,
      Fintype.card_fin]

lemma transfer (P : (Fin n → ℕ) → Prop) [DecidablePred P] :
    #{σ : Equiv.Perm (Fin n) | P (relRank σ)} = #{a ∈ A n | P a} := by
  rw [← image_relRank, filter_image, card_image_of_injective _ relRank_injective]

/-! ### Histories and the translated events -/

/-- History of a code `a` up to time `i`. -/
def hist (a : Fin n → ℕ) (i : Fin n) : List ℕ := ((List.finRange n).take (i.val + 1)).map a

lemma history_eq (σ : Equiv.Perm (Fin n)) (i : Fin n) : history σ i = hist (relRank σ) i := rfl

lemma mem_take_finRange {k : ℕ} {x : Fin n} (hx : x ∈ (List.finRange n).take k) : x.val < k := by
  rw [List.mem_take_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp at hi ⊢
  omega

lemma hist_length (a : Fin n → ℕ) (i : Fin n) : (hist a i).length = i.val + 1 := by
  simp [hist]

lemma hist_getLast? (a : Fin n → ℕ) (i : Fin n) : (hist a i).getLast? = some (a i) := by
  rw [List.getLast?_eq_getElem?, hist_length]
  simp [hist]

lemma hist_congr {a b : Fin n → ℕ} {i : Fin n} (h : ∀ j : Fin n, j ≤ i → a j = b j) :
    hist a i = hist b i := by
  unfold hist
  apply List.map_congr_left
  intro x hx
  apply h
  have := mem_take_finRange hx
  rw [Fin.le_def]; omega

lemma hist_update {a : Fin n → ℕ} {i j : Fin n} (hij : i < j) (c : ℕ) :
    hist (Function.update a j c) i = hist a i := by
  apply hist_congr
  intro k hk
  rw [Function.update_of_ne]
  exact ne_of_lt (lt_of_le_of_lt hk hij)

lemma cutoffRule_hist (r : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    cutoffRule r (hist a i) = true ↔ r ≤ i.val + 1 ∧ a i = i.val := by
  simp [cutoffRule, hist_length, hist_getLast?]

/-- The rule `s` stops at time `i` on code `a`. -/
def stopsAt (s : StoppingRule) (a : Fin n → ℕ) (i : Fin n) : Prop :=
  s (hist a i) = true ∧ ∀ j : Fin n, j < i → s (hist a j) = false

instance (s : StoppingRule) (a : Fin n → ℕ) (i : Fin n) : Decidable (stopsAt s a i) := by
  unfold stopsAt; infer_instance

/-- The rule `s` wins on code `a`. -/
def winsA (s : StoppingRule) (a : Fin n → ℕ) : Prop :=
  ∃ i : Fin n, stopsAt s a i ∧ a i = i.val ∧ ∀ j : Fin n, i < j → a j < j.val

instance (s : StoppingRule) (a : Fin n → ℕ) : Decidable (winsA s a) := by
  unfold winsA; infer_instance

lemma stopsAt_congr (s : StoppingRule) {a b : Fin n → ℕ} {i : Fin n}
    (h : ∀ j : Fin n, j ≤ i → a j = b j) : stopsAt s a i ↔ stopsAt s b i := by
  unfold stopsAt
  rw [hist_congr h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    rw [← hist_congr (fun k hk => h k (hk.trans hj.le))]; exact h2 j hj
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    rw [hist_congr (fun k hk => h k (hk.trans hj.le))]; exact h2 j hj

lemma isBest_iff (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    IsBest σ i ↔ relRank σ i = i.val ∧ ∀ j : Fin n, i < j → relRank σ j < j.val := by
  constructor
  · intro h
    refine ⟨(relRank_eq_iff σ i).2 fun k hk => ?_, fun j hj => ?_⟩
    · exact lt_of_le_of_ne (h k) (fun e => (ne_of_lt hk) (σ.injective e))
    · refine lt_of_le_of_ne (relRank_le σ j) (fun e => ?_)
      have := (relRank_eq_iff σ j).1 e i hj
      exact absurd (h j) (not_le.mpr this)
  · rintro ⟨h1, h2⟩
    have : Nonempty (Fin n) := ⟨i⟩
    obtain ⟨m, hm⟩ := Finite.exists_max σ
    rcases lt_trichotomy m i with hmi | hmi | hmi
    · have := (relRank_eq_iff σ i).1 h1 m hmi
      exact absurd (hm i) (not_le.mpr this)
    · subst hmi; exact hm
    · have hc : relRank σ m = m.val := (relRank_eq_iff σ m).2 fun k hk =>
        lt_of_le_of_ne (hm k) (fun e => (ne_of_lt hk) (σ.injective e))
      have := h2 m hmi
      omega

lemma wins_iff (s : StoppingRule) (σ : Equiv.Perm (Fin n)) : Wins s σ ↔ winsA s (relRank σ) := by
  unfold Wins winsA
  simp only [isBest_iff]
  rfl

lemma card_wins_eq (s : StoppingRule) :
    #{σ : Equiv.Perm (Fin n) | Wins s σ} = #{a ∈ A n | winsA s a} := by
  rw [← transfer]
  congr 1
  apply filter_congr
  intro σ _
  exact wins_iff s σ

lemma successProb_eq (s : StoppingRule) :
    successProb n s = (#{a ∈ A n | winsA s a} : ℝ) / (Nat.factorial n : ℝ) := by
  unfold successProb
  rw [card_wins_eq, Fintype.card_perm, Fintype.card_fin]

/-! ### The counting lemma -/

lemma count_fiber (E : (Fin n → ℕ) → Prop) [DecidablePred E] (j : Fin n)
    (hE : ∀ a c, E (Function.update a j c) ↔ E a) {c c' : ℕ} (hc : c ≤ j.val) (hc' : c' ≤ j.val) :
    #{a ∈ A n | E a ∧ a j = c} = #{a ∈ A n | E a ∧ a j = c'} := by
  refine card_bij' (fun a _ => Function.update a j c') (fun a _ => Function.update a j c)
    ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_A] at ha ⊢
    refine ⟨fun k => ?_, (hE a c').2 ha.2.1, by simp⟩
    by_cases hk : k = j
    · subst hk; simp [hc']
    · rw [Function.update_of_ne hk]; exact ha.1 k
  · intro a ha
    simp only [mem_filter, mem_A] at ha ⊢
    refine ⟨fun k => ?_, (hE a c).2 ha.2.1, by simp⟩
    by_cases hk : k = j
    · subst hk; simp [hc]
    · rw [Function.update_of_ne hk]; exact ha.1 k
  · intro a ha
    simp only [mem_filter] at ha
    simp only [Function.update_idem]
    rw [← ha.2.2, Function.update_eq_self]
  · intro a ha
    simp only [mem_filter] at ha
    simp only [Function.update_idem]
    rw [← ha.2.2, Function.update_eq_self]

lemma count_sum (E : (Fin n → ℕ) → Prop) [DecidablePred E] (j : Fin n)
    (hE : ∀ a c, E (Function.update a j c) ↔ E a) (C : Finset ℕ) (hC : C ⊆ range (j.val + 1)) :
    #{a ∈ A n | E a ∧ a j ∈ C} = #C * #{a ∈ A n | E a ∧ a j = 0} := by
  rw [card_eq_sum_card_fiberwise (f := fun a => a j) (t := C)
    (by intro a ha; rw [mem_coe, mem_filter] at ha; exact ha.2.2)]
  rw [← smul_eq_mul, ← sum_const]
  apply sum_congr rfl
  intro c hc
  have hcj : c ≤ j.val := by have := hC hc; simp at this; omega
  rw [filter_filter, ← count_fiber E j hE hcj (Nat.zero_le _)]
  congr 1
  apply filter_congr
  intro a _
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hc⟩, h3⟩

lemma count_main (E : (Fin n → ℕ) → Prop) [DecidablePred E] (j : Fin n)
    (hE : ∀ a c, E (Function.update a j c) ↔ E a) (C : Finset ℕ) (hC : C ⊆ range (j.val + 1)) :
    #{a ∈ A n | E a ∧ a j ∈ C} * (j.val + 1) = #{a ∈ A n | E a} * #C := by
  have h1 := count_sum E j hE C hC
  have h2 := count_sum E j hE (range (j.val + 1)) subset_rfl
  have h3 : #{a ∈ A n | E a ∧ a j ∈ range (j.val + 1)} = #{a ∈ A n | E a} := by
    congr 1
    apply filter_congr
    intro a ha
    rw [mem_A] at ha
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by rw [mem_range]; have := ha j; omega⟩
  rw [card_range] at h2
  rw [h1, ← h3, h2]
  ring

lemma count_iter (G : (Fin n → ℕ) → Prop) [DecidablePred G] (i : Fin n)
    (hG : ∀ a (j : Fin n) c, i < j → (G (Function.update a j c) ↔ G a)) :
    #{a ∈ A n | G a ∧ ∀ j : Fin n, i < j → a j < j.val} * n =
      #{a ∈ A n | G a} * (i.val + 1) := by
  have key : ∀ m, i.val + 1 ≤ m → m ≤ n →
      #{a ∈ A n | G a ∧ ∀ j : Fin n, i < j → j.val < m → a j < j.val} * m =
        #{a ∈ A n | G a} * (i.val + 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      congr 2
      apply filter_congr
      intro a _
      constructor
      · exact fun h => h.1
      · intro h; refine ⟨h, fun j hij hj => ?_⟩; rw [Fin.lt_def] at hij; omega
    | succ m hm ih =>
      intro hmn
      have ih := ih (by omega)
      let jm : Fin n := ⟨m, by omega⟩
      have hijm : i < jm := by rw [Fin.lt_def]; show i.val < m; omega
      have hE : ∀ a c, (G (Function.update a jm c) ∧
          ∀ j : Fin n, i < j → j.val < m → Function.update a jm c j < j.val) ↔
          (G a ∧ ∀ j : Fin n, i < j → j.val < m → a j < j.val) := by
        intro a c
        rw [hG a jm c hijm]
        apply and_congr_right
        intro _
        apply forall_congr'; intro j; apply imp_congr_right; intro _
        apply imp_congr_right; intro hj
        rw [Function.update_of_ne]
        intro e; rw [e] at hj; exact lt_irrefl _ hj
      have := count_main (fun a => G a ∧ ∀ j : Fin n, i < j → j.val < m → a j < j.val) jm hE
        (range m) (by intro x; simp only [mem_range]; intro hx; show x < m + 1; omega)
      rw [card_range, ih] at this
      rw [← this]
      congr 2
      apply filter_congr
      intro a _
      simp only [mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun j hij hj => h2 j hij (by omega)⟩, h2 jm hijm (by show m < m + 1; omega)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun j hij hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact h2 j hij hj
        · have : j = jm := Fin.ext hj
          rw [this]; exact h3
  have := key n (by omega) le_rfl
  rw [← this]
  congr 2
  apply filter_congr
  intro a _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hij _ => h2 j hij⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hij => h2 j hij j.isLt⟩

/-! ### Counts attached to a rule -/

/-- Number of codes on which `s` has not stopped before time `k`. -/
def R (s : StoppingRule) (n k : ℕ) : ℕ :=
  #{a ∈ A n | ∀ j : Fin n, j.val < k → s (hist a j) = false}

/-- Number of codes on which `s` stops at time `i` on a candidate. -/
def Qf (s : StoppingRule) (i : Fin n) : ℕ := #{a ∈ A n | stopsAt s a i ∧ a i = i.val}

/-- `Qf` indexed by natural numbers. -/
def Q (s : StoppingRule) (n k : ℕ) : ℕ := if h : k < n then Qf s (⟨k, h⟩ : Fin n) else 0

lemma Q_eq (s : StoppingRule) {k : ℕ} (h : k < n) : Q s n k = Qf s (⟨k, h⟩ : Fin n) := dif_pos h

lemma R_zero (s : StoppingRule) : R s n 0 = Nat.factorial n := by
  unfold R; rw [← card_A]; congr 1
  apply filter_true_of_mem
  intro a _ j hj; omega

lemma card_wins_sum (s : StoppingRule) :
    #{a ∈ A n | winsA s a} = ∑ i : Fin n,
      #{a ∈ A n | stopsAt s a i ∧ a i = i.val ∧ ∀ j : Fin n, i < j → a j < j.val} := by
  rw [← card_biUnion]
  · congr 1; ext a
    rw [mem_filter, mem_biUnion]
    simp only [mem_univ, true_and, mem_filter, winsA]
    constructor
    · rintro ⟨ha, i, hi⟩; exact ⟨i, ha, hi⟩
    · rintro ⟨i, ha, hi⟩; exact ⟨ha, i, hi⟩
  · intro i _ i' _ hii'
    simp only [Function.onFun]
    rw [disjoint_filter]
    intro a _ h1 h2
    rcases lt_or_gt_of_ne hii' with h | h
    · have := h2.1.2 i h; rw [h1.1.1] at this; exact Bool.noConfusion this
    · have := h1.1.2 i' h; rw [h2.1.1] at this; exact Bool.noConfusion this

/-- (P1) -/
lemma P1 (s : StoppingRule) :
    #{a ∈ A n | winsA s a} * n = ∑ i ∈ range n, Q s n i * (i + 1) := by
  rw [card_wins_sum, sum_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun i => Q s n i * (i + 1)) n]
  apply sum_congr rfl
  intro i _
  rw [Q_eq s i.isLt]
  have := count_iter (fun a => stopsAt s a i ∧ a i = i.val) i ?_
  · simp only [and_assoc] at this; rw [this]; rfl
  · intro a j c hij
    rw [stopsAt_congr s (b := a)
      (fun k hk => Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hk hij)) _ _)]
    rw [Function.update_of_ne (ne_of_lt hij)]

lemma notStopped_update (s : StoppingRule) (i : Fin n) (a : Fin n → ℕ) (c : ℕ) :
    (∀ j : Fin n, j.val < i.val → s (hist (Function.update a i c) j) = false) ↔
      (∀ j : Fin n, j.val < i.val → s (hist a j) = false) := by
  apply forall_congr'; intro j; apply imp_congr_right; intro hj
  rw [hist_update (show j < i from hj)]

lemma count_notStopped (s : StoppingRule) {k : ℕ} (hk : k < n) :
    #{a ∈ A n | (∀ j : Fin n, j.val < k → s (hist a j) = false) ∧
      a (⟨k, hk⟩ : Fin n) ∈ ({k} : Finset ℕ)} * (k + 1) = R s n k := by
  have := count_main (fun a => ∀ j : Fin n, j.val < k → s (hist a j) = false) (⟨k, hk⟩ : Fin n)
    (notStopped_update s ⟨k, hk⟩) {k} (by intro x; simp only [mem_singleton, mem_range]; omega)
  rw [card_singleton, mul_one] at this
  exact this

/-- (P2) -/
lemma P2 (s : StoppingRule) {k : ℕ} (hk : k < n) : Q s n k * (k + 1) ≤ R s n k := by
  rw [Q_eq s hk, ← count_notStopped s hk]
  apply Nat.mul_le_mul_right
  apply card_le_card
  intro a; simp only [mem_filter, mem_singleton]
  rintro ⟨ha, ⟨_, h2⟩, h3⟩
  exact ⟨ha, fun j hj => h2 j hj, h3⟩

lemma R_succ_add (s : StoppingRule) {k : ℕ} (hk : k < n) :
    R s n (k + 1) + #{a ∈ A n | stopsAt s a ⟨k, hk⟩} = R s n k := by
  unfold R
  rw [← card_filter_add_card_filter_not
    (s := filter (fun a => ∀ j : Fin n, j.val < k → s (hist a j) = false) (A n))
    (p := fun a => s (hist a ⟨k, hk⟩) = false)]
  rw [filter_filter, filter_filter]
  congr 2
  · apply filter_congr; intro a _
    constructor
    · intro h; exact ⟨fun j hj => h j (by omega), h ⟨k, hk⟩ (by simp)⟩
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact h1 j hj
      · have : j = ⟨k, hk⟩ := Fin.ext hj
        rw [this]; exact h2
  · apply filter_congr; intro a _
    unfold stopsAt
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by simpa using h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨by simpa using h2, fun j hj => h1 j hj⟩

/-- (P3) -/
lemma P3 (s : StoppingRule) {k : ℕ} (hk : k < n) : R s n (k + 1) + Q s n k ≤ R s n k := by
  rw [← R_succ_add s hk, Q_eq s hk]
  apply Nat.add_le_add_left
  apply card_le_card
  intro a ha
  rw [mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.1⟩

/-! ### The cutoff rule -/

lemma stopsAt_cutoff {r : ℕ} {a : Fin n → ℕ} {i : Fin n} (h : stopsAt (cutoffRule r) a i) :
    r ≤ i.val + 1 ∧ a i = i.val := (cutoffRule_hist r a i).1 h.1

/-- Equality in (P2) after the cutoff. -/
lemma cutoff_Q (r : ℕ) {k : ℕ} (hk : k < n) (hrk : r ≤ k + 1) :
    Q (cutoffRule r) n k * (k + 1) = R (cutoffRule r) n k := by
  rw [Q_eq _ hk, ← count_notStopped _ hk]
  unfold Qf
  congr 2
  apply filter_congr
  intro a _
  rw [mem_singleton]
  unfold stopsAt
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨fun j hj => h2 j hj, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨(cutoffRule_hist r a _).2 ⟨hrk, h3⟩, fun j hj => h1 j hj⟩, h3⟩

/-- Equality in (P3) after the cutoff. -/
lemma cutoff_R (r : ℕ) {k : ℕ} (hk : k < n) :
    R (cutoffRule r) n (k + 1) + Q (cutoffRule r) n k = R (cutoffRule r) n k := by
  rw [← R_succ_add _ hk, Q_eq _ hk]
  unfold Qf
  congr 2
  apply filter_congr
  intro a _
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, (stopsAt_cutoff h).2⟩

/-- Before the cutoff nothing happens. -/
lemma cutoff_before (r : ℕ) {k : ℕ} (hk : k < n) (hrk : k + 1 < r) :
    Q (cutoffRule r) n k = 0 ∧ R (cutoffRule r) n (k + 1) = R (cutoffRule r) n k := by
  have h0 : #{a ∈ A n | stopsAt (cutoffRule r) a ⟨k, hk⟩} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro a _ h
    have := (stopsAt_cutoff h).1
    simp only at this; omega
  have h1 := R_succ_add (cutoffRule r) hk
  have h2 := cutoff_R r hk
  omega

/-! ### Part C: optimality by backward induction -/


/-- Backward-induction values, indexed by the distance `d` to the horizon `n`. -/
noncomputable def W (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | d + 1 =>
      (1 / (((n - (d + 1) : ℕ) : ℝ) + 1)) *
          max ((((n - (d + 1) : ℕ) : ℝ) + 1) / n) (W n d) +
        (((n - (d + 1) : ℕ) : ℝ) / (((n - (d + 1) : ℕ) : ℝ) + 1)) * W n d

/-- The value of the optimal stopping problem from time `k` on. -/
noncomputable def V (n k : ℕ) : ℝ := W n (n - k)

lemma W_nonneg (n : ℕ) : ∀ d, 0 ≤ W n d := by
  intro d
  induction d with
  | zero => simp [W]
  | succ d ih =>
    simp only [W]
    have h1 : 0 ≤ max ((((n - (d + 1) : ℕ) : ℝ) + 1) / n) (W n d) := le_trans ih (le_max_right _ _)
    positivity

lemma V_nonneg (n k : ℕ) : 0 ≤ V n k := W_nonneg n _

lemma V_of_le {n k : ℕ} (h : n ≤ k) : V n k = 0 := by
  unfold V; rw [Nat.sub_eq_zero_of_le h]; rfl

lemma V_succ {n k : ℕ} (h : k < n) :
    V n k = (1 / ((k : ℝ) + 1)) * max (((k : ℝ) + 1) / n) (V n (k + 1)) +
      ((k : ℝ) / ((k : ℝ) + 1)) * V n (k + 1) := by
  unfold V
  rw [show n - k = (n - (k + 1)) + 1 by omega]
  simp only [W]
  rw [show n - (n - (k + 1) + 1) = k by omega]

lemma V_succ_le (n k : ℕ) : V n (k + 1) ≤ V n k := by
  by_cases h : k < n
  · rw [V_succ h]
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have := le_max_right (((k : ℝ) + 1) / n) (V n (k + 1))
    have e : V n (k + 1) = (1 / ((k : ℝ) + 1)) * V n (k + 1) +
        ((k : ℝ) / ((k : ℝ) + 1)) * V n (k + 1) := by field_simp; ring
    have h1 : (1 / ((k : ℝ) + 1)) * V n (k + 1) ≤
        (1 / ((k : ℝ) + 1)) * max (((k : ℝ) + 1) / n) (V n (k + 1)) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  · rw [V_of_le (by omega), V_of_le (by omega)]

lemma V_antitone (n : ℕ) : Antitone (V n) := antitone_nat_of_succ_le (V_succ_le n)

/-- One step of the backward induction (inequality, arbitrary rule). -/
lemma step_le {q Rk Rk1 v x k : ℝ} (hk : 0 ≤ k) (hq : 0 ≤ q) (hv : 0 ≤ v)
    (hP2 : q * (k + 1) ≤ Rk) (hP3 : Rk1 + q ≤ Rk) :
    q * x + Rk1 * v ≤ Rk * ((1 / (k + 1)) * max x v + (k / (k + 1)) * v) := by
  have hk1 : 0 < k + 1 := by linarith
  have e : Rk * ((1 / (k + 1)) * max x v + (k / (k + 1)) * v) =
      Rk / (k + 1) * (max x v - v) + Rk * v := by field_simp; ring
  rw [e]
  have h1 : Rk1 * v ≤ (Rk - q) * v := mul_le_mul_of_nonneg_right (by linarith) hv
  have hm : x - v ≤ max x v - v := by linarith [le_max_left x v]
  have hm0 : 0 ≤ max x v - v := by linarith [le_max_right x v]
  have hqR : q ≤ Rk / (k + 1) := by rw [le_div_iff₀ hk1]; linarith
  have h2 : q * (x - v) ≤ Rk / (k + 1) * (max x v - v) :=
    calc q * (x - v) ≤ q * (max x v - v) := mul_le_mul_of_nonneg_left hm hq
      _ ≤ Rk / (k + 1) * (max x v - v) := mul_le_mul_of_nonneg_right hqR hm0
  nlinarith [h1, h2]

/-- One step of the backward induction (equality, stop region). -/
lemma step_eq_stop {q Rk Rk1 v x k : ℝ} (hk : 0 ≤ k) (hxv : v ≤ x)
    (hP2 : q * (k + 1) = Rk) (hP3 : Rk1 + q = Rk) :
    q * x + Rk1 * v = Rk * ((1 / (k + 1)) * max x v + (k / (k + 1)) * v) := by
  have hk1 : k + 1 ≠ 0 := by linarith
  rw [max_eq_left hxv]
  have hq : q = Rk / (k + 1) := by field_simp; linarith
  have hR : Rk1 = Rk - Rk / (k + 1) := by linarith
  rw [hR, hq]
  field_simp
  ring

/-- One step of the backward induction (equality, continue region). -/
lemma step_eq_cont {q Rk Rk1 v x k : ℝ} (hk : 0 ≤ k) (hxv : x ≤ v)
    (hq : q = 0) (hP3 : Rk1 = Rk) :
    q * x + Rk1 * v = Rk * ((1 / (k + 1)) * max x v + (k / (k + 1)) * v) := by
  have hk1 : k + 1 ≠ 0 := by linarith
  rw [max_eq_right hxv, hq, hP3]
  field_simp
  ring

/-- The backward-induction bound for an arbitrary rule. -/
lemma tail_le (n : ℕ) (s : StoppingRule) : ∀ k, k ≤ n →
    ∑ i ∈ Ico k n, (Q s n i : ℝ) * ((i : ℝ) + 1) / n ≤ (R s n k : ℝ) * V n k := by
  intro k hk
  refine Nat.decreasingInduction (motive := fun k _ =>
    ∑ i ∈ Ico k n, (Q s n i : ℝ) * ((i : ℝ) + 1) / n ≤ (R s n k : ℝ) * V n k)
    (fun k hk ih => ?_) ?_ hk
  · rw [sum_eq_sum_Ico_succ_bot hk, V_succ hk]
    have h2 : ((Q s n k * (k + 1) : ℕ) : ℝ) ≤ (R s n k : ℝ) := by exact_mod_cast P2 s hk
    have h3 : ((R s n (k + 1) + Q s n k : ℕ) : ℝ) ≤ (R s n k : ℝ) := by exact_mod_cast P3 s hk
    push_cast at h2 h3
    have := step_le (x := ((k : ℝ) + 1) / n) (k := (k : ℝ)) (by positivity)
      (Nat.cast_nonneg (Q s n k)) (V_nonneg n (k + 1)) h2 h3
    have e : (Q s n k : ℝ) * ((k : ℝ) + 1) / n = (Q s n k : ℝ) * (((k : ℝ) + 1) / n) := by ring
    rw [e]
    have hih : ∑ i ∈ Ico (k + 1) n, (Q s n i : ℝ) * ((i : ℝ) + 1) / n ≤
        (R s n (k + 1) : ℝ) * V n (k + 1) := ih
    linarith
  · simp [V_of_le (le_refl n)]

lemma wins_eq_sum (n : ℕ) (hn : 1 ≤ n) (s : StoppingRule) :
    (#{a ∈ A n | winsA s a} : ℝ) = ∑ i ∈ Ico 0 n, (Q s n i : ℝ) * ((i : ℝ) + 1) / n := by
  have h := congrArg (fun x : ℕ => (x : ℝ)) (P1 (n := n) s)
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_one] at h
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← range_eq_Ico, ← sum_div, ← h]
  field_simp

lemma successProb_le_V (n : ℕ) (hn : 1 ≤ n) (s : StoppingRule) : successProb n s ≤ V n 0 := by
  rw [successProb_eq, wins_eq_sum n hn]
  have := tail_le n s 0 (Nat.zero_le _)
  rw [R_zero] at this
  have hf : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf]
  linarith

/-- The stop region is nonempty. -/
lemma exists_stop (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, k < n ∧ V n (k + 1) ≤ ((k : ℝ) + 1) / n := by
  refine ⟨n - 1, by omega, ?_⟩
  rw [V_of_le (by omega)]
  positivity

theorem optimal_cutoff (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ n ∧ successProb n (cutoffRule r) = optimalProb n := by
  classical
  let kst := Nat.find (exists_stop n hn)
  have hkst : kst < n ∧ V n (kst + 1) ≤ ((kst : ℝ) + 1) / n := Nat.find_spec (exists_stop n hn)
  have hafter : ∀ k, kst ≤ k → k < n → V n (k + 1) ≤ ((k : ℝ) + 1) / n := by
    intro k hk _
    have h1 : V n (k + 1) ≤ V n (kst + 1) := V_antitone n (by omega)
    have h2 : ((kst : ℝ) + 1) / n ≤ ((k : ℝ) + 1) / n := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      have : (kst : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    linarith [hkst.2]
  have hbefore : ∀ k, k < kst → ((k : ℝ) + 1) / n ≤ V n (k + 1) := by
    intro k hk
    have := Nat.find_min (exists_stop n hn) hk
    have hkn : k < n := by omega
    push Not at this
    exact (this hkn).le
  set c := cutoffRule (kst + 1) with hc
  have tail_eq : ∀ k, k ≤ n →
      ∑ i ∈ Ico k n, (Q c n i : ℝ) * ((i : ℝ) + 1) / n = (R c n k : ℝ) * V n k := by
    intro k hk
    refine Nat.decreasingInduction (motive := fun k _ =>
      ∑ i ∈ Ico k n, (Q c n i : ℝ) * ((i : ℝ) + 1) / n = (R c n k : ℝ) * V n k)
      (fun k hk ih => ?_) ?_ hk
    · have ih' : ∑ i ∈ Ico (k + 1) n, (Q c n i : ℝ) * ((i : ℝ) + 1) / n =
          (R c n (k + 1) : ℝ) * V n (k + 1) := ih
      rw [sum_eq_sum_Ico_succ_bot hk, V_succ hk, ih']
      have e : (Q c n k : ℝ) * ((k : ℝ) + 1) / n = (Q c n k : ℝ) * (((k : ℝ) + 1) / n) := by ring
      rw [e]
      by_cases hks : kst ≤ k
      · have h2 : ((Q c n k * (k + 1) : ℕ) : ℝ) = (R c n k : ℝ) := by
          exact_mod_cast cutoff_Q (kst + 1) hk (by omega)
        have h3 : ((R c n (k + 1) + Q c n k : ℕ) : ℝ) = (R c n k : ℝ) := by
          exact_mod_cast cutoff_R (kst + 1) hk
        push_cast at h2 h3
        exact step_eq_stop (Nat.cast_nonneg k) (hafter k hks hk) h2 h3
      · have hb := cutoff_before (kst + 1) hk (by omega : k + 1 < kst + 1)
        have h2 : (Q c n k : ℝ) = 0 := by exact_mod_cast hb.1
        have h3 : (R c n (k + 1) : ℝ) = (R c n k : ℝ) := by exact_mod_cast hb.2
        exact step_eq_cont (Nat.cast_nonneg k) (hbefore k (by omega)) h2 h3
    · simp [V_of_le (le_refl n)]
  have hcV : successProb n c = V n 0 := by
    rw [successProb_eq, wins_eq_sum n hn, tail_eq 0 (Nat.zero_le _), R_zero]
    have hf : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  have hbdd : BddAbove (Set.range fun s : StoppingRule => successProb n s) := by
    refine ⟨V n 0, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact successProb_le_V n hn s
  refine ⟨kst + 1, by omega, by omega, ?_⟩
  unfold optimalProb
  apply le_antisymm
  · exact le_ciSup hbdd c
  · apply ciSup_le
    intro s
    rw [hcV]
    exact successProb_le_V n hn s

end ClassicalSecretary.SecCore

open ClassicalSecretary in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ n ∧ successProb n (cutoffRule r) = optimalProb n :=
  ClassicalSecretary.SecCore.optimal_cutoff n hn
