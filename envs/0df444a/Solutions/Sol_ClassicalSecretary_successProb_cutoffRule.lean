-- Prove2me | solution 1 for ClassicalSecretary.successProb_cutoffRule
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T15:49:11.564808+00:00
-- url     : https://prove2.me/submissions/1ebe0844-5be3-44b7-b57b-28be136cddcc

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

/-! ### Part B: the cutoff formula -/



lemma R_cutoff_init (r : ℕ) (hrn : r ≤ n) :
    ∀ i, i ≤ r - 1 → R (cutoffRule r) n i = Nat.factorial n := by
  intro i
  induction i with
  | zero => intro _; exact R_zero _
  | succ i ih =>
    intro hi
    rw [(cutoff_before r (by omega : i < n) (by omega)).2, ih (by omega)]

lemma R_cutoff_mul (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    ∀ i, r - 1 ≤ i → i ≤ n → R (cutoffRule r) n i * i = Nat.factorial n * (r - 1) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => intro _; rw [R_cutoff_init r hrn (r - 1) le_rfl]
  | succ i hi ih =>
    intro hin
    have h1 := cutoff_Q r (by omega : i < n) (by omega)
    have h2 := cutoff_R r (by omega : i < n)
    have h3 := ih (by omega)
    have e : R (cutoffRule r) n (i + 1) * (i + 1) + Q (cutoffRule r) n i * (i + 1) =
        R (cutoffRule r) n i * (i + 1) := by rw [← add_mul, h2]
    rw [h1] at e
    have : R (cutoffRule r) n (i + 1) * (i + 1) + R (cutoffRule r) n i =
        R (cutoffRule r) n i * i + R (cutoffRule r) n i := by rw [e]; ring
    rw [← h3]; exact Nat.add_right_cancel this

lemma cutoff_wins (r : ℕ) :
    #{a ∈ A n | winsA (cutoffRule r) a} * n =
      ∑ i ∈ range n, if r ≤ i + 1 then R (cutoffRule r) n i else 0 := by
  rw [P1]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  split_ifs with h
  · exact cutoff_Q r hi h
  · rw [(cutoff_before r hi (by omega)).1, zero_mul]


lemma reindex (r n : ℕ) (hr : 1 ≤ r) :
    ∑ i ∈ Icc r n, 1 / ((i : ℝ) - 1) = ∑ i ∈ Ico (r - 1) n, 1 / (i : ℝ) := by
  have := sum_Ico_add' (fun i : ℕ => 1 / ((i : ℝ) - 1)) (r - 1) n 1
  rw [Nat.sub_add_cancel hr, Finset.Ico_add_one_right_eq_Icc] at this
  rw [← this]
  apply sum_congr rfl
  intro i _
  push_cast; ring

theorem cutoff_formula (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) :
    successProb n (cutoffRule r) =
      ((r : ℝ) - 1) / (n : ℝ) * ∑ i ∈ Icc r n, 1 / ((i : ℝ) - 1) := by
  rw [successProb_eq, reindex r n (by omega)]
  have hW := cutoff_wins (n := n) r
  have hterm : ∀ i ∈ range n, ((if r ≤ i + 1 then R (cutoffRule r) n i else 0 : ℕ) : ℝ) =
      if r ≤ i + 1 then (Nat.factorial n : ℝ) * ((r : ℝ) - 1) * (1 / (i : ℝ)) else 0 := by
    intro i hi
    rw [mem_range] at hi
    split_ifs with h
    · have h1 := R_cutoff_mul (n := n) r (by omega) hrn i (by omega) hi.le
      have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h1' : (R (cutoffRule r) n i : ℝ) * i = (Nat.factorial n : ℝ) * ((r : ℝ) - 1) := by
        have := congrArg (fun x : ℕ => (x : ℝ)) h1
        push_cast [Nat.cast_sub (by omega : 1 ≤ r)] at this
        exact this
      field_simp
      linarith
    · simp
  have hW' : (#{a ∈ A n | winsA (cutoffRule r) a} : ℝ) * n =
      (Nat.factorial n : ℝ) * ((r : ℝ) - 1) * ∑ i ∈ Ico (r - 1) n, 1 / (i : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hW
    simp only [Nat.cast_mul, Nat.cast_sum] at this
    rw [this, sum_congr rfl hterm, ← sum_filter, mul_sum]
    apply sum_congr
    · ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
    · intro i _; rfl
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hf : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [div_eq_iff hf]
  field_simp
  linarith [hW']

end ClassicalSecretary.SecCore

open ClassicalSecretary in
theorem solution (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) :
    successProb n (cutoffRule r) =
      ((r : ℝ) - 1) / (n : ℝ) * ∑ i ∈ Icc r n, 1 / ((i : ℝ) - 1) :=
  ClassicalSecretary.SecCore.cutoff_formula n r hr hrn
