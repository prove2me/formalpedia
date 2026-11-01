-- Prove2me | solution 1 for BudgetCournot.Equilibrium.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:04:31.546918+00:00
-- url     : https://prove2.me/submissions/6f9deb3b-53a1-4f41-8c3d-fc1588c7b5c4

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BCSol

open BudgetCournot.Equilibrium

noncomputable def Ssum {N : ℕ} (α : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n),
    α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))

noncomputable def lamv {N : ℕ} (α : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i / ((i : ℕ) + 2 : ℝ) + ∑ k ∈ univ.filter (fun k : Fin N => k ≤ i),
    α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))

noncomputable def cv {N : ℕ} (α : Fin N → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  r / (1 + (n : ℝ)) + Ssum α n

lemma closedForm_eq {N M : ℕ} (R β : Fin M → ℝ) (α : Fin N → ℝ) (n : Fin M → ℕ)
    (i : Fin N) (j : Fin M) :
    closedForm R β α n i j = β j * max 0 (cv α (R j) (n j) - lamv α i) := by
  unfold closedForm cv lamv Ssum
  congr 2
  ring

lemma filter_lt_succ {N : ℕ} (i : Fin N) :
    univ.filter (fun k : Fin N => (k : ℕ) < (i : ℕ) + 1) =
      insert i (univ.filter (fun k : Fin N => (k : ℕ) < (i : ℕ))) := by
  ext k; simp [Fin.ext_iff]; omega

lemma filter_le_eq {N : ℕ} (i : Fin N) :
    univ.filter (fun k : Fin N => k ≤ i) =
      univ.filter (fun k : Fin N => (k : ℕ) < (i : ℕ) + 1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.le_def]; omega

lemma filter_gt_succ {N : ℕ} (i i' : Fin N) (h : (i' : ℕ) = (i : ℕ) + 1) :
    univ.filter (fun k : Fin N => i < k) =
      insert i' (univ.filter (fun k : Fin N => i' < k)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega

lemma Ssum_succ {N : ℕ} (α : Fin N → ℝ) (i : Fin N) :
    Ssum α ((i : ℕ) + 1) = Ssum α (i : ℕ) + α i / (((i : ℕ) + 1 : ℝ) * ((i : ℕ) + 2 : ℝ)) := by
  unfold Ssum
  rw [filter_lt_succ, Finset.sum_insert (by simp)]
  ring

lemma Ssum_zero {N : ℕ} (α : Fin N → ℝ) : Ssum α 0 = 0 := by
  unfold Ssum; simp

lemma lamv_eq {N : ℕ} (α : Fin N → ℝ) (i : Fin N) :
    lamv α i = α i / ((i : ℕ) + 2 : ℝ) + Ssum α ((i : ℕ) + 1) := by
  unfold lamv Ssum; rw [filter_le_eq]

lemma L2 {N : ℕ} (α : Fin N → ℝ) (r : ℝ) (i : Fin N) :
    cv α r ((i : ℕ) + 1) - lamv α i = (r - α i) / ((i : ℕ) + 2 : ℝ) := by
  rw [lamv_eq]; unfold cv; push_cast
  have : (1 + ((i : ℕ) + 1 : ℝ)) = ((i : ℕ) + 2 : ℝ) := by ring
  rw [this]; ring

lemma L3 {N : ℕ} (α : Fin N → ℝ) (r : ℝ) (i : Fin N) :
    cv α r (i : ℕ) - lamv α i = (r - α i) / ((i : ℕ) + 1 : ℝ) := by
  rw [lamv_eq, Ssum_succ]; unfold cv
  have h1 : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
  field_simp; ring

lemma L1 {N : ℕ} (α : Fin N → ℝ) (i i' : Fin N) (h : (i' : ℕ) = (i : ℕ) + 1) :
    ((i : ℕ) + 2 : ℝ) * (lamv α i' - lamv α i) = α i' - α i := by
  rw [lamv_eq, lamv_eq, Ssum_succ α i', h]
  push_cast
  have h1 : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
  have h2 : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 + 2 := by positivity
  have h3 : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 + 1 := by positivity
  field_simp; ring

lemma monotone_of_succ {N : ℕ} (f : Fin N → ℝ)
    (h : ∀ i i' : Fin N, (i' : ℕ) = (i : ℕ) + 1 → f i ≤ f i') : Monotone f := by
  have key : ∀ d : ℕ, ∀ i i' : Fin N, (i' : ℕ) = (i : ℕ) + d → f i ≤ f i' := by
    intro d
    induction d with
    | zero => intro i i' hii; rw [Fin.ext ((by omega) : (i' : ℕ) = i)]
    | succ d ih =>
      intro i i' hii
      have hlt : (i : ℕ) + d < N := by have := i'.isLt; omega
      exact le_trans (ih i ⟨(i : ℕ) + d, hlt⟩ rfl) (h _ _ (by simp; omega))
  intro i i' hle
  exact key ((i' : ℕ) - i) i i' (by rw [Fin.le_def] at hle; omega)

lemma lamv_mono {N : ℕ} (α : Fin N → ℝ) (hα : Monotone α) : Monotone (lamv α) := by
  apply monotone_of_succ
  intro i i' h
  have e := L1 α i i' h
  have hii : α i ≤ α i' := hα (by rw [Fin.le_def]; omega)
  have hpos : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
  nlinarith

/-- the per-market structure -/
lemma market {N : ℕ} (α : Fin N → ℝ) (hα : Monotone α) (r : ℝ) (n : ℕ) (hn : n ≤ N)
    (hlo : ∀ i : Fin N, (i : ℕ) < n → α i ≤ r) (hhi : ∀ i : Fin N, n ≤ (i : ℕ) → r ≤ α i) :
    (∀ i : Fin N, (i : ℕ) < n → lamv α i ≤ cv α r n) ∧
    (∀ i : Fin N, n ≤ (i : ℕ) → cv α r n ≤ lamv α i) ∧
    (∀ i : Fin N, ((i : ℕ) + 2 : ℝ) * max 0 (cv α r n - lamv α i)
        + ∑ k ∈ univ.filter (fun k => i < k), max 0 (cv α r n - lamv α k)
        = max (r - α i) 0) ∧
    (∀ _i : Fin N, ∑ k, max 0 (cv α r n - lamv α k) = r - cv α r n) := by
  have hlm := lamv_mono α hα
  have Q1 : ∀ i : Fin N, (i : ℕ) < n → lamv α i ≤ cv α r n := by
    intro i hi
    set m : Fin N := ⟨n - 1, by omega⟩
    have hm : (m : ℕ) + 1 = n := by simp [m]; omega
    have e := L2 α r m
    rw [hm] at e
    have h1 : lamv α i ≤ lamv α m := hlm (by rw [Fin.le_def]; simp [m]; omega)
    have h2 : α m ≤ r := hlo m (by omega)
    have h3 : 0 ≤ (r - α m) / ((m : ℕ) + 2 : ℝ) := div_nonneg (by linarith) (by positivity)
    linarith
  have Q2 : ∀ i : Fin N, n ≤ (i : ℕ) → cv α r n ≤ lamv α i := by
    intro i hi
    set m : Fin N := ⟨n, by have := i.isLt; omega⟩
    have e := L3 α r m
    have hmn : (m : ℕ) = n := rfl
    rw [hmn] at e
    have h1 : lamv α m ≤ lamv α i := hlm (by rw [Fin.le_def]; simp [m]; omega)
    have h2 : r ≤ α m := hhi m (by simp [m])
    have h3 : (r - α m) / ((n : ℕ) + 1 : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  have P0 : ∀ i : Fin N, n ≤ (i : ℕ) → max 0 (cv α r n - lamv α i) = 0 := by
    intro i hi; exact max_eq_left (by linarith [Q2 i hi])
  have P1 : ∀ i : Fin N, (i : ℕ) < n → max 0 (cv α r n - lamv α i) = cv α r n - lamv α i := by
    intro i hi; exact max_eq_right (by linarith [Q1 i hi])
  have Q3 : ∀ i : Fin N, ((i : ℕ) + 2 : ℝ) * max 0 (cv α r n - lamv α i)
        + ∑ k ∈ univ.filter (fun k => i < k), max 0 (cv α r n - lamv α k)
        = max (r - α i) 0 := by
    have key : ∀ d : ℕ, ∀ i : Fin N, (i : ℕ) + 1 + d = N →
        ((i : ℕ) + 2 : ℝ) * max 0 (cv α r n - lamv α i)
        + ∑ k ∈ univ.filter (fun k => i < k), max 0 (cv α r n - lamv α k)
        = max (r - α i) 0 := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have hemp : univ.filter (fun k : Fin N => i < k) = ∅ := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rw [Fin.lt_def]; have := k.isLt; omega
        rw [hemp, Finset.sum_empty, add_zero]
        rcases lt_or_ge (i : ℕ) n with h | h
        · rw [P1 i h]
          have hn' : n = (i : ℕ) + 1 := by omega
          rw [hn', L2, max_eq_left (by linarith [hlo i h])]
          have : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
          field_simp
        · rw [P0 i h, max_eq_right (by linarith [hhi i h])]; ring
      | succ d ih =>
        intro i hi
        set i' : Fin N := ⟨(i : ℕ) + 1, by omega⟩
        have hii : (i' : ℕ) = (i : ℕ) + 1 := rfl
        have IH := ih i' (by rw [hii]; omega)
        rw [filter_gt_succ i i' hii, Finset.sum_insert (by simp)]
        have eL1 := L1 α i i' hii
        rw [hii] at IH
        push_cast at IH
        rcases lt_or_ge (i' : ℕ) n with h | h
        · have hi : (i : ℕ) < n := by omega
          rw [P1 i hi]
          rw [P1 i' h, max_eq_left (by linarith [hlo i' h])] at IH
          rw [P1 i' h, max_eq_left (by linarith [hlo i hi])]
          linarith
        · rcases lt_or_ge (i : ℕ) n with h' | h'
          · rw [P0 i' h, max_eq_right (by linarith [hhi i' h])] at IH
            rw [P0 i' h, P1 i h', max_eq_left (by linarith [hlo i h'])]
            have hn' : n = (i : ℕ) + 1 := by omega
            have e2 := L2 α r i
            rw [← hn'] at e2
            rw [e2]
            have : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
            field_simp
            linarith
          · rw [P0 i' h, max_eq_right (by linarith [hhi i' h])] at IH
            rw [P0 i' h, P0 i h', max_eq_right (by linarith [hhi i h'])]
            linarith
    intro i
    exact key (N - 1 - (i : ℕ)) i (by have := i.isLt; omega)
  refine ⟨Q1, Q2, Q3, ?_⟩
  intro i
  have hN : 0 < N := by have := i.isLt; omega
  set i0 : Fin N := ⟨0, hN⟩
  have huniv : (univ : Finset (Fin N)) = insert i0 (univ.filter (fun k => i0 < k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, true_iff]
    have h0 : (i0 : ℕ) = 0 := rfl
    rw [Fin.lt_def, Fin.ext_iff, h0]; omega
  have hl0 : lamv α i0 = α i0 := by
    have e := L3 α r i0
    have : ((i0 : ℕ)) = 0 := rfl
    rw [this] at e
    unfold cv at e
    rw [Ssum_zero] at e
    simp at e
    linarith
  rw [huniv, Finset.sum_insert (by simp)]
  have e := Q3 i0
  have : ((i0 : ℕ) : ℝ) = 0 := by simp [i0]
  rw [this] at e
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [P0 i0 (by simp)] at e ⊢
    rw [max_eq_right (by linarith [hhi i0 (by simp)])] at e
    have : cv α r 0 = r := by unfold cv; rw [Ssum_zero]; simp
    rw [this] at e ⊢; linarith
  · rw [P1 i0 (by simp [i0]; omega)] at e ⊢
    rw [max_eq_left (by linarith [hlo i0 (by simp [i0]; omega)])] at e
    rw [hl0] at e ⊢
    linarith

end BCSol

namespace BCSol

open BudgetCournot.Equilibrium

lemma sup_char' {N : ℕ} (P : Fin N → Prop) [DecidablePred P]
    (hP : ∀ i i' : Fin N, i ≤ i' → P i' → P i) (i : Fin N) :
    (i : ℕ) < (univ.filter P).sup (fun k => (k : ℕ) + 1) ↔ P i := by
  constructor
  · intro h
    rw [Finset.lt_sup_iff] at h
    obtain ⟨k, hk, hik⟩ := h
    rw [Finset.mem_filter] at hk
    exact hP i k (by rw [Fin.le_def]; omega) hk.2
  · intro h
    have := Finset.le_sup (f := fun k : Fin N => (k : ℕ) + 1)
      (Finset.mem_filter.2 ⟨mem_univ i, h⟩)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this

end BCSol

open BudgetCournot.Equilibrium in
theorem solution {N M : ℕ} (R β : Fin M → ℝ) (hR0 : ∀ j, 0 ≤ R j) (hβ : ∀ j, 0 < β j)
    (α : Fin N → ℝ) (hα : Monotone α) (hα0 : ∀ i, 0 ≤ α i) (V : Fin M → ℝ) (i : Fin N) :
    ((i : ℕ) + 2 : ℝ) * ∑ j, V j * xAlpha R β α i j
        + ∑ k ∈ univ.filter (fun k => i < k), ∑ j, V j * xAlpha R β α k j =
      ∑ j ∈ univ.filter (fun j => α i < R j), V j * β j * (R j - α i) := by
  have hmk := fun j : Fin M =>
    BCSol.market α hα (R j) (nAlpha R α j)
      (Finset.sup_le (fun k _ => k.isLt))
      (fun k hk => (BCSol.sup_char' (fun k : Fin N => α k ≤ R j)
          (fun a b hab hb => le_trans (hα hab) hb) k).1 hk)
      (fun k hk => by
        have : ¬ (α k ≤ R j) := fun h =>
          absurd ((BCSol.sup_char' (fun k : Fin N => α k ≤ R j)
            (fun a b hab hb => le_trans (hα hab) hb) k).2 h)
            (by unfold nAlpha at hk; omega)
        push Not at this
        exact this.le)
  have hx : ∀ k j, xAlpha R β α k j =
      β j * max 0 (BCSol.cv α (R j) (nAlpha R α j) - BCSol.lamv α k) := by
    intro k j; unfold xAlpha; rw [BCSol.closedForm_eq]
  simp only [hx]
  rw [Finset.mul_sum, Finset.sum_comm, ← Finset.sum_add_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e := (hmk j).2.2.1 i
  have e2 : ((i : ℕ) + 2 : ℝ) * (V j * (β j * max 0 (BCSol.cv α (R j) (nAlpha R α j)
        - BCSol.lamv α i))) + ∑ k ∈ univ.filter (fun k => i < k),
        V j * (β j * max 0 (BCSol.cv α (R j) (nAlpha R α j) - BCSol.lamv α k))
      = V j * β j * (((i : ℕ) + 2 : ℝ) * max 0 (BCSol.cv α (R j) (nAlpha R α j)
        - BCSol.lamv α i) + ∑ k ∈ univ.filter (fun k => i < k),
        max 0 (BCSol.cv α (R j) (nAlpha R α j) - BCSol.lamv α k)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [e2, e]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · push Not at h; rw [max_eq_right (by linarith)]; ring
