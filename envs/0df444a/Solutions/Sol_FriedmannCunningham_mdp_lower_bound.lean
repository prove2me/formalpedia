-- Prove2me | solution 1 for FriedmannCunningham.mdp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T07:12:38.306128+00:00
-- url     : https://prove2.me/submissions/6ca952fd-e4f7-4ce1-be15-6a0d4f0bae16

import Definitions.Def_friedmann_cunningham
import Theorems.Thm_FriedmannCunningham_mdp_valid
import Theorems.Thm_FriedmannCunningham_lp_valid
import Theorems.Thm_FriedmannCunningham_policy_pivot
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FriedmannCunningham

open FriedmannSimplex
open scoped BigOperators
open Matrix

@[ext]
lemma Name.ext {u v : Name} (h1 : u.kind = v.kind) (h2 : u.level = v.level) (h3 : u.one = v.one) :
    u = v := by
  cases u; cases v; simp_all

/-! ### Part 1: Row and Column Roundtrip Infrastructure and Transitions -/

def ValidRow (n : ℕ) (p : Kind × ℕ) : Prop :=
  match p.1 with
  | .a => 2 ≤ p.2 ∧ p.2 ≤ n
  | .b => 2 ≤ p.2 ∧ p.2 ≤ n - 1
  | .c => 2 ≤ p.2 ∧ p.2 ≤ n
  | .d => 2 ≤ p.2 ∧ p.2 ≤ n
  | .e => 1 ≤ p.2 ∧ p.2 ≤ n

instance instDecidableValidRow (n : ℕ) (p : Kind × ℕ) : Decidable (ValidRow n p) := by
  rcases p with ⟨k, i⟩
  cases k <;> dsimp [ValidRow] <;> infer_instance

lemma rowName_valid {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) :
    ValidRow n (rowName n r) := by
  have hr := r.isLt
  unfold rows at hr
  unfold rowName
  split_ifs <;> dsimp [ValidRow] <;> omega

lemma rowRank_lt_rows {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    rowRank n p < rows n := by
  rcases p with ⟨k, i⟩
  cases k <;> dsimp [ValidRow, rowRank, rows] at hp ⊢ <;> omega

lemma rowRank_rowName {n : ℕ} (_hn : 3 ≤ n) (r : Fin (rows n)) :
    rowRank n (rowName n r) = r.val := by
  have hr := r.isLt
  unfold rows at hr
  unfold rowName
  split_ifs <;> dsimp [rowRank] <;> omega

lemma rowName_rowRank {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    rowName n ⟨rowRank n p, rowRank_lt_rows hn hp⟩ = p := by
  rcases p with ⟨k, i⟩
  cases k <;> dsimp [ValidRow, rowRank, rowName] at hp ⊢ <;>
    split_ifs <;> first | omega | exact Prod.ext rfl (by omega)

def mkRow (n : ℕ) (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) : Fin (rows n) :=
  ⟨rowRank n p, rowRank_lt_rows hn hp⟩

@[simp]
lemma rowName_mkRow {n : ℕ} (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) :
    rowName n (mkRow n hn p hp) = p :=
  rowName_rowRank hn hp

lemma rowName_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (rowName n) := by
  intro q r hqr
  apply Fin.ext
  rw [← rowRank_rowName hn q, ← rowRank_rowName hn r, hqr]

lemma mkRow_rowName {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) :
    mkRow n hn (rowName n r) (rowName_valid hn r) = r := by
  apply rowName_injective hn
  exact rowName_mkRow hn _ _

lemma rowName_eq_iff {n : ℕ} (hn : 3 ≤ n) (q : Fin (rows n)) (p : Kind × ℕ) (hp : ValidRow n p) :
    rowName n q = p ↔ q = mkRow n hn p hp := by
  constructor
  · intro h
    apply rowName_injective hn
    rw [h, rowName_mkRow]
  · rintro rfl
    exact rowName_mkRow hn p hp

lemma eq_mkRow_iff_of_rowName {n : ℕ} (hn : 3 ≤ n) {q : Fin (rows n)} {kq : Kind} {i : ℕ}
    (hq : rowName n q = (kq, i)) (p : Kind × ℕ) (hp : ValidRow n p) :
    q = mkRow n hn p hp ↔ (kq, i) = p := by
  rw [← rowName_eq_iff hn q p hp, hq]

lemma columnRank_lt_cols {n : ℕ} (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) (b : Bool) :
    columnRank n ⟨p.1, p.2, b⟩ < cols n := by
  rcases p with ⟨k, i⟩
  cases k <;> cases b <;> dsimp [ValidRow, columnRank, cols] at hp ⊢ <;>
    (try split_ifs) <;> omega

lemma actionColumn_val {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) (b : Bool) :
    (actionColumn n hn r b).val = columnRank n ⟨(rowName n r).1, (rowName n r).2, b⟩ := by
  dsimp [actionColumn]
  exact Nat.mod_eq_of_lt (columnRank_lt_cols hn (rowName n r) (rowName_valid hn r) b)

lemma columnName_of_val {n : ℕ} (j : Fin (cols n)) (m : ℕ) (hm : j.val = m) :
    columnName n j =
      if m = 0 then ⟨.e, 1, true⟩
      else if m < 4 * n - 5 then
        let i := (m - 1) / 4 + 2
        match (m - 1) % 4 with
        | 0 => ⟨.d, i, false⟩
        | 1 => ⟨.e, i, true⟩
        | 2 => ⟨.b, i, true⟩
        | _ => ⟨.b, i, false⟩
      else if m < 6 * n - 7 then
        ⟨.c, (m - (4 * n - 5)) / 2 + 2, decide ((m - (4 * n - 5)) % 2 = 1)⟩
      else if m < 7 * n - 7 then ⟨.e, m - (6 * n - 7) + 1, false⟩
      else if m < 8 * n - 8 then ⟨.d, m - (7 * n - 7) + 2, true⟩
      else ⟨.a, n - (m - (8 * n - 8)) / 2, decide ((m - (8 * n - 8)) % 2 = 0)⟩ := by
  unfold columnName
  dsimp only
  subst hm
  rfl

lemma columnName_columnRank {n : ℕ} (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) (b : Bool)
    (h : columnRank n ⟨p.1, p.2, b⟩ % cols n < cols n) :
    columnName n ⟨columnRank n ⟨p.1, p.2, b⟩ % cols n, h⟩ = ⟨p.1, p.2, b⟩ := by
  rcases p with ⟨k, i⟩
  have hlt : columnRank n ⟨k, i, b⟩ < cols n := columnRank_lt_cols hn (k, i) hp b
  set j0 : Fin (cols n) := ⟨columnRank n ⟨k, i, b⟩ % cols n, h⟩
  have hmod : j0.val = columnRank n ⟨k, i, b⟩ := Nat.mod_eq_of_lt hlt
  cases k <;> cases b <;> dsimp [ValidRow, columnRank] at hp hmod ⊢
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_false_iff_not]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_true_eq]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
    dsimp only
    have hrem : (4 * (i - 2) + 4 - 1) % 4 = 3 := by omega
    have hdiv : (4 * (i - 2) + 4 - 1) / 4 + 2 = i := by omega
    rw [hrem, hdiv]; rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
    dsimp only
    have hrem : (4 * (i - 2) + 3 - 1) % 4 = 2 := by omega
    have hdiv : (4 * (i - 2) + 3 - 1) / 4 + 2 = i := by omega
    rw [hrem, hdiv]; rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_false_iff_not]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_true_eq]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
    dsimp only
    have hrem : (4 * (i - 2) + 1 - 1) % 4 = 0 := by omega
    have hdiv : (4 * (i - 2) + 1 - 1) / 4 + 2 = i := by omega
    rw [hrem, hdiv]; rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) rfl
  · by_cases hi1 : i = 1
    · subst hi1
      rw [if_pos rfl] at hmod
      rw [columnName_of_val j0 _ hmod]
      simp
    · rw [if_neg hi1] at hmod
      rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
      dsimp only
      have hrem : (4 * (i - 2) + 2 - 1) % 4 = 1 := by omega
      have hdiv : (4 * (i - 2) + 2 - 1) / 4 + 2 = i := by omega
      rw [hrem, hdiv]; rfl

lemma columnName_actionColumn (n : ℕ) (hn : 3 ≤ n) (r : Fin (rows n)) (b : Bool) :
    columnName n (actionColumn n hn r b) = ⟨(rowName n r).1, (rowName n r).2, b⟩ :=
  columnName_columnRank hn (rowName n r) (rowName_valid hn r) b _

lemma actionColumn_inj {n : ℕ} (hn : 3 ≤ n) {r₁ r₂ : Fin (rows n)} {b₁ b₂ : Bool}
    (h : actionColumn n hn r₁ b₁ = actionColumn n hn r₂ b₂) :
    r₁ = r₂ ∧ b₁ = b₂ := by
  have hc := congrArg (columnName n) h
  rw [columnName_actionColumn, columnName_actionColumn, Name.ext_iff] at hc
  rcases hc with ⟨h1, h2, h3⟩
  exact ⟨rowName_injective hn (Prod.ext h1 h2), h3⟩

lemma epsilon_pos (n : ℕ) : 0 < epsilon n := by
  unfold epsilon scale
  positivity

lemma epsilon_lt_one {n : ℕ} (hn : 3 ≤ n) : epsilon n < 1 := by
  unfold epsilon
  rw [div_lt_iff₀]
  · rw [one_mul]
    have hscale : (1 : ℚ) < scale n := by
      unfold scale
      have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      linarith
    exact one_lt_pow₀ hscale (by omega)
  · unfold scale
    positivity

lemma own_eq_ite {n : ℕ} (hn : 3 ≤ n) (r q : Fin (rows n)) (b : Bool) :
    let v : Name := ⟨(rowName n r).1, (rowName n r).2, b⟩
    indicator v (rowName n q).1 (rowName n q).2 false +
      indicator v (rowName n q).1 (rowName n q).2 true =
    if q = r then 1 else 0 := by
  dsimp [indicator]
  by_cases hqr : q = r
  · subst hqr
    cases b <;> simp
  · rw [if_neg hqr]
    have hne : rowName n q ≠ rowName n r := fun h => hqr (rowName_injective hn h)
    have h1 : ¬ ((rowName n r).1 = (rowName n q).1 ∧ (rowName n r).2 = (rowName n q).2 ∧ b = false) := by
      rintro ⟨h1, h2, _⟩
      exact hne (Prod.ext h1.symm h2.symm)
    have h2 : ¬ ((rowName n r).1 = (rowName n q).1 ∧ (rowName n r).2 = (rowName n q).2 ∧ b = true) := by
      rintro ⟨h1, h2, _⟩
      exact hne (Prod.ext h1.symm h2.symm)
    simp [Name.ext_iff, h1, h2]

lemma active_sum_eq (v : Name) (m : ℕ) :
    indicator v .a m true + indicator v .b m true + indicator v .c m true +
      indicator v .d m true + indicator v .e m true =
    if v.level = m ∧ v.one = true then 1 else 0 := by
  rcases v with ⟨k, j, b⟩
  cases k <;> cases b <;> dsimp [indicator] <;>
    by_cases h : j = m <;> simp [h]

lemma sum_indicator_e_false (n : ℕ) (v : Name) :
    (∑ j ∈ Finset.range (n + 1), indicator v .e j false) =
      if v.kind = .e ∧ v.level ≤ n ∧ v.one = false then 1 else 0 := by
  rcases v with ⟨k, l, b⟩
  by_cases h : k = .e ∧ l ≤ n ∧ b = false
  · rcases h with ⟨rfl, hl, rfl⟩
    simp only [hl, and_self, ↓reduceIte]
    have hmem : l ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hcongr : ∀ j ∈ Finset.range (n + 1),
        indicator ⟨.e, l, false⟩ .e j false = if l = j then 1 else 0 := by
      intro j _
      dsimp [indicator]
      simp [Name.ext_iff]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq, if_pos hmem]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    dsimp [indicator]
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact h ⟨rfl, by omega, rfl⟩

lemma transition_eq {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) (b : Bool) (q : Fin (rows n)) :
    transition n hn r b q =
      let v : Name := ⟨(rowName n r).1, (rowName n r).2, b⟩
      let i := (rowName n q).2
      match (rowName n q).1 with
      | .a =>
          if i = 2 then epsilon n *
            (indicator v .b 2 false + indicator v .c 2 false +
              indicator v .d 2 false + indicator v .e 1 true)
          else indicator v .a (i - 1) false +
            epsilon n * (if (rowName n r).2 = i - 1 ∧ b = true then 1 else 0)
      | .b => indicator v .b (i + 1) false + indicator v .d (i + 1) false
      | .c =>
          if i = n then (if (rowName n r).1 = .e ∧ (rowName n r).2 ≤ n ∧ b = false then 1 else 0)
          else indicator v .c (i + 1) false
      | .d => (1 - epsilon n) / 2 * (if (rowName n r).2 = i ∧ b = true then 1 else 0)
      | .e =>
          if i = 1 then (1 - epsilon n) *
            (indicator v .b 2 false + indicator v .c 2 false +
              indicator v .d 2 false + indicator v .e 1 true)
          else (1 - epsilon n) / 2 * (if (rowName n r).2 = i ∧ b = true then 1 else 0) := by
  unfold transition program
  dsimp only
  rw [columnName_actionColumn]
  unfold coefficient
  dsimp only
  have hown := own_eq_ite hn r q b
  dsimp only at hown
  rw [hown]
  generalize (if q = r then (1 : ℚ) else 0) = own_val
  set v : Name := ⟨(rowName n r).1, (rowName n r).2, b⟩
  cases (rowName n q).1 <;> dsimp only
  · rw [active_sum_eq v ((rowName n q).2 - 1)]; dsimp only [v]; split_ifs <;> ring
  · ring
  · rw [sum_indicator_e_false n v]; dsimp only [v]; split_ifs <;> ring
  · rw [active_sum_eq v (rowName n q).2]; dsimp only [v]; ring
  · rw [active_sum_eq v (rowName n q).2]; dsimp only [v]; split_ifs <;> ring

lemma valid_a_two {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.a, 2) := by dsimp [ValidRow]; omega
lemma valid_e_one {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.e, 1) := by dsimp [ValidRow]; omega
lemma valid_c_n {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.c, n) := by dsimp [ValidRow]; omega
lemma valid_d_n {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.d, n) := by dsimp [ValidRow]; omega
lemma valid_e_n {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.e, n) := by dsimp [ValidRow]; omega

lemma trans_a_false_lt {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)} {j : ℕ}
    (hr : rowName n r = (.a, j)) (_hj : j < n) (ha : ValidRow n (.a, j + 1)) (q : Fin (rows n)) :
    transition n hn r false q = if q = mkRow n hn (.a, j + 1) ha then 1 else 0 := by
  have hvp := rowName_valid hn r; rw [hr] at hvp
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r false q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  cases kq <;> dsimp [ValidRow, indicator] at hvp hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_a_false_eq {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)}
    (hr : rowName n r = (.a, n)) (q : Fin (rows n)) :
    transition n hn r false q = 0 := by
  have hvp := rowName_valid hn r; rw [hr] at hvp
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r false q, hr, hq]
  dsimp only
  cases kq <;> dsimp [ValidRow, indicator] at hvp hvq ⊢ <;>
    (try simp only [Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_bcd_false_two {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)} {k : Kind}
    (hr : rowName n r = (k, 2)) (hk : k = .b ∨ k = .c ∨ k = .d) (q : Fin (rows n)) :
    transition n hn r false q =
      (if q = mkRow n hn (.a, 2) (valid_a_two hn) then epsilon n else 0) +
      (if q = mkRow n hn (.e, 1) (valid_e_one hn) then 1 - epsilon n else 0) := by
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r false q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  rcases hk with rfl | rfl | rfl <;>
    cases kq <;> dsimp [ValidRow, indicator] at hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_bd_false_gt {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)} {k : Kind} {j : ℕ}
    (hr : rowName n r = (k, j)) (hk : k = .b ∨ k = .d) (_hj : 2 < j)
    (hb : ValidRow n (.b, j - 1)) (q : Fin (rows n)) :
    transition n hn r false q = if q = mkRow n hn (.b, j - 1) hb then 1 else 0 := by
  have hvp := rowName_valid hn r; rw [hr] at hvp
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r false q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  rcases hk with rfl | rfl <;>
    cases kq <;> dsimp [ValidRow, indicator] at hvp hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_c_false_gt {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)} {j : ℕ}
    (hr : rowName n r = (.c, j)) (_hj : 2 < j)
    (hc : ValidRow n (.c, j - 1)) (q : Fin (rows n)) :
    transition n hn r false q = if q = mkRow n hn (.c, j - 1) hc then 1 else 0 := by
  have hvp := rowName_valid hn r; rw [hr] at hvp
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r false q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  cases kq <;> dsimp [ValidRow, indicator] at hvp hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_e_false {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)} {j : ℕ}
    (hr : rowName n r = (.e, j)) (q : Fin (rows n)) :
    transition n hn r false q = if q = mkRow n hn (.c, n) (valid_c_n hn) then 1 else 0 := by
  have hvp := rowName_valid hn r; rw [hr] at hvp
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r false q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  cases kq <;> dsimp [ValidRow, indicator] at hvp hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_e_true_one {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)}
    (hr : rowName n r = (.e, 1)) (q : Fin (rows n)) :
    transition n hn r true q =
      (if q = mkRow n hn (.a, 2) (valid_a_two hn) then epsilon n else 0) +
      (if q = mkRow n hn (.e, 1) (valid_e_one hn) then 1 - epsilon n else 0) := by
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r true q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  cases kq <;> dsimp [ValidRow, indicator] at hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_true_lt {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)} {k : Kind} {j : ℕ}
    (hr : rowName n r = (k, j)) (_hj2 : 2 ≤ j) (_hjn : j < n)
    (ha : ValidRow n (.a, j + 1)) (hd : ValidRow n (.d, j)) (he : ValidRow n (.e, j))
    (q : Fin (rows n)) :
    transition n hn r true q =
      (if q = mkRow n hn (.a, j + 1) ha then epsilon n else 0) +
      (if q = mkRow n hn (.d, j) hd then (1 - epsilon n) / 2 else 0) +
      (if q = mkRow n hn (.e, j) he then (1 - epsilon n) / 2 else 0) := by
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r true q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  cases k <;> cases kq <;> dsimp [ValidRow, indicator] at hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

lemma trans_true_eq {n : ℕ} (hn : 3 ≤ n) {r : Fin (rows n)} {k : Kind}
    (hr : rowName n r = (k, n)) (q : Fin (rows n)) :
    transition n hn r true q =
      (if q = mkRow n hn (.d, n) (valid_d_n hn) then (1 - epsilon n) / 2 else 0) +
      (if q = mkRow n hn (.e, n) (valid_e_n hn) then (1 - epsilon n) / 2 else 0) := by
  rcases hq : rowName n q with ⟨kq, i⟩
  have hvq := rowName_valid hn q; rw [hq] at hvq
  rw [transition_eq hn r true q, hr, hq]
  dsimp only
  simp only [eq_mkRow_iff_of_rowName hn hq]
  cases k <;> cases kq <;> dsimp [ValidRow, indicator] at hvq ⊢ <;>
    (try simp only [Prod.mk.injEq, Name.ext_iff, reduceCtorEq,
      and_false, true_and, and_true, ↓reduceIte]) <;>
    (try split_ifs) <;> first | omega | ring

/-! ### Part 2: Universal Bellman Equation and `qFormula` -/

def valAt (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (k : Kind) (i : ℕ) : ℚ :=
  if h : ValidRow n (k, i) then V (mkRow n hn (k, i) h) else 0

@[simp]
lemma valAt_of_valid {n : ℕ} (hn : 3 ≤ n) (V : Fin (rows n) → ℚ)
    {k : Kind} {i : ℕ} (h : ValidRow n (k, i)) :
    valAt n hn V k i = V (mkRow n hn (k, i) h) :=
  dif_pos h

lemma valAt_rowName {n : ℕ} (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (r : Fin (rows n)) :
    valAt n hn V (rowName n r).1 (rowName n r).2 = V r := by
  have hv : ValidRow n ((rowName n r).1, (rowName n r).2) := rowName_valid hn r
  rw [valAt_of_valid hn V hv]
  congr 1
  exact mkRow_rowName hn r

@[simp]
lemma valAt_a_gt {n : ℕ} (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) {i : ℕ} (hi : n < i) :
    valAt n hn V .a i = 0 := by
  unfold valAt
  rw [dif_neg]
  dsimp [ValidRow]
  omega

def HVal (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (i : ℕ) : ℚ :=
  rewardH n i + valAt n hn V .a (i + 1)

def G1Val (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) : ℚ :=
  rewardG n 1 + epsilon n * HVal n hn V 1 + (1 - epsilon n) * valAt n hn V .e 1

def BPrev (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (i : ℕ) : ℚ :=
  if i = 2 then G1Val n hn V else valAt n hn V .b (i - 1)

def CPrev (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (i : ℕ) : ℚ :=
  if i = 2 then G1Val n hn V else valAt n hn V .c (i - 1)

def FRhs (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (i : ℕ) : ℚ :=
  epsilon n * HVal n hn V i + (1 - epsilon n) / 2 * valAt n hn V .d i +
    (1 - epsilon n) / 2 * valAt n hn V .e i

def GRhs (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (i : ℕ) : ℚ :=
  rewardG n i + FRhs n hn V i

def qFormula (n : ℕ) (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (k : Kind) (i : ℕ) (b : Bool) : ℚ :=
  match k, b with
  | .a, false => valAt n hn V .a (i + 1)
  | .a, true  => GRhs n hn V i
  | .b, false => BPrev n hn V i
  | .b, true  => GRhs n hn V i
  | .c, false => CPrev n hn V i
  | .c, true  => GRhs n hn V i
  | .d, false => BPrev n hn V i
  | .d, true  => FRhs n hn V i
  | .e, false => 1 + valAt n hn V .c n
  | .e, true  =>
      if i = 1 then epsilon n * HVal n hn V 1 + (1 - epsilon n) * valAt n hn V .e 1
      else FRhs n hn V i

lemma actionReward_eq {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) (b : Bool) :
    actionReward n hn r b =
      objectiveCoefficient n ⟨(rowName n r).1, (rowName n r).2, b⟩ := by
  unfold actionReward program
  dsimp only
  rw [columnName_actionColumn]

lemma qVal_eq_qFormula {n : ℕ} (hn : 3 ≤ n) (V : Fin (rows n) → ℚ) (r : Fin (rows n)) (b : Bool) :
    actionReward n hn r b + (∑ q : Fin (rows n), transition n hn r b q * V q) =
      qFormula n hn V (rowName n r).1 (rowName n r).2 b := by
  have hp := rowName_valid hn r
  rcases hr : rowName n r with ⟨k, j⟩
  rw [hr] at hp
  rw [actionReward_eq hn r b, hr]
  dsimp only
  cases b
  · cases k <;> dsimp [ValidRow] at hp
    · by_cases hj : j < n
      · have ha : ValidRow n (.a, j + 1) := by dsimp [ValidRow]; omega
        simp [trans_a_false_lt hn hr hj ha, qFormula, objectiveCoefficient, indicator,
          valAt_of_valid hn V ha]
      · have hjn : j = n := by omega
        subst j
        simp [trans_a_false_eq hn hr, qFormula, objectiveCoefficient, indicator]
    · by_cases hj : j = 2
      · subst j
        simp only [trans_bcd_false_two hn hr (Or.inl rfl), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          qFormula, BPrev, G1Val, HVal, objectiveCoefficient, indicator, Name.ext_iff,
          reduceCtorEq, and_self, false_and, valAt_of_valid hn V (valid_a_two hn),
          valAt_of_valid hn V (valid_e_one hn)]
        ring
      · have hjgt : 2 < j := by omega
        have hb : ValidRow n (.b, j - 1) := by dsimp [ValidRow]; omega
        simp [trans_bd_false_gt hn hr (Or.inl rfl) hjgt hb, qFormula, BPrev, hj,
          objectiveCoefficient, indicator, Name.ext_iff, valAt_of_valid hn V hb]
    · by_cases hj : j = 2
      · subst j
        simp only [trans_bcd_false_two hn hr (Or.inr (Or.inl rfl)), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          qFormula, CPrev, G1Val, HVal, objectiveCoefficient, indicator, Name.ext_iff,
          reduceCtorEq, and_self, false_and, valAt_of_valid hn V (valid_a_two hn),
          valAt_of_valid hn V (valid_e_one hn)]
        ring
      · have hjgt : 2 < j := by omega
        have hc : ValidRow n (.c, j - 1) := by dsimp [ValidRow]; omega
        simp [trans_c_false_gt hn hr hjgt hc, qFormula, CPrev, hj,
          objectiveCoefficient, indicator, Name.ext_iff, valAt_of_valid hn V hc]
    · by_cases hj : j = 2
      · subst j
        simp only [trans_bcd_false_two hn hr (Or.inr (Or.inr rfl)), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          qFormula, BPrev, G1Val, HVal, objectiveCoefficient, indicator, Name.ext_iff,
          reduceCtorEq, and_self, false_and, valAt_of_valid hn V (valid_a_two hn),
          valAt_of_valid hn V (valid_e_one hn)]
        ring
      · have hjgt : 2 < j := by omega
        have hb : ValidRow n (.b, j - 1) := by dsimp [ValidRow]; omega
        simp [trans_bd_false_gt hn hr (Or.inr rfl) hjgt hb, qFormula, BPrev, hj,
          objectiveCoefficient, indicator, Name.ext_iff, valAt_of_valid hn V hb]
    · simp [trans_e_false hn hr, qFormula, objectiveCoefficient, indicator,
        valAt_of_valid hn V (valid_c_n hn)]
  · have hj_cases : (k = .e ∧ j = 1) ∨ (2 ≤ j ∧ j ≤ n) := by
      cases k <;> dsimp [ValidRow] at hp <;> simp <;> omega
    rcases hj_cases with ⟨rfl, rfl⟩ | ⟨hj2, hjn⟩
    · simp only [trans_e_true_one hn hr, add_mul, ite_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        qFormula, HVal, objectiveCoefficient, indicator, Name.ext_iff, reduceCtorEq, and_false,
        valAt_of_valid hn V (valid_a_two hn), valAt_of_valid hn V (valid_e_one hn)]
      ring
    · by_cases hjlt : j < n
      · have ha : ValidRow n (.a, j + 1) := by dsimp [ValidRow]; omega
        have hd : ValidRow n (.d, j) := by dsimp [ValidRow]; omega
        have he : ValidRow n (.e, j) := by dsimp [ValidRow]; omega
        have hj1 : j ≠ 1 := by omega
        cases k <;>
          simp only [trans_true_lt hn hr hj2 hjlt ha hd he, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            qFormula, GRhs, FRhs, HVal, hj1, objectiveCoefficient, indicator, Name.ext_iff,
            reduceCtorEq, and_false, valAt_of_valid hn V ha, valAt_of_valid hn V hd,
            valAt_of_valid hn V he] <;> ring
      · have hjeq : j = n := by omega
        subst j
        have hn1 : n ≠ 1 := by omega
        cases k <;>
          simp only [trans_true_eq hn hr, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            qFormula, GRhs, FRhs, HVal, hn1, objectiveCoefficient, indicator, Name.ext_iff,
            reduceCtorEq, and_false, valAt_a_gt hn V (by omega : n < n + 1),
            valAt_of_valid hn V (valid_d_n hn), valAt_of_valid hn V (valid_e_n hn)] <;> ring

lemma policyValue_bellman {n : ℕ} (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    policyValue n hn σ r =
      actionReward n hn r (σ r) +
        ∑ q : Fin (rows n), transition n hn r (σ r) q * policyValue n hn σ q := by
  set M := basisMatrix (program n) (policyBasis n hn σ)
  set v := policyValue n hn σ
  have hdet : IsUnit Mᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr ((mdp_valid n hn).2.2 σ)
  have hmul : (Mᵀ *ᵥ v) r = actionReward n hn r (σ r) := by
    change (Mᵀ *ᵥ (Mᵀ⁻¹ *ᵥ (fun q => actionReward n hn q (σ q)))) r = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Mᵀ hdet, Matrix.one_mulVec]
  dsimp [mulVec, dotProduct, transpose_apply, M, basisMatrix, policyBasis] at hmul
  have hA : ∀ q, (program n).A q (actionColumn n hn r (σ r)) * v q =
      (if q = r then v q else 0) - transition n hn r (σ r) q * v q := by
    intro q
    unfold transition
    split_ifs <;> ring
  simp only [hA, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hmul
  linarith

lemma policyValue_eq_qFormula {n : ℕ} (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    policyValue n hn σ r =
      qFormula n hn (policyValue n hn σ) (rowName n r).1 (rowName n r).2 (σ r) := by
  rw [policyValue_bellman hn σ r, qVal_eq_qFormula hn (policyValue n hn σ) r (σ r)]

lemma mdpImproving_iff_qFormula {n : ℕ} (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    mdpImproving n hn σ r ↔
      qFormula n hn (policyValue n hn σ) (rowName n r).1 (rowName n r).2 (σ r) <
        qFormula n hn (policyValue n hn σ) (rowName n r).1 (rowName n r).2 (!σ r) := by
  unfold mdpImproving
  rw [← policyValue_eq_qFormula hn σ r, qVal_eq_qFormula hn (policyValue n hn σ) r (!σ r)]

/-! ### Part 3: Policy Representation, Local Value Evaluation, and Scale Bounds -/

def policyOf (n : ℕ) (f : Kind → ℕ → Bool) : Policy n :=
  fun r => f (rowName n r).1 (rowName n r).2

@[simp]
lemma policyOf_mkRow {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {k : Kind} {i : ℕ} (h : ValidRow n (k, i)) :
    policyOf n f (mkRow n hn (k, i) h) = f k i := by
  unfold policyOf
  rw [rowName_mkRow]

lemma policyOf_ext {n : ℕ} (hn : 3 ≤ n) {f₁ f₂ : Kind → ℕ → Bool}
    (h : ∀ k i, ValidRow n (k, i) → f₁ k i = f₂ k i) :
    policyOf n f₁ = policyOf n f₂ := by
  ext r
  exact h (rowName n r).1 (rowName n r).2 (rowName_valid hn r)

lemma update_policyOf_eq {n : ℕ} (hn : 3 ≤ n) {f₁ f₂ : Kind → ℕ → Bool}
    (k₀ : Kind) (i₀ : ℕ) (h₀ : ValidRow n (k₀, i₀))
    (h : ∀ k i, ValidRow n (k, i) →
      (if k = k₀ ∧ i = i₀ then !f₁ k₀ i₀ else f₁ k i) = f₂ k i) :
    Function.update (policyOf n f₁) (mkRow n hn (k₀, i₀) h₀)
      (!(policyOf n f₁) (mkRow n hn (k₀, i₀) h₀)) = policyOf n f₂ := by
  ext r
  have hv := rowName_valid hn r
  rcases hr : rowName n r with ⟨k, i⟩
  rw [hr] at hv
  have hreq : r = mkRow n hn (k₀, i₀) h₀ ↔ k = k₀ ∧ i = i₀ := by
    rw [← rowName_eq_iff hn r (k₀, i₀) h₀, hr, Prod.mk.injEq]
  by_cases hki : k = k₀ ∧ i = i₀
  · have hr0 : r = mkRow n hn (k₀, i₀) h₀ := hreq.mpr hki
    subst hr0
    simp only [Function.update_self, policyOf_mkRow]
    have h1 := h k₀ i₀ h₀
    rw [if_pos ⟨rfl, rfl⟩] at h1
    exact h1
  · have hr0 : r ≠ mkRow n hn (k₀, i₀) h₀ := fun h' => hki (hreq.mp h')
    simp only [Function.update_of_ne hr0, policyOf, hr]
    have h1 := h k i hv
    rw [if_neg hki] at h1
    exact h1

lemma valAt_policyValue {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {k : Kind} {i : ℕ} (h : ValidRow n (k, i)) :
    valAt n hn (policyValue n hn (policyOf n f)) k i =
      qFormula n hn (policyValue n hn (policyOf n f)) k i (f k i) := by
  rw [valAt_of_valid hn _ h, policyValue_eq_qFormula hn (policyOf n f) (mkRow n hn (k, i) h),
    rowName_mkRow, policyOf_mkRow]

lemma mdpImproving_policyOf_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {k : Kind} {i : ℕ} (h : ValidRow n (k, i)) :
    mdpImproving n hn (policyOf n f) (mkRow n hn (k, i) h) ↔
      qFormula n hn (policyValue n hn (policyOf n f)) k i (f k i) <
        qFormula n hn (policyValue n hn (policyOf n f)) k i (!f k i) := by
  rw [mdpImproving_iff_qFormula, rowName_mkRow, policyOf_mkRow]

lemma valAt_e_one_of_true {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) (hf : f .e 1 = true) :
    valAt n hn (policyValue n hn (policyOf n f)) .e 1 =
      HVal n hn (policyValue n hn (policyOf n f)) 1 := by
  have h := valAt_policyValue hn f (valid_e_one hn)
  rw [hf] at h
  dsimp [qFormula] at h
  have heps : 0 < epsilon n := epsilon_pos n
  nlinarith

lemma G1Val_of_e_one_true {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) (hf : f .e 1 = true) :
    G1Val n hn (policyValue n hn (policyOf n f)) =
      rewardG n 1 + rewardH n 1 + valAt n hn (policyValue n hn (policyOf n f)) .a 2 := by
  unfold G1Val
  rw [valAt_e_one_of_true hn f hf]
  unfold HVal
  ring

lemma valAt_e_one_of_false {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) (hf : f .e 1 = false) :
    valAt n hn (policyValue n hn (policyOf n f)) .e 1 =
      1 + valAt n hn (policyValue n hn (policyOf n f)) .c n := by
  have h := valAt_policyValue hn f (valid_e_one hn)
  rw [hf] at h
  exact h

lemma FRhs_of_de_true_true {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {i : ℕ}
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hd : f .d i = true) (he : f .e i = true) :
    FRhs n hn (policyValue n hn (policyOf n f)) i =
      HVal n hn (policyValue n hn (policyOf n f)) i := by
  set V := policyValue n hn (policyOf n f)
  have hvd : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hve : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hd_eq := valAt_policyValue hn f hvd
  have he_eq := valAt_policyValue hn f hve
  rw [hd] at hd_eq
  rw [he] at he_eq
  have hi1 : i ≠ 1 := by omega
  dsimp [qFormula] at hd_eq he_eq
  rw [if_neg hi1] at he_eq
  have hF : FRhs n hn V i = epsilon n * HVal n hn V i +
      (1 - epsilon n) / 2 * valAt n hn V .d i + (1 - epsilon n) / 2 * valAt n hn V .e i := rfl
  rw [hd_eq, he_eq] at hF
  have heps : 0 < epsilon n := epsilon_pos n
  nlinarith

lemma GRhs_of_de_true_true {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {i : ℕ}
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hd : f .d i = true) (he : f .e i = true) :
    GRhs n hn (policyValue n hn (policyOf n f)) i =
      rewardG n i + rewardH n i + valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) := by
  unfold GRhs
  rw [FRhs_of_de_true_true hn f hi2 hin hd he]
  unfold HVal
  ring

lemma FRhs_of_de_true_false {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {i : ℕ}
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hd : f .d i = true) (he : f .e i = false) :
    (1 + epsilon n) * (FRhs n hn (policyValue n hn (policyOf n f)) i -
        (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) =
      2 * epsilon n * (HVal n hn (policyValue n hn (policyOf n f)) i -
        (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) := by
  set V := policyValue n hn (policyOf n f)
  have hvd : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hve : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hd_eq := valAt_policyValue hn f hvd
  have he_eq := valAt_policyValue hn f hve
  rw [hd] at hd_eq
  rw [he] at he_eq
  dsimp [qFormula] at hd_eq he_eq
  have hF : FRhs n hn V i = epsilon n * HVal n hn V i +
      (1 - epsilon n) / 2 * valAt n hn V .d i + (1 - epsilon n) / 2 * valAt n hn V .e i := rfl
  rw [hd_eq, he_eq] at hF
  linarith

lemma FRhs_of_de_false_true {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {i : ℕ}
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hd : f .d i = false) (he : f .e i = true) :
    (1 + epsilon n) * (FRhs n hn (policyValue n hn (policyOf n f)) i -
        BPrev n hn (policyValue n hn (policyOf n f)) i) =
      2 * epsilon n * (HVal n hn (policyValue n hn (policyOf n f)) i -
        BPrev n hn (policyValue n hn (policyOf n f)) i) := by
  set V := policyValue n hn (policyOf n f)
  have hvd : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hve : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hd_eq := valAt_policyValue hn f hvd
  have he_eq := valAt_policyValue hn f hve
  rw [hd] at hd_eq
  rw [he] at he_eq
  have hi1 : i ≠ 1 := by omega
  dsimp [qFormula] at hd_eq he_eq
  rw [if_neg hi1] at he_eq
  have hF : FRhs n hn V i = epsilon n * HVal n hn V i +
      (1 - epsilon n) / 2 * valAt n hn V .d i + (1 - epsilon n) / 2 * valAt n hn V .e i := rfl
  rw [hd_eq, he_eq] at hF
  linarith

lemma FRhs_of_de_false_false {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {i : ℕ}
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hd : f .d i = false) (he : f .e i = false) :
    FRhs n hn (policyValue n hn (policyOf n f)) i =
      epsilon n * HVal n hn (policyValue n hn (policyOf n f)) i +
        (1 - epsilon n) / 2 * BPrev n hn (policyValue n hn (policyOf n f)) i +
        (1 - epsilon n) / 2 * (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n) := by
  set V := policyValue n hn (policyOf n f)
  have hvd : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hve : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hd_eq := valAt_policyValue hn f hvd
  have he_eq := valAt_policyValue hn f hve
  rw [hd] at hd_eq
  rw [he] at he_eq
  dsimp [qFormula] at hd_eq he_eq
  unfold FRhs
  rw [hd_eq, he_eq]

def vaBase (n b i : ℕ) : ℚ :=
  ∑ j ∈ Finset.Ico i (n + 1),
    if b.testBit (j - 1) then rewardG n j + rewardH n j else 0

lemma vaBase_gt {n b i : ℕ} (hi : n < i) : vaBase n b i = 0 := by
  unfold vaBase
  rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]

lemma vaBase_step {n b i : ℕ} (hi : i ≤ n) :
    vaBase n b i =
      (if b.testBit (i - 1) then rewardG n i + rewardH n i else 0) + vaBase n b (i + 1) := by
  unfold vaBase
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i < n + 1)]

lemma valAt_a_eq_vaBase_aux {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) (b : ℕ) :
    ∀ d i : ℕ, n + 1 - i = d → 2 ≤ i →
      (∀ j, i ≤ j → j ≤ n → f .a j = b.testBit (j - 1)) →
      (∀ j, i ≤ j → j ≤ n → b.testBit (j - 1) = true → f .d j = true ∧ f .e j = true) →
      valAt n hn (policyValue n hn (policyOf n f)) .a i = vaBase n b i
  | 0, i, hd, _, _, _ => by
    have hi : n < i := by omega
    rw [valAt_a_gt hn _ hi, vaBase_gt hi]
  | d + 1, i, hd, hi2, ha, hde => by
    have hin : i ≤ n := by omega
    have hva : ValidRow n (.a, i) := ⟨hi2, hin⟩
    have ih := valAt_a_eq_vaBase_aux hn f b d (i + 1) (by omega) (by omega)
      (fun j hj1 hj2 => ha j (by omega) hj2)
      (fun j hj1 hj2 hb => hde j (by omega) hj2 hb)
    rw [valAt_policyValue hn f hva, vaBase_step hin, ha i (le_refl i) hin]
    cases hb : b.testBit (i - 1)
    · dsimp [qFormula]
      linarith
    · rcases hde i (le_refl i) hin hb with ⟨hdi, hei⟩
      dsimp [qFormula]
      rw [GRhs_of_de_true_true hn f hi2 hin hdi hei, ih]

lemma valAt_a_eq_vaBase {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) (b i : ℕ) (hi2 : 2 ≤ i)
    (ha : ∀ j, i ≤ j → j ≤ n → f .a j = b.testBit (j - 1))
    (hde : ∀ j, i ≤ j → j ≤ n → b.testBit (j - 1) = true → f .d j = true ∧ f .e j = true) :
    valAt n hn (policyValue n hn (policyOf n f)) .a i = vaBase n b i :=
  valAt_a_eq_vaBase_aux hn f b (n + 1 - i) i rfl hi2 ha hde

lemma BPrev_eq_G1Val {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) :
    ∀ i : ℕ, 2 ≤ i → i ≤ n → (∀ j, 2 ≤ j → j < i → f .b j = false) →
      BPrev n hn (policyValue n hn (policyOf n f)) i =
        G1Val n hn (policyValue n hn (policyOf n f))
  | 0, hi2, _, _ => by omega
  | 1, hi2, _, _ => by omega
  | 2, _, _, _ => rfl
  | i + 3, _, hin, hb => by
    unfold BPrev
    rw [if_neg (by omega)]
    have hvb : ValidRow n (.b, i + 2) := ⟨by omega, by omega⟩
    rw [show i + 3 - 1 = i + 2 by omega, valAt_policyValue hn f hvb,
      hb (i + 2) (by omega) (by omega)]
    dsimp [qFormula]
    exact BPrev_eq_G1Val hn f (i + 2) (by omega) (by omega) (fun j hj1 hj2 => hb j hj1 (by omega))

lemma BPrev_eq_Gm {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {m : ℕ}
    (hm2 : 2 ≤ m) (hbm : f .b m = true) (hdm : f .d m = true) (hem : f .e m = true) :
    ∀ i : ℕ, m < i → i ≤ n → (∀ j, m < j → j < i → f .b j = false) →
      BPrev n hn (policyValue n hn (policyOf n f)) i =
        rewardG n m + rewardH n m + valAt n hn (policyValue n hn (policyOf n f)) .a (m + 1)
  | 0, hmi, _, _ => by omega
  | 1, hmi, _, _ => by omega
  | i + 2, hmi, hin, hb => by
    unfold BPrev
    rw [if_neg (by omega)]
    have hvb : ValidRow n (.b, i + 1) := ⟨by omega, by omega⟩
    rw [show i + 2 - 1 = i + 1 by omega, valAt_policyValue hn f hvb]
    rcases eq_or_lt_of_le (by omega : m ≤ i + 1) with rfl | hlt
    · rw [hbm]
      dsimp [qFormula]
      exact GRhs_of_de_true_true hn f hm2 (by omega) hdm hem
    · rw [hb (i + 1) hlt (by omega)]
      dsimp [qFormula]
      exact BPrev_eq_Gm hn f hm2 hbm hdm hem (i + 1) hlt (by omega)
        (fun j hj1 hj2 => hb j hj1 (by omega))

lemma CPrev_eq_G1Val {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) :
    ∀ i : ℕ, 2 ≤ i → i ≤ n → (∀ j, 2 ≤ j → j < i → f .c j = false) →
      CPrev n hn (policyValue n hn (policyOf n f)) i =
        G1Val n hn (policyValue n hn (policyOf n f))
  | 0, hi2, _, _ => by omega
  | 1, hi2, _, _ => by omega
  | 2, _, _, _ => rfl
  | i + 3, _, hin, hc => by
    unfold CPrev
    rw [if_neg (by omega)]
    have hvc : ValidRow n (.c, i + 2) := ⟨by omega, by omega⟩
    rw [show i + 3 - 1 = i + 2 by omega, valAt_policyValue hn f hvc,
      hc (i + 2) (by omega) (by omega)]
    dsimp [qFormula]
    exact CPrev_eq_G1Val hn f (i + 2) (by omega) (by omega) (fun j hj1 hj2 => hc j hj1 (by omega))

lemma valAt_c_n_eq_G1Val {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    (hc : ∀ j, 2 ≤ j → j ≤ n → f .c j = false) :
    valAt n hn (policyValue n hn (policyOf n f)) .c n =
      G1Val n hn (policyValue n hn (policyOf n f)) := by
  rw [valAt_policyValue hn f (valid_c_n hn), hc n (by omega) (le_refl n)]
  dsimp [qFormula]
  exact CPrev_eq_G1Val hn f n (by omega) (le_refl n) (fun j hj1 hj2 => hc j hj1 (by omega))

lemma CPrev_eq_Gm {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {m : ℕ}
    (hm2 : 2 ≤ m) (hcm : f .c m = true) (hdm : f .d m = true) (hem : f .e m = true) :
    ∀ i : ℕ, m < i → i ≤ n → (∀ j, m < j → j < i → f .c j = false) →
      CPrev n hn (policyValue n hn (policyOf n f)) i =
        rewardG n m + rewardH n m + valAt n hn (policyValue n hn (policyOf n f)) .a (m + 1)
  | 0, hmi, _, _ => by omega
  | 1, hmi, _, _ => by omega
  | i + 2, hmi, hin, hc => by
    unfold CPrev
    rw [if_neg (by omega)]
    have hvc : ValidRow n (.c, i + 1) := ⟨by omega, by omega⟩
    rw [show i + 2 - 1 = i + 1 by omega, valAt_policyValue hn f hvc]
    rcases eq_or_lt_of_le (by omega : m ≤ i + 1) with rfl | hlt
    · rw [hcm]
      dsimp [qFormula]
      exact GRhs_of_de_true_true hn f hm2 (by omega) hdm hem
    · rw [hc (i + 1) hlt (by omega)]
      dsimp [qFormula]
      exact CPrev_eq_Gm hn f hm2 hcm hdm hem (i + 1) hlt (by omega)
        (fun j hj1 hj2 => hc j hj1 (by omega))

lemma valAt_c_n_eq_Gm {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool) {m : ℕ}
    (hm2 : 2 ≤ m) (hmn : m ≤ n) (hcm : f .c m = true) (hdm : f .d m = true) (hem : f .e m = true)
    (hc : ∀ j, m < j → j ≤ n → f .c j = false) :
    valAt n hn (policyValue n hn (policyOf n f)) .c n =
      rewardG n m + rewardH n m + valAt n hn (policyValue n hn (policyOf n f)) .a (m + 1) := by
  rw [valAt_policyValue hn f (valid_c_n hn)]
  rcases eq_or_lt_of_le hmn with rfl | hlt
  · rw [hcm]
    dsimp [qFormula]
    exact GRhs_of_de_true_true hn f hm2 (le_refl m) hdm hem
  · rw [hc n hlt (le_refl n)]
    dsimp [qFormula]
    exact CPrev_eq_Gm hn f hm2 hcm hdm hem n hlt (le_refl n)
      (fun j hj1 hj2 => hc j hj1 (by omega))

lemma scale_ge_seven {n : ℕ} (hn : 3 ≤ n) : (7 : ℚ) ≤ scale n := by
  unfold scale
  have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  linarith

lemma scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

lemma rewardG_eq {n i : ℕ} (hi : 1 ≤ i) :
    rewardG n i = -(scale n) ^ (2 * i - 1) := by
  unfold rewardG
  have hodd : Odd (2 * i - 1) := ⟨i - 1, by omega⟩
  exact hodd.neg_pow (scale n)

lemma rewardH_eq (n i : ℕ) :
    rewardH n i = (scale n) ^ (2 * i) := by
  unfold rewardH
  have heven : Even (2 * i) := ⟨i, by ring⟩
  exact heven.neg_pow (scale n)

lemma rewardGH_eq {n i : ℕ} (hi : 1 ≤ i) :
    rewardG n i + rewardH n i = (scale n - 1) * (scale n) ^ (2 * i - 1) := by
  rw [rewardG_eq hi, rewardH_eq]
  have hpow : (scale n) ^ (2 * i) = scale n * (scale n) ^ (2 * i - 1) := by
    rw [← pow_succ', show 2 * i - 1 + 1 = 2 * i by omega]
  rw [hpow]
  ring

lemma rewardGH_ge_42 {n i : ℕ} (hn : 3 ≤ n) (hi : 1 ≤ i) :
    (42 : ℚ) ≤ rewardG n i + rewardH n i := by
  rw [rewardGH_eq hi]
  have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
  have hpow : (scale n) ^ 1 ≤ (scale n) ^ (2 * i - 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  rw [pow_one] at hpow
  nlinarith

lemma rewardGH_nonneg {n j : ℕ} (hn : 3 ≤ n) :
    0 ≤ rewardG n j + rewardH n j := by
  rcases j with _ | j
  · unfold rewardG rewardH; simp
  · have := rewardGH_ge_42 hn (by omega : 1 ≤ j + 1)
    linarith

lemma rewardGH_le_sub_pow {n i : ℕ} (hn : 3 ≤ n) (hi : 1 ≤ i) :
    rewardG n i + rewardH n i ≤ (scale n) ^ (2 * i) - (scale n) ^ (2 * i - 2) := by
  rw [rewardG_eq hi, rewardH_eq]
  have hs : (1 : ℚ) ≤ scale n := by have := scale_ge_seven hn; linarith
  have hle : (scale n) ^ (2 * i - 2) ≤ (scale n) ^ (2 * i - 1) :=
    pow_le_pow_right₀ hs (by omega)
  linarith

lemma sum_rewardGH_Ico_le {n : ℕ} (hn : 3 ≤ n) :
    ∀ k i : ℕ, 1 ≤ i →
      (∑ j ∈ Finset.Ico i (i + k), (rewardG n j + rewardH n j)) ≤
        (scale n) ^ (2 * (i + k - 1)) - (scale n) ^ (2 * i - 2)
  | 0, i, hi => by
    simp only [add_zero, Finset.Ico_self, Finset.sum_empty]
    have heq : 2 * (i - 1) = 2 * i - 2 := by omega
    rw [heq]
    linarith
  | k + 1, i, hi => by
    rw [show i + (k + 1) = (i + k) + 1 by omega,
      Finset.sum_Ico_succ_top (by omega : i ≤ i + k)]
    have ih := sum_rewardGH_Ico_le hn k i hi
    have htop := rewardGH_le_sub_pow hn (by omega : 1 ≤ i + k)
    have heq : 2 * (i + k) - 2 = 2 * (i + k - 1) := by omega
    rw [heq] at htop
    have heq2 : i + k + 1 - 1 = i + k := by omega
    rw [heq2]
    linarith

lemma vaBase_nonneg {n b i : ℕ} (hn : 3 ≤ n) : 0 ≤ vaBase n b i := by
  unfold vaBase
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact rewardGH_nonneg hn
  · linarith

lemma vaBase_le_sum_Ico {n b i m : ℕ} (hn : 3 ≤ n) (hm : n + 1 ≤ m) :
    vaBase n b i ≤ ∑ j ∈ Finset.Ico i m, (rewardG n j + rewardH n j) := by
  unfold vaBase
  calc (∑ j ∈ Finset.Ico i (n + 1), if b.testBit (j - 1) then rewardG n j + rewardH n j else 0)
    _ ≤ ∑ j ∈ Finset.Ico i (n + 1), (rewardG n j + rewardH n j) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · linarith
      · exact rewardGH_nonneg hn
    _ ≤ ∑ j ∈ Finset.Ico i m, (rewardG n j + rewardH n j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Ico_subset_Ico_right hm
      · intro j _ _
        exact rewardGH_nonneg hn

lemma vaBase_le_pow {n b i : ℕ} (hn : 3 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n + 1) :
    vaBase n b i ≤ (scale n) ^ (2 * n) - (scale n) ^ (2 * i - 2) := by
  have h1 := vaBase_le_sum_Ico (b := b) (i := i) hn (le_refl (n + 1))
  have h2 := sum_rewardGH_Ico_le hn (n + 1 - i) i hi
  rw [show i + (n + 1 - i) = n + 1 by omega, show n + 1 - 1 = n by omega] at h2
  linarith

lemma vaBase_le_scale_pow {n b i : ℕ} (hn : 3 ≤ n) (hi1 : 1 ≤ i) :
    vaBase n b i ≤ (scale n) ^ (2 * n) := by
  by_cases hi : i ≤ n + 1
  · have h1 := vaBase_le_pow (b := b) hn hi1 hi
    have hpos : (0 : ℚ) ≤ (scale n) ^ (2 * i - 2) := by
      have := scale_pos n; positivity
    linarith
  · rw [vaBase_gt (by omega)]
    have := scale_pos n
    positivity

lemma vaBase_anti {n b i₁ i₂ : ℕ} (hn : 3 ≤ n) (h : i₁ ≤ i₂) :
    vaBase n b i₂ ≤ vaBase n b i₁ := by
  unfold vaBase
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ico_subset_Ico_left h
  · intro j _ _
    split_ifs
    · exact rewardGH_nonneg hn
    · linarith

lemma vaBase_lt_of_testBit {n b i₁ i₂ : ℕ} (hn : 3 ≤ n) (hi₁ : 1 ≤ i₁)
    (hlt : i₁ < i₂) (hin : i₁ ≤ n) (hb : b.testBit (i₁ - 1) = true) :
    vaBase n b i₂ + 42 ≤ vaBase n b i₁ := by
  rw [vaBase_step hin, if_pos hb]
  have h1 := rewardGH_ge_42 (n := n) hn hi₁
  have h2 := vaBase_anti (b := b) hn (by omega : i₁ + 1 ≤ i₂)
  linarith

lemma vaBase_split_at_false {n b i m : ℕ} (him : i ≤ m) (hmn : m ≤ n)
    (hbit : b.testBit (m - 1) = false) :
    vaBase n b i =
      (∑ j ∈ Finset.Ico i m, if b.testBit (j - 1) then rewardG n j + rewardH n j else 0) +
        vaBase n b (m + 1) := by
  unfold vaBase
  rw [← Finset.sum_Ico_consecutive _ him (by omega : m ≤ n + 1)]
  congr 1
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m < n + 1), if_neg]
  · ring
  · simp [hbit]

lemma odd_gap_ge_41 {n b m : ℕ} (hn : 3 ≤ n) (hm2 : 2 ≤ m) (hmn : m ≤ n)
    (hbit : b.testBit (m - 1) = false) :
    vaBase n b 1 + 41 ≤ rewardG n m + rewardH n m + vaBase n b (m + 1) := by
  rw [vaBase_split_at_false (by omega : 1 ≤ m) hmn hbit]
  have hsum : (∑ j ∈ Finset.Ico 1 m, if b.testBit (j - 1) then rewardG n j + rewardH n j else 0) ≤
      ∑ j ∈ Finset.Ico 1 m, (rewardG n j + rewardH n j) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · linarith
    · exact rewardGH_nonneg hn
  have hico := sum_rewardGH_Ico_le hn (m - 1) 1 (le_refl 1)
  rw [show 1 + (m - 1) = m by omega, show 2 * 1 - 2 = 0 by omega, pow_zero] at hico
  have htop : 42 * (scale n) ^ (2 * (m - 1)) ≤ rewardG n m + rewardH n m := by
    rw [rewardGH_eq (by omega : 1 ≤ m)]
    have hpow : (scale n) ^ (2 * m - 1) = scale n * (scale n) ^ (2 * (m - 1)) := by
      rw [← pow_succ', show 2 * (m - 1) + 1 = 2 * m - 1 by omega]
    rw [hpow]
    have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
    have h42 : (42 : ℚ) ≤ (scale n - 1) * scale n := by nlinarith
    have hp : (0 : ℚ) ≤ (scale n) ^ (2 * (m - 1)) := by have := scale_pos n; positivity
    calc 42 * (scale n) ^ (2 * (m - 1))
      _ ≤ (scale n - 1) * scale n * (scale n) ^ (2 * (m - 1)) :=
        mul_le_mul_of_nonneg_right h42 hp
      _ = (scale n - 1) * (scale n * (scale n) ^ (2 * (m - 1))) := by ring
  have hp1 : (1 : ℚ) ≤ (scale n) ^ (2 * (m - 1)) :=
    one_le_pow₀ (by have := scale_ge_seven hn; linarith)
  linarith

def Gm (n b m : ℕ) : ℚ :=
  rewardG n m + rewardH n m + vaBase n b (m + 1)

lemma HVal_gt_Gm {n b m i : ℕ} (hn : 3 ≤ n) (hm1 : 1 ≤ m) (hmi : m ≤ i) (hin : i ≤ n) :
    Gm n b m + 7 ≤ rewardH n i + vaBase n b (i + 1) := by
  unfold Gm
  rcases eq_or_lt_of_le hmi with rfl | hlt
  · rw [rewardG_eq hm1]
    have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
    have hp : (scale n) ^ 1 ≤ (scale n) ^ (2 * m - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    rw [pow_one] at hp
    linarith
  · have hsplit : vaBase n b (m + 1) ≤
        (∑ j ∈ Finset.Ico (m + 1) (i + 1), (rewardG n j + rewardH n j)) + vaBase n b (i + 1) := by
      unfold vaBase
      rw [← Finset.sum_Ico_consecutive _ (by omega : m + 1 ≤ i + 1) (by omega : i + 1 ≤ n + 1)]
      gcongr with j _
      split_ifs
      · linarith
      · exact rewardGH_nonneg hn
    have hcons : (rewardG n m + rewardH n m) +
        (∑ j ∈ Finset.Ico (m + 1) (i + 1), (rewardG n j + rewardH n j)) =
        ∑ j ∈ Finset.Ico m (i + 1), (rewardG n j + rewardH n j) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m < i + 1)]
    have hlast : (∑ j ∈ Finset.Ico m (i + 1), (rewardG n j + rewardH n j)) =
        (∑ j ∈ Finset.Ico m i, (rewardG n j + rewardH n j)) + (rewardG n i + rewardH n i) :=
      Finset.sum_Ico_succ_top (by omega : m ≤ i) (fun j => rewardG n j + rewardH n j)
    rw [← hcons] at hlast
    have hico2 := sum_rewardGH_Ico_le hn (i - m) m hm1
    rw [show m + (i - m) - 1 = i - 1 by omega, show m + (i - m) = i by omega] at hico2
    have hgi : rewardG n i + rewardH n i = (scale n) ^ (2 * i) - (scale n) ^ (2 * i - 1) := by
      rw [rewardG_eq (by omega : 1 ≤ i), rewardH_eq]; ring
    have hpow : 7 * (scale n) ^ (2 * (i - 1)) ≤ (scale n) ^ (2 * i - 1) := by
      have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
      have hp0 : (0 : ℚ) ≤ (scale n) ^ (2 * (i - 1)) := by have := scale_pos n; positivity
      have heq : 2 * i - 1 = 2 * (i - 1) + 1 := by omega
      rw [heq, pow_succ']
      exact mul_le_mul_of_nonneg_right hs hp0
    have hp1 : (7 : ℚ) ≤ (scale n) ^ (2 * (i - 1)) := by
      have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
      have h1 : (scale n) ^ 1 ≤ (scale n) ^ (2 * (i - 1)) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      rw [pow_one] at h1
      linarith
    have hp2 : (0 : ℚ) ≤ (scale n) ^ (2 * m - 2) := by have := scale_pos n; positivity
    have hrh : rewardH n i = (scale n) ^ (2 * i) := rewardH_eq n i
    linarith

lemma HVal_lt_Gm_of_lt {n b m i : ℕ} (hn : 3 ≤ n) (hi1 : 1 ≤ i) (hlt : i < m) (hmn : m ≤ n)
    (hbit : b.testBit (m - 1) = false) :
    rewardH n i + vaBase n b (i + 1) + 41 ≤ Gm n b m := by
  unfold Gm
  rw [vaBase_split_at_false (by omega : i + 1 ≤ m) hmn hbit]
  have hsum : (∑ j ∈ Finset.Ico (i + 1) m, if b.testBit (j - 1) then rewardG n j + rewardH n j else 0) ≤
      ∑ j ∈ Finset.Ico (i + 1) m, (rewardG n j + rewardH n j) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · linarith
    · exact rewardGH_nonneg hn
  have hico := sum_rewardGH_Ico_le hn (m - (i + 1)) (i + 1) (by omega)
  rw [show (i + 1) + (m - (i + 1)) = m by omega,
    show 2 * (i + 1) - 2 = 2 * i by omega] at hico
  have hrh : rewardH n i = (scale n) ^ (2 * i) := rewardH_eq n i
  have htop : 42 * (scale n) ^ (2 * (m - 1)) ≤ rewardG n m + rewardH n m := by
    rw [rewardGH_eq (by omega : 1 ≤ m)]
    have hpow : (scale n) ^ (2 * m - 1) = scale n * (scale n) ^ (2 * (m - 1)) := by
      rw [← pow_succ', show 2 * (m - 1) + 1 = 2 * m - 1 by omega]
    rw [hpow]
    have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
    have h42 : (42 : ℚ) ≤ (scale n - 1) * scale n := by nlinarith
    have hp : (0 : ℚ) ≤ (scale n) ^ (2 * (m - 1)) := by have := scale_pos n; positivity
    calc 42 * (scale n) ^ (2 * (m - 1))
      _ ≤ (scale n - 1) * scale n * (scale n) ^ (2 * (m - 1)) :=
        mul_le_mul_of_nonneg_right h42 hp
      _ = (scale n - 1) * (scale n * (scale n) ^ (2 * (m - 1))) := by ring
  have hp1 : (1 : ℚ) ≤ (scale n) ^ (2 * (m - 1)) :=
    one_le_pow₀ (by have := scale_ge_seven hn; linarith)
  linarith

lemma eps_mul_le_quarter {n : ℕ} (hn : 3 ≤ n) {X : ℚ}
    (hX : |X| ≤ 2 * (scale n) ^ (2 * n)) :
    |epsilon n * X| ≤ 1 / 4 := by
  rw [abs_mul, abs_of_pos (epsilon_pos n)]
  unfold epsilon
  have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
  have hpos : (0 : ℚ) < (scale n) ^ (2 * n) := by positivity
  have hpow : (scale n) ^ (2 * n + 2) = (scale n) ^ 2 * (scale n) ^ (2 * n) := by ring
  rw [hpow, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have hs2 : (8 : ℚ) ≤ (scale n) ^ 2 := by nlinarith
  nlinarith

lemma two_eps_div_mul_lt_one {n : ℕ} (hn : 3 ≤ n) {X D : ℚ}
    (hD : (1 + epsilon n) * D = 2 * epsilon n * X)
    (hX : |X| ≤ 2 * (scale n) ^ (2 * n)) :
    |D| < 1 := by
  have heps : 0 < epsilon n := epsilon_pos n
  have h1 : 1 < 1 + epsilon n := by linarith
  have habs := congrArg abs hD
  rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 + epsilon n),
    abs_of_pos (by linarith : 0 < 2 * epsilon n)] at habs
  have hq := eps_mul_le_quarter hn hX
  rw [abs_mul, abs_of_pos heps] at hq
  have h2 : (1 + epsilon n) * |D| ≤ 1 / 2 := by linarith
  have h3 : 1 * |D| ≤ (1 + epsilon n) * |D| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg D)
  linarith

lemma sign_of_one_add_eps_eq {n : ℕ} {D X : ℚ}
    (hD : (1 + epsilon n) * D = 2 * epsilon n * X) :
    (0 < D ↔ 0 < X) ∧ (D < 0 ↔ X < 0) := by
  have heps : 0 < epsilon n := epsilon_pos n
  have h1 : 0 < 1 + epsilon n := by linarith
  have h2 : 0 < 2 * epsilon n := by linarith
  constructor
  · constructor
    · intro h
      have : 0 < 2 * epsilon n * X := by rw [← hD]; exact mul_pos h1 h
      exact (mul_pos_iff_of_pos_left h2).mp this
    · intro h
      have : 0 < (1 + epsilon n) * D := by rw [hD]; exact mul_pos h2 h
      exact (mul_pos_iff_of_pos_left h1).mp this
  · constructor
    · intro h
      have : 2 * epsilon n * X < 0 := by rw [← hD]; exact mul_neg_of_pos_of_neg h1 h
      nlinarith
    · intro h
      have : (1 + epsilon n) * D < 0 := by rw [hD]; exact mul_neg_of_pos_of_neg h2 h
      nlinarith

/-! ### Part 4: `MdpPath`, `StateAt`, Step Lemmas, and Binary Counter Policies -/

noncomputable def mdpStrictNonImproving (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    (r : Fin (rows n)) : Prop :=
  actionReward n hn r (!σ r) +
    ∑ q : Fin (rows n), transition n hn r (!σ r) q * policyValue n hn σ q <
    policyValue n hn σ r

lemma not_mdpImproving_of_strict {n : ℕ} {hn : 3 ≤ n} {σ : Policy n} {r : Fin (rows n)}
    (h : mdpStrictNonImproving n hn σ r) : ¬ mdpImproving n hn σ r :=
  not_lt.mpr (le_of_lt h)

lemma mdpStrictNonImproving_policyOf_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {k : Kind} {i : ℕ} (h : ValidRow n (k, i)) :
    mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (k, i) h) ↔
      qFormula n hn (policyValue n hn (policyOf n f)) k i (!f k i) <
        qFormula n hn (policyValue n hn (policyOf n f)) k i (f k i) := by
  unfold mdpStrictNonImproving
  rw [policyValue_eq_qFormula hn (policyOf n f) (mkRow n hn (k, i) h),
    qVal_eq_qFormula hn (policyValue n hn (policyOf n f)) (mkRow n hn (k, i) h)
      (!(policyOf n f) (mkRow n hn (k, i) h)),
    rowName_mkRow, policyOf_mkRow]

noncomputable def mdpStrictStep (n : ℕ) (hn : 3 ≤ n) (s s' : MDPState n) : Prop :=
  ∃ r, mdpImproving n hn s.policy r ∧
    (∀ q, q ≠ r →
      cyclicDistance (order n) s.last (actionColumn n hn q (!s.policy q)) ≤
        cyclicDistance (order n) s.last (actionColumn n hn r (!s.policy r)) →
      mdpStrictNonImproving n hn s.policy q) ∧
    s'.policy = Function.update s.policy r (!s.policy r) ∧
    s'.last = actionColumn n hn r (!s.policy r)

lemma mdpStep_of_strictStep {n : ℕ} {hn : 3 ≤ n} {s s' : MDPState n}
    (h : mdpStrictStep n hn s s') : mdpStep n hn s s' := by
  rcases h with ⟨r, himp, hno, hpol, hlast⟩
  refine ⟨r, himp, ?_, hpol, hlast⟩
  intro q hq
  by_cases hqr : q = r
  · subst hqr; exact le_refl _
  · by_contra hlt
    exact not_mdpImproving_of_strict (hno q hqr (by omega)) hq

inductive MdpPath (n : ℕ) (hn : 3 ≤ n) : ℕ → MDPState n → MDPState n → Prop
  | refl (s : MDPState n) : MdpPath n hn 0 s s
  | step {t : ℕ} {s₁ s₂ s₃ : MDPState n} :
      mdpStrictStep n hn s₁ s₂ → MdpPath n hn t s₂ s₃ → MdpPath n hn (t + 1) s₁ s₃

lemma MdpPath.single {n : ℕ} {hn : 3 ≤ n} {s₁ s₂ : MDPState n}
    (h : mdpStrictStep n hn s₁ s₂) : MdpPath n hn 1 s₁ s₂ :=
  MdpPath.step h (MdpPath.refl s₂)

lemma MdpPath.trans {n : ℕ} {hn : 3 ≤ n} :
    ∀ {t₁ t₂ : ℕ} {s₁ s₂ s₃ : MDPState n},
      MdpPath n hn t₁ s₁ s₂ → MdpPath n hn t₂ s₂ s₃ → MdpPath n hn (t₁ + t₂) s₁ s₃
  | 0, _, _, _, _, .refl _, h₂ => by simpa using h₂
  | t₁ + 1, t₂, _, _, _, .step h₁₂ hp, h₂ => by
    rw [show t₁ + 1 + t₂ = (t₁ + t₂) + 1 by omega]
    exact .step h₁₂ (MdpPath.trans hp h₂)

lemma mdpStrictRun_of_mdpPath {n : ℕ} {hn : 3 ≤ n} :
    ∀ {T : ℕ} {s₀ sT : MDPState n},
      MdpPath n hn T s₀ sT →
      (∀ r : Fin (rows n), mdpStrictNonImproving n hn sT.policy r) →
      ∃ s : ℕ → MDPState n, s 0 = s₀ ∧
        (∀ t < T, mdpStrictStep n hn (s t) (s (t + 1))) ∧
        ∀ r : Fin (rows n), mdpStrictNonImproving n hn (s T).policy r
  | 0, s₀, _, .refl _, hterm =>
    ⟨fun _ => s₀, rfl, fun _ ht => by omega, hterm⟩
  | T + 1, s₀, sT, .step (s₂ := s₁) h₀₁ hp, hterm => by
    rcases mdpStrictRun_of_mdpPath hp hterm with ⟨s', hs'0, hs'step, hs'term⟩
    refine ⟨fun t => match t with | 0 => s₀ | t + 1 => s' t, rfl, ?_, hs'term⟩
    intro t ht
    cases t with
    | zero => simpa [hs'0] using h₀₁
    | succ t => exact hs'step t (by omega)

lemma mdpRun_of_mdpPath {n : ℕ} {hn : 3 ≤ n} {T : ℕ} {s₀ sT : MDPState n}
    (hp : MdpPath n hn T s₀ sT)
    (hterm : ∀ r : Fin (rows n), mdpStrictNonImproving n hn sT.policy r) :
    ∃ s : ℕ → MDPState n, s 0 = s₀ ∧
      (∀ t < T, mdpStep n hn (s t) (s (t + 1))) ∧
      ∀ r : Fin (rows n), ¬ mdpImproving n hn (s T).policy r := by
  rcases mdpStrictRun_of_mdpPath hp hterm with ⟨s, hs0, hstep, hsterm⟩
  exact ⟨s, hs0, fun t ht => mdpStep_of_strictStep (hstep t ht),
    fun r => not_mdpImproving_of_strict (hsterm r)⟩

@[simp]
lemma actionColumn_mkRow_val {n : ℕ} (hn : 3 ≤ n) {k : Kind} {i : ℕ}
    (hv : ValidRow n (k, i)) (b : Bool) :
    (actionColumn n hn (mkRow n hn (k, i) hv) b).val = columnRank n ⟨k, i, b⟩ := by
  rw [actionColumn_val hn, rowName_mkRow]

def StateAt (n : ℕ) (f : Kind → ℕ → Bool) (m : ℕ) (s : MDPState n) : Prop :=
  s.policy = policyOf n f ∧ s.last.val = m ∧
  ∃ k₁ i₁, ValidRow n (k₁, i₁) ∧ m = columnRank n ⟨k₁, i₁, f k₁ i₁⟩

lemma opp_columnRank_ne_of_stateAt {n : ℕ} (hn : 3 ≤ n)
    {f : Kind → ℕ → Bool} {m : ℕ} {s : MDPState n}
    (hs : StateAt n f m s) {k : Kind} {i : ℕ} (hv : ValidRow n (k, i)) :
    columnRank n ⟨k, i, !f k i⟩ ≠ m := by
  rcases hs with ⟨_, _, k₁, i₁, hv₁, rfl⟩
  intro heq
  have h1 : actionColumn n hn (mkRow n hn (k, i) hv) (!f k i) =
      actionColumn n hn (mkRow n hn (k₁, i₁) hv₁) (f k₁ i₁) := by
    apply Fin.ext
    rw [actionColumn_mkRow_val hn hv, actionColumn_mkRow_val hn hv₁, heq]
  have h2 := congrArg (columnName n) h1
  rw [columnName_actionColumn n hn, columnName_actionColumn n hn,
    rowName_mkRow, rowName_mkRow] at h2
  injection h2 with hk hi hb
  subst hk; subst hi
  revert hb
  cases f k i <;> decide

lemma cyclicDistance_order_eq {n : ℕ} (last j : Fin (cols n)) :
    cyclicDistance (order n) last j =
      if last.val ≤ j.val then j.val - last.val else j.val + cols n - last.val := by
  unfold cyclicDistance order
  simp only [Equiv.refl_apply]
  have hj := j.isLt
  have hl := last.isLt
  split_ifs with h
  · rw [show j.val + cols n - last.val = (j.val - last.val) + cols n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

lemma step_stateAt_of_le {n : ℕ} (hn : 3 ≤ n)
    {f₁ f₂ : Kind → ℕ → Bool} {m₁ : ℕ} {s₁ : MDPState n}
    (hs₁ : StateAt n f₁ m₁ s₁)
    (k₀ : Kind) (i₀ : ℕ) (h₀ : ValidRow n (k₀, i₀))
    (hm : m₁ ≤ columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩)
    (himp : mdpImproving n hn (policyOf n f₁) (mkRow n hn (k₀, i₀) h₀))
    (hno : ∀ k i (hv : ValidRow n (k, i)),
      m₁ < columnRank n ⟨k, i, !f₁ k i⟩ →
      columnRank n ⟨k, i, !f₁ k i⟩ < columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ →
      mdpStrictNonImproving n hn (policyOf n f₁) (mkRow n hn (k, i) hv))
    (hup : ∀ k i, ValidRow n (k, i) →
      (if k = k₀ ∧ i = i₀ then !f₁ k₀ i₀ else f₁ k i) = f₂ k i) :
    ∃ s₂ : MDPState n, MdpPath n hn 1 s₁ s₂ ∧
      StateAt n f₂ (columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩) s₂ := by
  let r₀ := mkRow n hn (k₀, i₀) h₀
  let j₀ := actionColumn n hn r₀ (!s₁.policy r₀)
  refine ⟨⟨policyOf n f₂, j₀⟩, MdpPath.single ?_, ?_⟩
  · refine ⟨r₀, ?_, ?_, ?_, rfl⟩
    · rw [hs₁.1]; exact himp
    · intro q hqr hdist
      have hv : ValidRow n ((rowName n q).1, (rowName n q).2) := rowName_valid hn q
      have hq_eq : q = mkRow n hn ((rowName n q).1, (rowName n q).2) hv :=
        (mkRow_rowName hn q).symm
      have hne_last := opp_columnRank_ne_of_stateAt hn hs₁ hv
      have hj₀ : (actionColumn n hn r₀ (!s₁.policy r₀)).val = columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ := by
        rw [hs₁.1, policyOf_mkRow, actionColumn_mkRow_val hn h₀]
      have hjq : (actionColumn n hn q (!s₁.policy q)).val =
          columnRank n ⟨(rowName n q).1, (rowName n q).2, !f₁ (rowName n q).1 (rowName n q).2⟩ := by
        conv_lhs => rw [hq_eq]
        rw [hs₁.1, policyOf_mkRow, actionColumn_mkRow_val hn hv]
      have hne_j₀ : (actionColumn n hn q (!s₁.policy q)).val ≠
          (actionColumn n hn r₀ (!s₁.policy r₀)).val := by
        intro heq
        have hcol := Fin.ext heq
        exact hqr (actionColumn_inj hn hcol).1
      rw [cyclicDistance_order_eq, cyclicDistance_order_eq, hs₁.2.1, hj₀, hjq] at hdist
      rw [hj₀, hjq] at hne_j₀
      have hlt₀ : columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ < cols n :=
        columnRank_lt_cols hn (k₀, i₀) h₀ _
      have hin : m₁ < columnRank n ⟨(rowName n q).1, (rowName n q).2, !f₁ (rowName n q).1 (rowName n q).2⟩ ∧
          columnRank n ⟨(rowName n q).1, (rowName n q).2, !f₁ (rowName n q).1 (rowName n q).2⟩ <
            columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ := by
        split_ifs at hdist <;> omega
      rw [hs₁.1, hq_eq]
      exact hno _ _ hv hin.1 hin.2
    · rw [hs₁.1]
      exact (update_policyOf_eq hn k₀ i₀ h₀ hup).symm
  · refine ⟨rfl, ?_, k₀, i₀, h₀, ?_⟩
    · dsimp [j₀, r₀]
      rw [hs₁.1, policyOf_mkRow, actionColumn_mkRow_val hn h₀]
    · have h1 := hup k₀ i₀ h₀
      rw [if_pos ⟨rfl, rfl⟩] at h1
      rw [h1]

lemma step_stateAt_of_wrap {n : ℕ} (hn : 3 ≤ n)
    {f₁ f₂ : Kind → ℕ → Bool} {m₁ : ℕ} {s₁ : MDPState n}
    (hs₁ : StateAt n f₁ m₁ s₁)
    (k₀ : Kind) (i₀ : ℕ) (h₀ : ValidRow n (k₀, i₀))
    (hm : columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ < m₁)
    (himp : mdpImproving n hn (policyOf n f₁) (mkRow n hn (k₀, i₀) h₀))
    (hno : ∀ k i (hv : ValidRow n (k, i)),
      (m₁ < columnRank n ⟨k, i, !f₁ k i⟩ ∨
        columnRank n ⟨k, i, !f₁ k i⟩ < columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩) →
      mdpStrictNonImproving n hn (policyOf n f₁) (mkRow n hn (k, i) hv))
    (hup : ∀ k i, ValidRow n (k, i) →
      (if k = k₀ ∧ i = i₀ then !f₁ k₀ i₀ else f₁ k i) = f₂ k i) :
    ∃ s₂ : MDPState n, MdpPath n hn 1 s₁ s₂ ∧
      StateAt n f₂ (columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩) s₂ := by
  let r₀ := mkRow n hn (k₀, i₀) h₀
  let j₀ := actionColumn n hn r₀ (!s₁.policy r₀)
  refine ⟨⟨policyOf n f₂, j₀⟩, MdpPath.single ?_, ?_⟩
  · refine ⟨r₀, ?_, ?_, ?_, rfl⟩
    · rw [hs₁.1]; exact himp
    · intro q hqr hdist
      have hv : ValidRow n ((rowName n q).1, (rowName n q).2) := rowName_valid hn q
      have hq_eq : q = mkRow n hn ((rowName n q).1, (rowName n q).2) hv :=
        (mkRow_rowName hn q).symm
      have hne_last := opp_columnRank_ne_of_stateAt hn hs₁ hv
      have hj₀ : (actionColumn n hn r₀ (!s₁.policy r₀)).val = columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ := by
        rw [hs₁.1, policyOf_mkRow, actionColumn_mkRow_val hn h₀]
      have hjq : (actionColumn n hn q (!s₁.policy q)).val =
          columnRank n ⟨(rowName n q).1, (rowName n q).2, !f₁ (rowName n q).1 (rowName n q).2⟩ := by
        conv_lhs => rw [hq_eq]
        rw [hs₁.1, policyOf_mkRow, actionColumn_mkRow_val hn hv]
      have hne_j₀ : (actionColumn n hn q (!s₁.policy q)).val ≠
          (actionColumn n hn r₀ (!s₁.policy r₀)).val := by
        intro heq
        have hcol := Fin.ext heq
        exact hqr (actionColumn_inj hn hcol).1
      rw [cyclicDistance_order_eq, cyclicDistance_order_eq, hs₁.2.1, hj₀, hjq] at hdist
      rw [hj₀, hjq] at hne_j₀
      have hm₁ : m₁ < cols n := by rw [← hs₁.2.1]; exact s₁.last.isLt
      have hlt₀ : columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ < cols n :=
        columnRank_lt_cols hn (k₀, i₀) h₀ _
      have hlt_q : columnRank n ⟨(rowName n q).1, (rowName n q).2,
          !f₁ (rowName n q).1 (rowName n q).2⟩ < cols n :=
        columnRank_lt_cols hn _ hv _
      have hin : m₁ < columnRank n ⟨(rowName n q).1, (rowName n q).2, !f₁ (rowName n q).1 (rowName n q).2⟩ ∨
          columnRank n ⟨(rowName n q).1, (rowName n q).2, !f₁ (rowName n q).1 (rowName n q).2⟩ <
            columnRank n ⟨k₀, i₀, !f₁ k₀ i₀⟩ := by
        split_ifs at hdist <;> omega
      rw [hs₁.1, hq_eq]
      exact hno _ _ hv hin
    · rw [hs₁.1]
      exact (update_policyOf_eq hn k₀ i₀ h₀ hup).symm
  · refine ⟨rfl, ?_, k₀, i₀, h₀, ?_⟩
    · dsimp [j₀, r₀]
      rw [hs₁.1, policyOf_mkRow, actionColumn_mkRow_val hn h₀]
    · have h1 := hup k₀ i₀ h₀
      rw [if_pos ⟨rfl, rfl⟩] at h1
      rw [h1]

def findLevel (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | i, 0 => i
  | i, k + 1 => if p i then i else findLevel p (i + 1) k

lemma findLevel_ge (p : ℕ → Bool) : ∀ i k, i ≤ findLevel p i k
  | i, 0 => le_refl i
  | i, k + 1 => by
    unfold findLevel
    split_ifs
    · exact le_refl i
    · have := findLevel_ge p (i + 1) k; omega

lemma findLevel_lt_false (p : ℕ → Bool) :
    ∀ i k j, i ≤ j → j < findLevel p i k → p j = false
  | i, 0, j, hij, hlt => by unfold findLevel at hlt; omega
  | i, k + 1, j, hij, hlt => by
    unfold findLevel at hlt
    split_ifs at hlt with hp
    · omega
    · rcases eq_or_lt_of_le hij with rfl | hgt
      · exact Bool.eq_false_iff.mpr hp
      · exact findLevel_lt_false p (i + 1) k j (by omega) hlt

lemma findLevel_spec (p : ℕ → Bool) :
    ∀ i k j, i ≤ j → j < i + k → p j = true →
      findLevel p i k < i + k ∧ p (findLevel p i k) = true
  | i, 0, j, hij, hjk, _ => by omega
  | i, k + 1, j, hij, hjk, hpj => by
    unfold findLevel
    split_ifs with hp
    · exact ⟨by omega, hp⟩
    · have hne : j ≠ i := by rintro rfl; exact hp hpj
      rcases findLevel_spec p (i + 1) k j (by omega) (by omega) hpj with ⟨h1, h2⟩
      exact ⟨by omega, h2⟩

lemma findLevel_eq_of_min (p : ℕ → Bool) {i k m : ℕ}
    (him : i ≤ m) (hmk : m < i + k) (hpm : p m = true)
    (hmin : ∀ j, i ≤ j → j < m → p j = false) :
    findLevel p i k = m := by
  rcases findLevel_spec p i k m him hmk hpm with ⟨_, hpf⟩
  have h1 : ¬ findLevel p i k < m := by
    intro hlt
    have := hmin (findLevel p i k) (findLevel_ge p i k) hlt
    rw [hpf] at this; contradiction
  have h2 : ¬ m < findLevel p i k := by
    intro hlt
    have := findLevel_lt_false p i k m him hlt
    rw [hpm] at this; contradiction
  omega

def mu (n b : ℕ) : ℕ :=
  findLevel (fun i => !b.testBit (i - 1)) 2 (n - 1)

def nu (n b : ℕ) : ℕ :=
  findLevel (fun i => b.testBit (i - 1)) 2 (n - 1)

lemma testBit_succ_Carry :
    ∀ i b : ℕ,
      (∀ j < i, b.testBit j = true) →
      (b + 1).testBit i = !b.testBit i
  | 0, b, _ => by
    simp only [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h] <;> omega
  | i + 1, b, h => by
    have h0 : b % 2 = 1 := by
      have := h 0 (by omega)
      rw [Nat.testBit_zero] at this
      rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;> simp_all
    have hdiv : (b + 1) / 2 = b / 2 + 1 := by omega
    rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
    apply testBit_succ_Carry i (b / 2)
    intro j hj
    rw [← Nat.testBit_succ]
    exact h (j + 1) (by omega)

lemma testBit_succ_NoCarry :
    ∀ i b m : ℕ, m < i → b.testBit m = false →
      (b + 1).testBit i = b.testBit i
  | 0, _, _, hm, _ => by omega
  | i + 1, b, 0, _, hm0 => by
    rw [Nat.testBit_zero] at hm0
    have h0 : b % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp_all
    have hdiv : (b + 1) / 2 = b / 2 := by omega
    rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
  | i + 1, b, m + 1, hlt, hm => by
    rw [Nat.testBit_succ, Nat.testBit_succ]
    rcases Nat.mod_two_eq_zero_or_one b with h0 | h1
    · have hdiv : (b + 1) / 2 = b / 2 := by omega
      rw [hdiv]
    · have hdiv : (b + 1) / 2 = b / 2 + 1 := by omega
      rw [hdiv]
      apply testBit_succ_NoCarry i (b / 2) m (by omega)
      rw [← Nat.testBit_succ]
      exact hm

lemma exists_testBit_false_of_lt {n b : ℕ} (hb : b < 2 ^ n - 1) :
    ∃ j < n, b.testBit j = false := by
  by_contra hall
  have h1 : ∀ j < n, b.testBit j = true := by
    intro j hj
    cases h : b.testBit j
    · exfalso; exact hall ⟨j, hj, h⟩
    · rfl
  have hcarry := testBit_succ_Carry n b h1
  have hbn : b.testBit n = false := Nat.testBit_lt_two_pow (by omega)
  have hbn1 : (b + 1).testBit n = false := Nat.testBit_lt_two_pow (by omega)
  rw [hbn, hbn1] at hcarry
  contradiction

lemma exists_testBit_true_of_pos :
    ∀ n b : ℕ, 0 < b → b < 2 ^ n → ∃ j < n, b.testBit j = true
  | 0, b, hpos, hlt => by simp at hlt; omega
  | n + 1, b, hpos, hlt => by
    rcases Nat.mod_two_eq_zero_or_one b with h0 | h1
    · have hpos' : 0 < b / 2 := by omega
      have hlt' : b / 2 < 2 ^ n := by
        rw [Nat.pow_succ] at hlt; omega
      rcases exists_testBit_true_of_pos n (b / 2) hpos' hlt' with ⟨j, hj, hbit⟩
      refine ⟨j + 1, by omega, ?_⟩
      rw [Nat.testBit_succ]
      exact hbit
    · refine ⟨0, by omega, ?_⟩
      rw [Nat.testBit_zero]
      exact decide_eq_true h1

lemma mu_spec {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1) :
    2 ≤ mu n b ∧ mu n b ≤ n ∧ b.testBit (mu n b - 1) = false ∧
    ∀ i, 1 ≤ i → i < mu n b → b.testBit (i - 1) = true := by
  have hb0 : b.testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  rcases exists_testBit_false_of_lt hb with ⟨j, hjn, hbj⟩
  have hj0 : j ≠ 0 := by rintro rfl; rw [hb0] at hbj; contradiction
  have hspec := findLevel_spec (fun i => !b.testBit (i - 1)) 2 (n - 1) (j + 1)
    (by omega) (by omega) (by simp [hbj])
  refine ⟨findLevel_ge _ 2 (n - 1), by unfold mu; omega, ?_, ?_⟩
  · have h2 := hspec.2
    change (!b.testBit (mu n b - 1)) = true at h2
    simpa using h2
  · intro i hi1 hilt
    rcases eq_or_lt_of_le hi1 with rfl | hi2
    · exact hb0
    · have hlt := findLevel_lt_false (fun k => !b.testBit (k - 1)) 2 (n - 1) i hi2 hilt
      simpa using hlt

lemma nu_spec {n b : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hpos : 0 < b) (hb : b < 2 ^ n) :
    2 ≤ nu n b ∧ nu n b ≤ n ∧ b.testBit (nu n b - 1) = true ∧
    ∀ i, 1 ≤ i → i < nu n b → b.testBit (i - 1) = false := by
  have hb0 : b.testBit 0 = false := by
    rw [Nat.testBit_zero]; exact decide_eq_false (by omega)
  rcases exists_testBit_true_of_pos n b hpos hb with ⟨j, hjn, hbj⟩
  have hj0 : j ≠ 0 := by rintro rfl; rw [hb0] at hbj; contradiction
  have hspec := findLevel_spec (fun i => b.testBit (i - 1)) 2 (n - 1) (j + 1)
    (by omega) (by omega) (by simpa using hbj)
  refine ⟨findLevel_ge _ 2 (n - 1), by unfold nu; omega, hspec.2, ?_⟩
  intro i hi1 hilt
  rcases eq_or_lt_of_le hi1 with rfl | hi2
  · exact hb0
  · exact findLevel_lt_false (fun k => b.testBit (k - 1)) 2 (n - 1) i hi2 hilt

lemma odd_succ_bits {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1) :
    (∀ i, 1 ≤ i → i < mu n b → (b + 1).testBit (i - 1) = false) ∧
    (b + 1).testBit (mu n b - 1) = true ∧
    (∀ i, mu n b < i → (b + 1).testBit (i - 1) = b.testBit (i - 1)) ∧
    nu n (b + 1) = mu n b := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, hmumin⟩
  have hlt : ∀ i, 1 ≤ i → i < mu n b → (b + 1).testBit (i - 1) = false := by
    intro i hi1 hilt
    rw [testBit_succ_Carry (i - 1) b]
    · rw [hmumin i hi1 hilt]; rfl
    · intro j hj
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ j + 1)] using hmumin (j + 1) (by omega) (by omega)
  have heq : (b + 1).testBit (mu n b - 1) = true := by
    rw [testBit_succ_Carry (mu n b - 1) b]
    · rw [hmubit]; rfl
    · intro j hj
      simpa using hmumin (j + 1) (by omega) (by omega)
  have hgt : ∀ i, mu n b < i → (b + 1).testBit (i - 1) = b.testBit (i - 1) := by
    intro i higt
    exact testBit_succ_NoCarry (i - 1) b (mu n b - 1) (by omega) hmubit
  refine ⟨hlt, heq, hgt, ?_⟩
  unfold nu
  apply findLevel_eq_of_min _ hmu2 (by omega) heq
  intro j hj2 hjlt
  exact hlt j (by omega) hjlt

lemma even_succ_bits {b : ℕ} (heven : b % 2 = 0) :
    (b + 1).testBit 0 = true ∧
    ∀ i, 2 ≤ i → (b + 1).testBit (i - 1) = b.testBit (i - 1) := by
  have hb0 : b.testBit 0 = false := by
    rw [Nat.testBit_zero]; exact decide_eq_false (by omega)
  refine ⟨?_, ?_⟩
  · rw [testBit_succ_Carry 0 b (by intro j hj; omega), hb0]; rfl
  · intro i hi2
    exact testBit_succ_NoCarry (i - 1) b 0 (by omega) hb0

lemma vaBase_even_succ {n b i : ℕ} (heven : b % 2 = 0) (hi : 2 ≤ i) :
    vaBase n (b + 1) i = vaBase n b i := by
  unfold vaBase
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [(even_succ_bits heven).2 j (by omega)]

lemma vaBase_odd_succ_gt {n b i : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hi : mu n b < i) :
    vaBase n (b + 1) i = vaBase n b i := by
  unfold vaBase
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [(odd_succ_bits hn hodd hb).2.2.1 j (by omega)]

lemma vaBase_odd_succ_le {n b i : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hi1 : 1 ≤ i) (hile : i ≤ mu n b) :
    vaBase n (b + 1) i = rewardG n (mu n b) + rewardH n (mu n b) + vaBase n b (mu n b + 1) := by
  rcases mu_spec hn hodd hb with ⟨_, hmun, _, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨hlt, heq, _, _⟩
  have hsplit : vaBase n (b + 1) i =
      (∑ j ∈ Finset.Ico i (mu n b),
        if (b + 1).testBit (j - 1) then rewardG n j + rewardH n j else 0) +
        vaBase n (b + 1) (mu n b) := by
    unfold vaBase
    rw [← Finset.sum_Ico_consecutive _ hile (by omega : mu n b ≤ n + 1)]
  have hzero : (∑ j ∈ Finset.Ico i (mu n b),
      if (b + 1).testBit (j - 1) then rewardG n j + rewardH n j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [hlt j (by omega) hj.2, if_neg (by decide)]
  rw [hsplit, hzero, zero_add, vaBase_step hmun, if_pos heq,
    vaBase_odd_succ_gt hn hodd hb (by omega)]

def counterFun (n b : ℕ) (k : Kind) (i : ℕ) : Bool :=
  match k with
  | .a => b.testBit (i - 1)
  | .b => if b.testBit 0 then false else decide (i = nu n b)
  | .c => if b.testBit 0 then false else decide (i = nu n b)
  | .d => true
  | .e => b.testBit (i - 1)

lemma one_testBit_zero : (1 : ℕ).testBit 0 = true := rfl

lemma one_testBit_of_ge_two {i : ℕ} (hi : 2 ≤ i) : (1 : ℕ).testBit (i - 1) = false := by
  apply Nat.testBit_lt_two_pow
  have : 1 < 2 ^ (i - 1) := Nat.one_lt_two_pow (by omega)
  omega

lemma initialMDPState_stateAt {n : ℕ} (hn : 3 ≤ n) :
    StateAt n (counterFun n 1) 0 (initialMDPState n hn) := by
  refine ⟨?_, rfl, .e, 1, valid_e_one hn, rfl⟩
  ext r
  unfold initialMDPState initialPolicy policyOf
  dsimp only
  have hv := rowName_valid hn r
  rcases hr : rowName n r with ⟨k, i⟩
  rw [hr] at hv
  cases k <;> dsimp [counterFun, initialBit, ValidRow] at hv ⊢
  · exact (one_testBit_of_ge_two hv.1).symm
  · rfl
  · rfl
  · rfl
  · rcases eq_or_lt_of_le hv.1 with rfl | hi2
    · rfl
    · rw [one_testBit_of_ge_two hi2]
      simp [Nat.ne_of_gt hi2]

lemma Gm_one_of_odd {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) :
    Gm n b 1 = vaBase n b 1 := by
  unfold Gm
  have hb0 : b.testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  rw [vaBase_step (by omega : 1 ≤ n), if_pos hb0]

lemma vaBase_eq_Gm_nu_of_even {n b i : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0)
    (hpos : 0 < b) (hb : b < 2 ^ n) (hi1 : 1 ≤ i) (hile : i ≤ nu n b) :
    vaBase n b i = Gm n b (nu n b) := by
  rcases nu_spec hn heven hpos hb with ⟨_, hnun, hnubit, hnumin⟩
  have hsplit : vaBase n b i =
      (∑ j ∈ Finset.Ico i (nu n b),
        if b.testBit (j - 1) then rewardG n j + rewardH n j else 0) +
        vaBase n b (nu n b) := by
    unfold vaBase
    rw [← Finset.sum_Ico_consecutive _ hile (by omega : nu n b ≤ n + 1)]
  have hzero : (∑ j ∈ Finset.Ico i (nu n b),
      if b.testBit (j - 1) then rewardG n j + rewardH n j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [hnumin j (by omega) hj.2, if_neg (by decide)]
  unfold Gm
  rw [hsplit, hzero, zero_add, vaBase_step hnun, if_pos hnubit]

lemma Gm_nu_lt_Gm_one_of_even {n b : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0)
    (hpos : 0 < b) (hb : b < 2 ^ n) :
    Gm n b (nu n b) + 42 ≤ Gm n b 1 := by
  rcases nu_spec hn heven hpos hb with ⟨hnu2, _, _, _⟩
  unfold Gm
  have hva := vaBase_eq_Gm_nu_of_even hn heven hpos hb (by omega : 1 ≤ 2) hnu2
  unfold Gm at hva
  have hgh := rewardGH_ge_42 (n := n) (i := 1) hn (le_refl 1)
  linarith

lemma Gm_one_lt_Gm_mu_of_odd {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1)
    (hb : b < 2 ^ n - 1) :
    Gm n b 1 + 41 ≤ Gm n b (mu n b) := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rw [Gm_one_of_odd hn hodd]
  exact odd_gap_ge_41 hn hmu2 hmun hmubit

lemma Gm_ge_42 {n b m : ℕ} (hn : 3 ≤ n) (hm1 : 1 ≤ m) :
    42 ≤ Gm n b m := by
  unfold Gm
  have h1 := rewardGH_ge_42 hn hm1
  have h2 := vaBase_nonneg (b := b) (i := m + 1) hn
  linarith

lemma Gm_le_scale_pow {n b m : ℕ} (hn : 3 ≤ n) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    Gm n b m ≤ (scale n) ^ (2 * n) := by
  unfold Gm
  have h1 := rewardGH_le_sub_pow hn hm1
  have h2 := vaBase_le_pow (b := b) hn (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ n + 1)
  rw [show 2 * (m + 1) - 2 = 2 * m by omega] at h2
  have hp : (0 : ℚ) ≤ (scale n) ^ (2 * m - 2) := by have := scale_pos n; positivity
  linarith

lemma HVal_base_ge_49 {n b i : ℕ} (hn : 3 ≤ n) (hi1 : 1 ≤ i) :
    49 ≤ rewardH n i + vaBase n b (i + 1) := by
  rw [rewardH_eq]
  have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
  have hp : (scale n) ^ 2 ≤ (scale n) ^ (2 * i) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hs2 : (49 : ℚ) ≤ (scale n) ^ 2 := by nlinarith
  have hva := vaBase_nonneg (b := b) (i := i + 1) hn
  linarith

lemma HVal_base_le_scale_pow {n b i : ℕ} (hn : 3 ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    rewardH n i + vaBase n b (i + 1) ≤ (scale n) ^ (2 * n) := by
  rw [rewardH_eq]
  have h2 := vaBase_le_pow (b := b) hn (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ n + 1)
  rw [show 2 * (i + 1) - 2 = 2 * i by omega] at h2
  linarith

lemma abs_HVal_sub_Gm_le {n b' b m i : ℕ} (hn : 3 ≤ n)
    (hm1 : 1 ≤ m) (hmn : m ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    |(rewardH n i + vaBase n b' (i + 1)) - Gm n b m| ≤ 2 * (scale n) ^ (2 * n) := by
  have hH0 := HVal_base_ge_49 (b := b') hn hi1
  have hH1 := HVal_base_le_scale_pow (b := b') hn hi1 hin
  have hG0 := Gm_ge_42 (b := b) hn hm1
  have hG1 := Gm_le_scale_pow (b := b) hn hm1 hmn
  rw [abs_le]
  constructor <;> linarith

lemma abs_HVal_sub_one_add_Gm_le {n b' b m i : ℕ} (hn : 3 ≤ n)
    (hm1 : 1 ≤ m) (hmn : m ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    |(rewardH n i + vaBase n b' (i + 1)) - (1 + Gm n b m)| ≤ 2 * (scale n) ^ (2 * n) := by
  have hH0 := HVal_base_ge_49 (b := b') hn hi1
  have hH1 := HVal_base_le_scale_pow (b := b') hn hi1 hin
  have hG0 := Gm_ge_42 (b := b) hn hm1
  have hG1 := Gm_le_scale_pow (b := b) hn hm1 hmn
  rw [abs_le]
  constructor <;> linarith

lemma rewardG_le_neg_343 {n i : ℕ} (hn : 3 ≤ n) (hi2 : 2 ≤ i) :
    rewardG n i ≤ -343 := by
  rw [rewardG_eq (by omega : 1 ≤ i)]
  have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
  have hp : (scale n) ^ 3 ≤ (scale n) ^ (2 * i - 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hs2 : (49 : ℚ) ≤ (scale n) ^ 2 := by nlinarith
  have hs3 : (343 : ℚ) ≤ (scale n) ^ 3 := by
    have : (scale n) ^ 3 = scale n * (scale n) ^ 2 := by ring
    nlinarith
  linarith

lemma FRhs_GRhs_of_de_true_false_Gm {n b' b m i : ℕ} (hn : 3 ≤ n)
    (f : Kind → ℕ → Bool) (hi2 : 2 ≤ i) (hin : i ≤ n) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hd : f .d i = true) (he : f .e i = false)
    (hva : valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) = vaBase n b' (i + 1))
    (hcn : valAt n hn (policyValue n hn (policyOf n f)) .c n = Gm n b m) :
    let V := policyValue n hn (policyOf n f)
    |FRhs n hn V i - (1 + Gm n b m)| < 1 ∧
    (1 + Gm n b m < FRhs n hn V i ↔ 1 + Gm n b m < rewardH n i + vaBase n b' (i + 1)) ∧
    (FRhs n hn V i < 1 + Gm n b m ↔ rewardH n i + vaBase n b' (i + 1) < 1 + Gm n b m) ∧
    GRhs n hn V i + 300 < Gm n b m := by
  intro V
  have hH : HVal n hn V i = rewardH n i + vaBase n b' (i + 1) := by
    unfold HVal; rw [hva]
  have hF := FRhs_of_de_true_false hn f hi2 hin hd he
  change (1 + epsilon n) * (FRhs n hn V i - (1 + valAt n hn V .c n)) =
    2 * epsilon n * (HVal n hn V i - (1 + valAt n hn V .c n)) at hF
  rw [hcn, hH] at hF
  have habs := two_eps_div_mul_lt_one hn hF
    (abs_HVal_sub_one_add_Gm_le hn hm1 hmn (by omega) hin)
  have hsign := sign_of_one_add_eps_eq hF
  have h1 : 1 + Gm n b m < FRhs n hn V i ↔ 1 + Gm n b m < rewardH n i + vaBase n b' (i + 1) := by
    rw [← sub_pos (a := FRhs n hn V i), ← sub_pos (a := rewardH n i + vaBase n b' (i + 1))]
    exact hsign.1
  have h2 : FRhs n hn V i < 1 + Gm n b m ↔ rewardH n i + vaBase n b' (i + 1) < 1 + Gm n b m := by
    rw [← sub_lt_zero (a := FRhs n hn V i), ← sub_lt_zero (a := rewardH n i + vaBase n b' (i + 1))]
    exact hsign.2
  have hG : GRhs n hn V i + 300 < Gm n b m := by
    unfold GRhs
    have hrg := rewardG_le_neg_343 hn hi2
    have habs' := (abs_lt.mp habs).2
    linarith
  exact ⟨habs, h1, h2, hG⟩

lemma FRhs_GRhs_of_de_false_true_Gm {n b' b m i : ℕ} (hn : 3 ≤ n)
    (f : Kind → ℕ → Bool) (hi2 : 2 ≤ i) (hin : i ≤ n) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hd : f .d i = false) (he : f .e i = true)
    (hva : valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) = vaBase n b' (i + 1))
    (hbp : BPrev n hn (policyValue n hn (policyOf n f)) i = Gm n b m) :
    let V := policyValue n hn (policyOf n f)
    |FRhs n hn V i - Gm n b m| < 1 ∧
    (Gm n b m < FRhs n hn V i ↔ Gm n b m < rewardH n i + vaBase n b' (i + 1)) ∧
    (FRhs n hn V i < Gm n b m ↔ rewardH n i + vaBase n b' (i + 1) < Gm n b m) ∧
    GRhs n hn V i + 300 < Gm n b m := by
  intro V
  have hH : HVal n hn V i = rewardH n i + vaBase n b' (i + 1) := by
    unfold HVal; rw [hva]
  have hF := FRhs_of_de_false_true hn f hi2 hin hd he
  change (1 + epsilon n) * (FRhs n hn V i - BPrev n hn V i) =
    2 * epsilon n * (HVal n hn V i - BPrev n hn V i) at hF
  rw [hbp, hH] at hF
  have habs := two_eps_div_mul_lt_one hn hF
    (abs_HVal_sub_Gm_le hn hm1 hmn (by omega) hin)
  have hsign := sign_of_one_add_eps_eq hF
  have h1 : Gm n b m < FRhs n hn V i ↔ Gm n b m < rewardH n i + vaBase n b' (i + 1) := by
    rw [← sub_pos (a := FRhs n hn V i), ← sub_pos (a := rewardH n i + vaBase n b' (i + 1))]
    exact hsign.1
  have h2 : FRhs n hn V i < Gm n b m ↔ rewardH n i + vaBase n b' (i + 1) < Gm n b m := by
    rw [← sub_lt_zero (a := FRhs n hn V i), ← sub_lt_zero (a := rewardH n i + vaBase n b' (i + 1))]
    exact hsign.2
  have hG : GRhs n hn V i + 300 < Gm n b m := by
    unfold GRhs
    have hrg := rewardG_le_neg_343 hn hi2
    have habs' := (abs_lt.mp habs).2
    linarith
  exact ⟨habs, h1, h2, hG⟩

lemma FRhs_gt_one_add_cn_of_de_false_false {n i : ℕ} (hn : 3 ≤ n)
    (f : Kind → ℕ → Bool) (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hd : f .d i = false) (he : f .e i = false)
    (hH : 1 + valAt n hn (policyValue n hn (policyOf n f)) .c n <
      HVal n hn (policyValue n hn (policyOf n f)) i)
    (hB : 1 + valAt n hn (policyValue n hn (policyOf n f)) .c n <
      BPrev n hn (policyValue n hn (policyOf n f)) i) :
    1 + valAt n hn (policyValue n hn (policyOf n f)) .c n <
      FRhs n hn (policyValue n hn (policyOf n f)) i := by
  have hF := FRhs_of_de_false_false hn f hi2 hin hd he
  have heps : 0 < epsilon n := epsilon_pos n
  have heps1 : epsilon n < 1 := epsilon_lt_one hn
  have hpos1 : 0 < epsilon n * (HVal n hn (policyValue n hn (policyOf n f)) i -
      (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) :=
    mul_pos heps (by linarith)
  have hpos2 : 0 < ((1 - epsilon n) / 2) * (BPrev n hn (policyValue n hn (policyOf n f)) i -
      (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) :=
    mul_pos (by linarith) (by linarith)
  linarith

lemma FRhs_GRhs_of_de_false_false_same_Gm {n b' b m i : ℕ} (hn : 3 ≤ n)
    (f : Kind → ℕ → Bool) (hi2 : 2 ≤ i) (hin : i ≤ n) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hd : f .d i = false) (he : f .e i = false)
    (hva : valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) = vaBase n b' (i + 1))
    (hbp : BPrev n hn (policyValue n hn (policyOf n f)) i = Gm n b m)
    (hcn : valAt n hn (policyValue n hn (policyOf n f)) .c n = Gm n b m)
    (hHgt : Gm n b m < rewardH n i + vaBase n b' (i + 1)) :
    let V := policyValue n hn (policyOf n f)
    Gm n b m < FRhs n hn V i ∧
    FRhs n hn V i < 1 + Gm n b m ∧
    GRhs n hn V i + 300 < Gm n b m := by
  intro V
  have hH : HVal n hn V i = rewardH n i + vaBase n b' (i + 1) := by
    unfold HVal; rw [hva]
  have hF := FRhs_of_de_false_false hn f hi2 hin hd he
  change FRhs n hn V i =
    epsilon n * HVal n hn V i +
      (1 - epsilon n) / 2 * BPrev n hn V i +
      (1 - epsilon n) / 2 * (1 + valAt n hn V .c n) at hF
  rw [hcn, hbp, hH] at hF
  have heps : 0 < epsilon n := epsilon_pos n
  have heps1 : epsilon n < 1 := epsilon_lt_one hn
  have hq := eps_mul_le_quarter hn
    (abs_HVal_sub_Gm_le (b' := b') (b := b) hn hm1 hmn (by omega) hin)
  have hq_up := (abs_le.mp hq).2
  have hpos : 0 < epsilon n * (rewardH n i + vaBase n b' (i + 1) - Gm n b m) :=
    mul_pos heps (by linarith)
  have h1 : Gm n b m < FRhs n hn V i := by linarith
  have h2 : FRhs n hn V i < 1 + Gm n b m := by linarith
  have h3 : GRhs n hn V i + 300 < Gm n b m := by
    unfold GRhs
    have hrg := rewardG_le_neg_343 hn hi2
    linarith
  exact ⟨h1, h2, h3⟩

lemma Gm_lt_Gm_of_lt_of_testBit {n b m i : ℕ} (hn : 3 ≤ n)
    (hm1 : 1 ≤ m) (hlt : m < i) (hin : i ≤ n) (hbi : b.testBit (i - 1) = true) :
    Gm n b i + 42 ≤ Gm n b m := by
  have hi : Gm n b i = vaBase n b i := by
    unfold Gm; rw [vaBase_step hin, if_pos hbi]
  have hanti : vaBase n b i ≤ vaBase n b (m + 1) :=
    vaBase_anti hn (by omega : m + 1 ≤ i)
  have hgh := rewardGH_ge_42 (n := n) hn hm1
  rw [hi]
  unfold Gm
  linarith

lemma Gm_lt_Gm_mu_of_odd {n b i : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hi1 : 1 ≤ i) (hilt : i < mu n b) :
    Gm n b i + 41 ≤ Gm n b (mu n b) := by
  rcases mu_spec hn hodd hb with ⟨_, hmun, hmubit, hmumin⟩
  have hbi := hmumin i hi1 hilt
  have hi : Gm n b i = vaBase n b i := by
    unfold Gm; rw [vaBase_step (by omega : i ≤ n), if_pos hbi]
  have hanti : vaBase n b i ≤ vaBase n b 1 := vaBase_anti hn hi1
  have hgap := odd_gap_ge_41 hn (by omega) hmun hmubit
  rw [hi]
  unfold Gm
  linarith

lemma HVal_gt_Gm_nu_of_even {n b i : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0)
    (hpos : 0 < b) (hb : b < 2 ^ n) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    Gm n b (nu n b) + 7 ≤ rewardH n i + vaBase n b (i + 1) := by
  rcases nu_spec hn heven hpos hb with ⟨hnu2, hnun, _, _⟩
  by_cases hlt : i < nu n b
  · rw [vaBase_eq_Gm_nu_of_even hn heven hpos hb (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ nu n b)]
    rw [rewardH_eq]
    have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
    have hp : (scale n) ^ 2 ≤ (scale n) ^ (2 * i) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hs2 : (49 : ℚ) ≤ (scale n) ^ 2 := by nlinarith
    linarith
  · exact HVal_gt_Gm hn (by omega) (by omega) hin

lemma GRhs_eq_Gm_of_de_true_true {n b' i : ℕ} (hn : 3 ≤ n)
    (f : Kind → ℕ → Bool) (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hd : f .d i = true) (he : f .e i = true)
    (hva : valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) = vaBase n b' (i + 1)) :
    GRhs n hn (policyValue n hn (policyOf n f)) i = Gm n b' i := by
  rw [GRhs_of_de_true_true hn f hi2 hin hd he, hva]; rfl

lemma FRhs_eq_HVal_of_de_true_true {n b' i : ℕ} (hn : 3 ≤ n)
    (f : Kind → ℕ → Bool) (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hd : f .d i = true) (he : f .e i = true)
    (hva : valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) = vaBase n b' (i + 1)) :
    FRhs n hn (policyValue n hn (policyOf n f)) i = rewardH n i + vaBase n b' (i + 1) := by
  rw [FRhs_of_de_true_true hn f hi2 hin hd he]
  unfold HVal; rw [hva]

@[simp] lemma columnRank_a_true (n i : ℕ) :
    columnRank n ⟨.a, i, true⟩ = 8 * n - 8 + 2 * (n - i) := rfl
@[simp] lemma columnRank_a_false (n i : ℕ) :
    columnRank n ⟨.a, i, false⟩ = 8 * n - 8 + 2 * (n - i) + 1 := rfl
@[simp] lemma columnRank_b_true (n i : ℕ) :
    columnRank n ⟨.b, i, true⟩ = 4 * (i - 2) + 3 := rfl
@[simp] lemma columnRank_b_false (n i : ℕ) :
    columnRank n ⟨.b, i, false⟩ = 4 * (i - 2) + 4 := rfl
@[simp] lemma columnRank_c_true (n i : ℕ) :
    columnRank n ⟨.c, i, true⟩ = 4 * n - 5 + 2 * (i - 2) + 1 := rfl
@[simp] lemma columnRank_c_false (n i : ℕ) :
    columnRank n ⟨.c, i, false⟩ = 4 * n - 5 + 2 * (i - 2) := rfl
@[simp] lemma columnRank_d_true (n i : ℕ) :
    columnRank n ⟨.d, i, true⟩ = 7 * n - 7 + (i - 2) := rfl
@[simp] lemma columnRank_d_false (n i : ℕ) :
    columnRank n ⟨.d, i, false⟩ = 4 * (i - 2) + 1 := rfl
@[simp] lemma columnRank_e_true (n i : ℕ) :
    columnRank n ⟨.e, i, true⟩ = if i = 1 then 0 else 4 * (i - 2) + 2 := rfl
@[simp] lemma columnRank_e_false (n i : ℕ) :
    columnRank n ⟨.e, i, false⟩ = 6 * n - 7 + (i - 1) := rfl

lemma mdpImproving_a_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.a, i)) :
    mdpImproving n hn (policyOf n f) (mkRow n hn (.a, i) hv) ↔
      if f .a i then
        GRhs n hn (policyValue n hn (policyOf n f)) i <
          valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1)
      else
        valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) <
          GRhs n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpImproving_policyOf_iff]
  cases f .a i <;> rfl

lemma mdpStrictNonImproving_a_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.a, i)) :
    mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.a, i) hv) ↔
      if f .a i then
        valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) <
          GRhs n hn (policyValue n hn (policyOf n f)) i
      else
        GRhs n hn (policyValue n hn (policyOf n f)) i <
          valAt n hn (policyValue n hn (policyOf n f)) .a (i + 1) := by
  rw [mdpStrictNonImproving_policyOf_iff]
  cases f .a i <;> rfl

lemma mdpImproving_b_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.b, i)) :
    mdpImproving n hn (policyOf n f) (mkRow n hn (.b, i) hv) ↔
      if f .b i then
        GRhs n hn (policyValue n hn (policyOf n f)) i <
          BPrev n hn (policyValue n hn (policyOf n f)) i
      else
        BPrev n hn (policyValue n hn (policyOf n f)) i <
          GRhs n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpImproving_policyOf_iff]
  cases f .b i <;> rfl

lemma mdpStrictNonImproving_b_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.b, i)) :
    mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.b, i) hv) ↔
      if f .b i then
        BPrev n hn (policyValue n hn (policyOf n f)) i <
          GRhs n hn (policyValue n hn (policyOf n f)) i
      else
        GRhs n hn (policyValue n hn (policyOf n f)) i <
          BPrev n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpStrictNonImproving_policyOf_iff]
  cases f .b i <;> rfl

lemma mdpImproving_c_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.c, i)) :
    mdpImproving n hn (policyOf n f) (mkRow n hn (.c, i) hv) ↔
      if f .c i then
        GRhs n hn (policyValue n hn (policyOf n f)) i <
          CPrev n hn (policyValue n hn (policyOf n f)) i
      else
        CPrev n hn (policyValue n hn (policyOf n f)) i <
          GRhs n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpImproving_policyOf_iff]
  cases f .c i <;> rfl

lemma mdpStrictNonImproving_c_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.c, i)) :
    mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.c, i) hv) ↔
      if f .c i then
        CPrev n hn (policyValue n hn (policyOf n f)) i <
          GRhs n hn (policyValue n hn (policyOf n f)) i
      else
        GRhs n hn (policyValue n hn (policyOf n f)) i <
          CPrev n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpStrictNonImproving_policyOf_iff]
  cases f .c i <;> rfl

lemma mdpImproving_d_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.d, i)) :
    mdpImproving n hn (policyOf n f) (mkRow n hn (.d, i) hv) ↔
      if f .d i then
        FRhs n hn (policyValue n hn (policyOf n f)) i <
          BPrev n hn (policyValue n hn (policyOf n f)) i
      else
        BPrev n hn (policyValue n hn (policyOf n f)) i <
          FRhs n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpImproving_policyOf_iff]
  cases f .d i <;> rfl

lemma mdpStrictNonImproving_d_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.d, i)) :
    mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.d, i) hv) ↔
      if f .d i then
        BPrev n hn (policyValue n hn (policyOf n f)) i <
          FRhs n hn (policyValue n hn (policyOf n f)) i
      else
        FRhs n hn (policyValue n hn (policyOf n f)) i <
          BPrev n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpStrictNonImproving_policyOf_iff]
  cases f .d i <;> rfl

lemma mdpImproving_e_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.e, i)) (hi2 : 2 ≤ i) :
    mdpImproving n hn (policyOf n f) (mkRow n hn (.e, i) hv) ↔
      if f .e i then
        FRhs n hn (policyValue n hn (policyOf n f)) i <
          1 + valAt n hn (policyValue n hn (policyOf n f)) .c n
      else
        1 + valAt n hn (policyValue n hn (policyOf n f)) .c n <
          FRhs n hn (policyValue n hn (policyOf n f)) i := by
  rw [mdpImproving_policyOf_iff]
  have hne : i ≠ 1 := by omega
  cases f .e i <;> simp [qFormula, hne]

lemma mdpStrictNonImproving_e_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    {i : ℕ} (hv : ValidRow n (.e, i)) (hi2 : 2 ≤ i) :
    mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.e, i) hv) ↔
      if f .e i then
        1 + valAt n hn (policyValue n hn (policyOf n f)) .c n <
          FRhs n hn (policyValue n hn (policyOf n f)) i
      else
        FRhs n hn (policyValue n hn (policyOf n f)) i <
          1 + valAt n hn (policyValue n hn (policyOf n f)) .c n := by
  rw [mdpStrictNonImproving_policyOf_iff]
  have hne : i ≠ 1 := by omega
  cases f .e i <;> simp [qFormula, hne]

lemma mdpImproving_e_one_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    (hv : ValidRow n (.e, 1)) :
    mdpImproving n hn (policyOf n f) (mkRow n hn (.e, 1) hv) ↔
      if f .e 1 then
        HVal n hn (policyValue n hn (policyOf n f)) 1 <
          1 + valAt n hn (policyValue n hn (policyOf n f)) .c n
      else
        1 + valAt n hn (policyValue n hn (policyOf n f)) .c n <
          HVal n hn (policyValue n hn (policyOf n f)) 1 := by
  rw [mdpImproving_policyOf_iff]
  have heps : 0 < epsilon n := epsilon_pos n
  cases hf : f .e 1
  · have hval := valAt_e_one_of_false hn f hf
    simp only [qFormula, Bool.not_false, Bool.false_eq_true, ↓reduceIte, hval]
    constructor
    · intro h
      have h1 : 0 < epsilon n * (HVal n hn (policyValue n hn (policyOf n f)) 1 -
          (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) := by linarith
      have h2 := (mul_pos_iff_of_pos_left heps).mp h1
      linarith
    · intro h
      have h1 : 0 < epsilon n * (HVal n hn (policyValue n hn (policyOf n f)) 1 -
          (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) :=
        mul_pos heps (by linarith)
      linarith
  · have hval := valAt_e_one_of_true hn f hf
    simp only [qFormula, Bool.not_true, ↓reduceIte, hval]
    constructor <;> intro h <;> linarith

lemma mdpStrictNonImproving_e_one_iff {n : ℕ} (hn : 3 ≤ n) (f : Kind → ℕ → Bool)
    (hv : ValidRow n (.e, 1)) :
    mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.e, 1) hv) ↔
      if f .e 1 then
        1 + valAt n hn (policyValue n hn (policyOf n f)) .c n <
          HVal n hn (policyValue n hn (policyOf n f)) 1
      else
        HVal n hn (policyValue n hn (policyOf n f)) 1 <
          1 + valAt n hn (policyValue n hn (policyOf n f)) .c n := by
  rw [mdpStrictNonImproving_policyOf_iff]
  have heps : 0 < epsilon n := epsilon_pos n
  cases hf : f .e 1
  · have hval := valAt_e_one_of_false hn f hf
    simp only [qFormula, Bool.not_false, Bool.false_eq_true, ↓reduceIte, hval]
    constructor
    · intro h
      have h1 : epsilon n * (HVal n hn (policyValue n hn (policyOf n f)) 1 -
          (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) < 0 := by linarith
      nlinarith
    · intro h
      have h1 : epsilon n * (HVal n hn (policyValue n hn (policyOf n f)) 1 -
          (1 + valAt n hn (policyValue n hn (policyOf n f)) .c n)) < 0 :=
        mul_neg_of_pos_of_neg heps (by linarith)
      linarith
  · have hval := valAt_e_one_of_true hn f hf
    simp only [qFormula, Bool.not_true, ↓reduceIte, hval]
    constructor <;> intro h <;> linarith

lemma rewardG_add_Gm_lt_vaBase {n b m i : ℕ} (hn : 3 ≤ n)
    (hm1 : 1 ≤ m) (hlt : m < i) (hin : i ≤ n) (hbi : b.testBit (i - 1) = false) :
    rewardG n i + Gm n b m + 200 ≤ vaBase n b (i + 1) := by
  unfold Gm
  rw [vaBase_split_at_false (by omega : m + 1 ≤ i) hin hbi]
  have hsum : (∑ j ∈ Finset.Ico (m + 1) i, if b.testBit (j - 1) then rewardG n j + rewardH n j else 0) ≤
      ∑ j ∈ Finset.Ico (m + 1) i, (rewardG n j + rewardH n j) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · linarith
    · exact rewardGH_nonneg hn
  have hico := sum_rewardGH_Ico_le hn (i - (m + 1)) (m + 1) (by omega)
  rw [show (m + 1) + (i - (m + 1)) - 1 = i - 1 by omega,
    show (m + 1) + (i - (m + 1)) = i by omega,
    show 2 * (m + 1) - 2 = 2 * m by omega] at hico
  have hgm := rewardGH_le_sub_pow hn hm1
  have hp2 : (0 : ℚ) ≤ (scale n) ^ (2 * m - 2) := by have := scale_pos n; positivity
  have hrg : rewardG n i + (scale n) ^ (2 * (i - 1)) ≤ -294 := by
    rw [rewardG_eq (by omega : 1 ≤ i)]
    have heq : 2 * i - 1 = 2 * (i - 1) + 1 := by omega
    rw [heq, pow_succ']
    have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
    have hp : (49 : ℚ) ≤ (scale n) ^ (2 * (i - 1)) := by
      have h1 : (scale n) ^ 2 ≤ (scale n) ^ (2 * (i - 1)) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have hs2 : (49 : ℚ) ≤ (scale n) ^ 2 := by nlinarith
      linarith
    have hmul : 7 * (scale n) ^ (2 * (i - 1)) ≤ scale n * (scale n) ^ (2 * (i - 1)) :=
      mul_le_mul_of_nonneg_right hs (by linarith)
    linarith
  linarith

/-! ### Part 5: Odd Sweep `b → b + 1` (`b % 2 = 1`, `b < 2^n - 1`) -/

def oddAfterEMu (n b : ℕ) (k : Kind) (i : ℕ) : Bool :=
  match k with
  | .a => b.testBit (i - 1)
  | .b => false
  | .c => false
  | .d => true
  | .e => decide (i = mu n b) || b.testBit (i - 1)

def oddBlock1Fun (n b k : ℕ) (kind : Kind) (i : ℕ) : Bool :=
  match kind with
  | .a => b.testBit (i - 1)
  | .b => decide (i = mu n b)
  | .c => false
  | .d => if mu n b < i ∧ i < k then b.testBit (i - 1) else true
  | .e => if i = mu n b ∨ (mu n b < i ∧ i < k) then true else b.testBit (i - 1)

def oddBlock1MidFun (n b k : ℕ) (kind : Kind) (i : ℕ) : Bool :=
  match kind with
  | .a => b.testBit (i - 1)
  | .b => decide (i = mu n b)
  | .c => false
  | .d => if mu n b < i ∧ i ≤ k then b.testBit (i - 1) else true
  | .e => if i = mu n b ∨ (mu n b < i ∧ i < k) then true else b.testBit (i - 1)

lemma counterFun_odd_vals {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) :
    let f := counterFun n b
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    G1Val n hn V = Gm n b 1 ∧
    (∀ i, 2 ≤ i → i ≤ n → BPrev n hn V i = Gm n b 1) ∧
    (∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1) ∧
    valAt n hn V .c n = Gm n b 1 := by
  intro f V
  have hb0 : b.testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j _ _ hbj => ⟨rfl, hbj⟩)
  have hg1 : G1Val n hn V = Gm n b 1 := by
    rw [G1Val_of_e_one_true hn f hb0, hva 2 (le_refl 2)]; rfl
  have hbp : ∀ i, 2 ≤ i → i ≤ n → BPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin
    rw [BPrev_eq_G1Val hn f i hi2 hin (fun j _ _ => by dsimp [f, counterFun]; rw [if_pos hb0]), hg1]
  have hcp : ∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin
    rw [CPrev_eq_G1Val hn f i hi2 hin (fun j _ _ => by dsimp [f, counterFun]; rw [if_pos hb0]), hg1]
  have hcn : valAt n hn V .c n = Gm n b 1 := by
    rw [valAt_c_n_eq_G1Val hn f (fun j _ _ => by dsimp [f, counterFun]; rw [if_pos hb0]), hg1]
  exact ⟨hva, hg1, hbp, hcp, hcn⟩

lemma counterFun_odd_nonImproving {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    {k : Kind} {i : ℕ} (hv : ValidRow n (k, i))
    (hcol : columnRank n ⟨k, i, !counterFun n b k i⟩ < 4 * (mu n b - 2) + 2 ∨
      7 * n - 7 ≤ columnRank n ⟨k, i, !counterFun n b k i⟩) :
    mdpStrictNonImproving n hn (policyOf n (counterFun n b)) (mkRow n hn (k, i) hv) := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, hmumin⟩
  rcases counterFun_odd_vals hn hodd with ⟨hva, _, hbp, _, hcn⟩
  have hb0 : b.testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  set f := counterFun n b
  set V := policyValue n hn (policyOf n f)
  cases k with
  | a =>
    clear hcol
    have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    rw [mdpStrictNonImproving_a_iff, hva (i + 1) (by omega)]
    change if b.testBit (i - 1) = true then vaBase n b (i + 1) < GRhs n hn V i
      else GRhs n hn V i < vaBase n b (i + 1)
    cases hbi : b.testBit (i - 1)
    · rw [if_neg (by decide)]
      have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b) (b := b) (m := 1) (i := i)
        hn f hi2 hin (le_refl 1) (by omega) rfl hbi (hva (i + 1) (by omega)) hcn
      have hF_up := (abs_lt.mp hFG.1).2
      have hrg := rewardG_add_Gm_lt_vaBase (b := b) hn (le_refl 1) (by omega : 1 < i) hin hbi
      unfold GRhs
      linarith
    · rw [if_pos rfl]
      rw [GRhs_eq_Gm_of_de_true_true hn f hi2 hin rfl hbi (hva (i + 1) (by omega))]
      unfold Gm
      have := rewardGH_ge_42 (n := n) hn (by omega : 1 ≤ i)
      linarith
  | b =>
    have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n - 1 := hv.2
    have hfb : f .b i = false := by dsimp [f, counterFun]; rw [if_pos hb0]
    rw [hfb] at hcol
    simp only [Bool.not_false, columnRank_b_true] at hcol
    have hilt : i < mu n b := by omega
    have hbi := hmumin i (by omega) hilt
    rw [mdpStrictNonImproving_b_iff, hfb, if_neg (by decide), hbp i hi2 (by omega),
      GRhs_eq_Gm_of_de_true_true hn f hi2 (by omega) rfl hbi (hva (i + 1) (by omega))]
    have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (le_refl 1) (by omega : 1 < i) (by omega) hbi
    linarith
  | c =>
    have hfc : f .c i = false := by dsimp [f, counterFun]; rw [if_pos hb0]
    rw [hfc] at hcol
    simp only [Bool.not_false, columnRank_c_true] at hcol
    have : 2 ≤ i ∧ i ≤ n := hv
    omega
  | d =>
    have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    have hfd : f .d i = true := rfl
    rw [hfd] at hcol
    simp only [Bool.not_true, columnRank_d_false] at hcol
    have hile : i ≤ mu n b := by omega
    rw [mdpStrictNonImproving_d_iff, hfd, if_pos rfl, hbp i hi2 hin]
    have hH : Gm n b 1 + 7 ≤ rewardH n i + vaBase n b (i + 1) :=
      HVal_gt_Gm hn (le_refl 1) (by omega) hin
    rcases eq_or_lt_of_le hile with himu | hilt
    · subst himu
      have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b) (b := b) (m := 1) (i := mu n b)
        hn f hi2 hin (le_refl 1) (by omega) rfl hmubit (hva (mu n b + 1) (by omega)) hcn
      have h1 : 1 + Gm n b 1 < FRhs n hn V (mu n b) := hFG.2.1.mpr (by linarith)
      linarith
    · have hbi := hmumin i (by omega) hilt
      rw [FRhs_eq_HVal_of_de_true_true hn f hi2 hin rfl hbi (hva (i + 1) (by omega))]
      linarith
  | e =>
    have hi1 : 1 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    cases hbi : b.testBit (i - 1)
    · have hfe : f .e i = false := hbi
      rw [hfe] at hcol
      have hi2 : 2 ≤ i := by
        rcases eq_or_lt_of_le hi1 with rfl | h
        · rw [hb0] at hbi; contradiction
        · exact h
      simp only [Bool.not_false, columnRank_e_true, if_neg (by omega : i ≠ 1)] at hcol
      have hilt : i < mu n b := by omega
      have := hmumin i hi1 hilt
      rw [this] at hbi; contradiction
    · have hfe : f .e i = true := hbi
      rw [hfe] at hcol
      simp only [Bool.not_true, columnRank_e_false] at hcol
      omega

lemma odd_step_e_mu {n b m₀ : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    {s₀ : MDPState n} (hs₀ : StateAt n (counterFun n b) m₀ s₀)
    (hm₀ : m₀ = 0 ∨ (7 * n - 7 ≤ m₀ ∧ m₀ < 8 * n - 8)) :
    ∃ s₁ : MDPState n, MdpPath n hn 1 s₀ s₁ ∧
      StateAt n (oddAfterEMu n b) (4 * (mu n b - 2) + 2) s₁ := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rcases counterFun_odd_vals hn hodd with ⟨hva, _, _, _, hcn⟩
  have hb0 : b.testBit 0 = true := by rw [Nat.testBit_zero]; exact decide_eq_true hodd
  have hv₀ : ValidRow n (.e, mu n b) := ⟨by omega, hmun⟩
  have hf₀ : counterFun n b .e (mu n b) = false := hmubit
  have hrank : columnRank n ⟨.e, mu n b, !counterFun n b .e (mu n b)⟩ = 4 * (mu n b - 2) + 2 := by
    rw [hf₀, Bool.not_false, columnRank_e_true, if_neg (by omega)]
  have himp : mdpImproving n hn (policyOf n (counterFun n b)) (mkRow n hn (.e, mu n b) hv₀) := by
    rw [mdpImproving_e_iff hn _ hv₀ hmu2, hf₀, if_neg (by decide), hcn]
    have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b) (b := b) (m := 1) (i := mu n b)
      hn (counterFun n b) hmu2 hmun (le_refl 1) (by omega) rfl hmubit
      (hva (mu n b + 1) (by omega)) hcn
    have hH := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ mu n b) hmun
    exact hFG.2.1.mpr (by linarith)
  have hup : ∀ k i, ValidRow n (k, i) →
      (if k = .e ∧ i = mu n b then !counterFun n b .e (mu n b) else counterFun n b k i) =
        oddAfterEMu n b k i := by
    intro k i _
    by_cases h : k = .e ∧ i = mu n b
    · rcases h with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩, hf₀]
      dsimp [oddAfterEMu]; simp
    · rw [if_neg h]
      cases k <;> unfold counterFun oddAfterEMu <;> dsimp only
      · rw [if_pos hb0]
      · rw [if_pos hb0]
      · have hi : i ≠ mu n b := fun heq => h ⟨rfl, heq⟩
        rw [decide_eq_false hi, Bool.false_or]
  rcases hm₀ with rfl | ⟨hm₀1, hm₀2⟩
  · rcases step_stateAt_of_le hn hs₀ .e (mu n b) hv₀ (by rw [hrank]; omega) himp
      (fun k i hv _ hlt => counterFun_odd_nonImproving hn hodd hb hv (Or.inl (by rw [hrank] at hlt; exact hlt)))
      hup with ⟨s₁, hp, hs₁⟩
    rw [hrank] at hs₁
    exact ⟨s₁, hp, hs₁⟩
  · rcases step_stateAt_of_wrap hn hs₀ .e (mu n b) hv₀ (by rw [hrank]; omega) himp
      (fun k i hv hor => counterFun_odd_nonImproving hn hodd hb hv
        (by rw [hrank] at hor; rcases hor with h1 | h2; exact Or.inr (by omega); exact Or.inl h2))
      hup with ⟨s₁, hp, hs₁⟩
    rw [hrank] at hs₁
    exact ⟨s₁, hp, hs₁⟩

lemma odd_step_b_mu {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    {s₁ : MDPState n} (hs₁ : StateAt n (oddAfterEMu n b) (4 * (mu n b - 2) + 2) s₁) :
    ∃ t s₂ m₂, MdpPath n hn t s₁ s₂ ∧
      4 * (mu n b - 2) + 2 ≤ m₂ ∧ m₂ ≤ 4 * (mu n b - 2) + 3 ∧
      m₂ ≤ 4 * n - 6 ∧
      StateAt n (oddBlock1Fun n b (mu n b + 1)) m₂ s₂ := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  have hb0 : b.testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  by_cases hlt : mu n b < n
  · set f := oddAfterEMu n b
    set V := policyValue n hn (policyOf n f)
    have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
      intro i hi2
      exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
        (fun j _ _ hbj => ⟨rfl, by dsimp [f, oddAfterEMu]; rw [hbj, Bool.or_true]⟩)
    have hg1 : G1Val n hn V = Gm n b 1 := by
      have he1 : f .e 1 = true := by dsimp [f, oddAfterEMu]; rw [hb0, Bool.or_true]
      rw [G1Val_of_e_one_true hn f he1, hva 2 (le_refl 2)]; rfl
    have hbp : BPrev n hn V (mu n b) = Gm n b 1 := by
      rw [BPrev_eq_G1Val hn f (mu n b) hmu2 hmun (fun _ _ _ => rfl), hg1]
    have hv₀ : ValidRow n (.b, mu n b) := ⟨hmu2, by omega⟩
    have hf₀ : f .b (mu n b) = false := rfl
    have hrank : columnRank n ⟨.b, mu n b, !f .b (mu n b)⟩ = 4 * (mu n b - 2) + 3 := rfl
    have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.b, mu n b) hv₀) := by
      have he_mu : f .e (mu n b) = true := by dsimp [f, oddAfterEMu]; simp
      rw [mdpImproving_b_iff hn f hv₀, hf₀, if_neg (by decide), hbp,
        GRhs_eq_Gm_of_de_true_true hn f hmu2 hmun rfl he_mu (hva (mu n b + 1) (by omega))]
      have := Gm_one_lt_Gm_mu_of_odd hn hodd hb
      linarith
    have hup : ∀ k i, ValidRow n (k, i) →
        (if k = .b ∧ i = mu n b then !f .b (mu n b) else f k i) =
          oddBlock1Fun n b (mu n b + 1) k i := by
      intro k i _
      by_cases h : k = .b ∧ i = mu n b
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hf₀]
        dsimp [oddBlock1Fun]; simp
      · rw [if_neg h]
        cases k <;> dsimp [f, oddAfterEMu, oddBlock1Fun]
        · have hi : i ≠ mu n b := fun heq => h ⟨rfl, heq⟩
          rw [decide_eq_false hi]
        · rw [if_neg (by omega)]
        · by_cases hi : i = mu n b
          · subst hi; rw [if_pos (Or.inl rfl)]; simp
          · rw [decide_eq_false hi, Bool.false_or, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs₁ .b (mu n b) hv₀ (by rw [hrank]; omega) himp
      (fun _ _ _ h1 h2 => by rw [hrank] at h2; omega) hup with ⟨s₂, hp, hs₂⟩
    rw [hrank] at hs₂
    exact ⟨1, s₂, 4 * (mu n b - 2) + 3, hp, by omega, by omega, by omega, hs₂⟩
  · have hpol : policyOf n (oddAfterEMu n b) = policyOf n (oddBlock1Fun n b (mu n b + 1)) := by
      apply policyOf_ext hn
      intro k i hv
      cases k <;> dsimp [oddAfterEMu, oddBlock1Fun, ValidRow] at hv ⊢
      · symm; exact decide_eq_false (by omega)
      · rw [if_neg (by omega)]
      · by_cases hi : i = mu n b
        · subst hi; rw [if_pos (Or.inl rfl)]; simp
        · rw [decide_eq_false hi, Bool.false_or, if_neg (by omega)]
    refine ⟨0, s₁, 4 * (mu n b - 2) + 2, MdpPath.refl s₁, by omega, by omega, by omega, ?_⟩
    rcases hs₁ with ⟨hs₁pol, hs₁last, _, _, _, _⟩
    refine ⟨by rw [hs₁pol, hpol], hs₁last, .e, mu n b, ⟨by omega, hmun⟩, ?_⟩
    have he1 : oddBlock1Fun n b (mu n b + 1) .e (mu n b) = true := by
      dsimp [oddBlock1Fun]; rw [if_pos (Or.inl rfl)]
    rw [he1, columnRank_e_true, if_neg (by omega)]

lemma oddBlock1_vals {n b k : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (_hk1 : mu n b + 1 ≤ k) (_hkn : k ≤ n + 1) :
    let f := oddBlock1Fun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    G1Val n hn V = Gm n b 1 ∧
    (∀ i, 2 ≤ i → i ≤ mu n b → BPrev n hn V i = Gm n b 1) ∧
    (∀ i, mu n b < i → i ≤ n → BPrev n hn V i = Gm n b (mu n b)) ∧
    (∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1) ∧
    valAt n hn V .c n = Gm n b 1 := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, _, _⟩
  have hb0 : b.testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  intro f V
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j _ _ hbj => by
        dsimp [f, oddBlock1Fun]
        exact ⟨by split_ifs <;> first | rfl | exact hbj,
          by split_ifs <;> first | rfl | exact hbj⟩)
  have he1 : f .e 1 = true := by
    dsimp [f, oddBlock1Fun]; rw [if_neg (by omega)]; exact hb0
  have hg1 : G1Val n hn V = Gm n b 1 := by
    rw [G1Val_of_e_one_true hn f he1, hva 2 (le_refl 2)]; rfl
  have hbp_le : ∀ i, 2 ≤ i → i ≤ mu n b → BPrev n hn V i = Gm n b 1 := by
    intro i hi2 hile
    rw [BPrev_eq_G1Val hn f i hi2 (by omega)
      (fun j _ hj => by dsimp [f, oddBlock1Fun]; exact decide_eq_false (by omega)), hg1]
  have hbp_gt : ∀ i, mu n b < i → i ≤ n → BPrev n hn V i = Gm n b (mu n b) := by
    intro i higt hin
    have hbm : f .b (mu n b) = true := by dsimp [f, oddBlock1Fun]; simp
    have hdm : f .d (mu n b) = true := by dsimp [f, oddBlock1Fun]; rw [if_neg (by omega)]
    have hem : f .e (mu n b) = true := by dsimp [f, oddBlock1Fun]; rw [if_pos (Or.inl rfl)]
    rw [BPrev_eq_Gm hn f hmu2 hbm hdm hem i higt hin
      (fun j hj1 _ => by dsimp [f, oddBlock1Fun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega)]
    rfl
  have hcp : ∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin
    rw [CPrev_eq_G1Val hn f i hi2 hin (fun _ _ _ => rfl), hg1]
  have hcn : valAt n hn V .c n = Gm n b 1 := by
    rw [valAt_c_n_eq_G1Val hn f (fun _ _ _ => rfl), hg1]
  exact ⟨hva, hg1, hbp_le, hbp_gt, hcp, hcn⟩

lemma oddBlock1_nonImproving_lt {n b k : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hk1 : mu n b + 1 ≤ k) (hkn : k ≤ n + 1)
    {kind : Kind} {i : ℕ} (hv : ValidRow n (kind, i))
    (hgt : 4 * (mu n b - 2) + 2 < columnRank n ⟨kind, i, !oddBlock1Fun n b k kind i⟩)
    (hlt1 : columnRank n ⟨kind, i, !oddBlock1Fun n b k kind i⟩ < 4 * (k - 2) + 1)
    (hlt2 : columnRank n ⟨kind, i, !oddBlock1Fun n b k kind i⟩ < 4 * n - 5) :
    mdpStrictNonImproving n hn (policyOf n (oddBlock1Fun n b k)) (mkRow n hn (kind, i) hv) := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rcases oddBlock1_vals hn hodd hb hk1 hkn with ⟨hva, _, hbp_le, hbp_gt, _, hcn⟩
  set f := oddBlock1Fun n b k
  set V := policyValue n hn (policyOf n f)
  cases kind with
  | a =>
    have : 2 ≤ i ∧ i ≤ n := hv
    cases hfa : f .a i <;> rw [hfa] at hlt2 <;>
      simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt2 <;>
      omega
  | c =>
    have : 2 ≤ i ∧ i ≤ n := hv
    cases hfc : f .c i <;> rw [hfc] at hlt2 <;>
      simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hlt2 <;>
      omega
  | b =>
    have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n - 1 := hv.2
    by_cases himu : i = mu n b
    · subst himu
      have hfb : f .b (mu n b) = true := by dsimp [f, oddBlock1Fun]; simp
      have hfd : f .d (mu n b) = true := by dsimp [f, oddBlock1Fun]; rw [if_neg (by omega)]
      have hfe : f .e (mu n b) = true := by dsimp [f, oddBlock1Fun]; rw [if_pos (Or.inl rfl)]
      rw [mdpStrictNonImproving_b_iff, hfb, if_pos rfl, hbp_le (mu n b) hmu2 (le_refl _),
        GRhs_eq_Gm_of_de_true_true hn f hmu2 hmun hfd hfe (hva (mu n b + 1) (by omega))]
      have := Gm_one_lt_Gm_mu_of_odd hn hodd hb
      linarith
    · have hfb : f .b i = false := by dsimp [f, oddBlock1Fun]; exact decide_eq_false himu
      rw [hfb] at hgt hlt1
      simp only [Bool.not_false, columnRank_b_true] at hgt hlt1
      have higt : mu n b < i := by omega
      have hilt : i < k := by omega
      have hfe : f .e i = true := by
        dsimp [f, oddBlock1Fun]; rw [if_pos (Or.inr ⟨higt, hilt⟩)]
      rw [mdpStrictNonImproving_b_iff, hfb, if_neg (by decide), hbp_gt i higt (by omega)]
      cases hbi : b.testBit (i - 1)
      · have hfd : f .d i = false := by
          dsimp [f, oddBlock1Fun]; rw [if_pos ⟨higt, hilt⟩, hbi]
        have hFG := FRhs_GRhs_of_de_false_true_Gm (b' := b) (b := b) (m := mu n b) (i := i)
          hn f hi2 (by omega) (by omega) hmun hfd hfe (hva (i + 1) (by omega))
          (hbp_gt i higt (by omega))
        linarith [hFG.2.2.2]
      · have hfd : f .d i = true := by
          dsimp [f, oddBlock1Fun]; rw [if_pos ⟨higt, hilt⟩, hbi]
        rw [GRhs_eq_Gm_of_de_true_true hn f hi2 (by omega) hfd hfe (hva (i + 1) (by omega))]
        have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (by omega : 1 ≤ mu n b) higt (by omega) hbi
        linarith
  | d =>
    have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    cases hfd : f .d i
    · rw [hfd] at hlt2
      simp only [Bool.not_false, columnRank_d_true] at hlt2
      omega
    · rw [hfd] at hgt hlt1
      simp only [Bool.not_true, columnRank_d_false] at hgt hlt1
      have higt : mu n b < i := by omega
      have hilt : i < k := by omega
      have hbi : b.testBit (i - 1) = true := by
        dsimp [f, oddBlock1Fun] at hfd
        rw [if_pos ⟨higt, hilt⟩] at hfd
        exact hfd
      have hfe : f .e i = true := by
        dsimp [f, oddBlock1Fun]; rw [if_pos (Or.inr ⟨higt, hilt⟩)]
      rw [mdpStrictNonImproving_d_iff, hfd, if_pos rfl, hbp_gt i higt hin,
        FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
      have := HVal_gt_Gm (b := b) hn (by omega : 1 ≤ mu n b) (by omega : mu n b ≤ i) hin
      linarith
  | e =>
    have hi1 : 1 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    cases hfe : f .e i
    · rw [hfe] at hgt hlt1
      have hi2 : 2 ≤ i := by
        rcases eq_or_lt_of_le hi1 with rfl | h
        · have hb0 : b.testBit 0 = true := by rw [Nat.testBit_zero]; exact decide_eq_true hodd
          dsimp [f, oddBlock1Fun] at hfe
          rw [if_neg (by omega), hb0] at hfe; contradiction
        · exact h
      simp only [Bool.not_false, columnRank_e_true, if_neg (by omega : i ≠ 1)] at hgt hlt1
      have higt : mu n b < i := by omega
      have hilt : i < k := by omega
      dsimp [f, oddBlock1Fun] at hfe
      rw [if_pos (Or.inr ⟨higt, hilt⟩)] at hfe
      contradiction
    · rw [hfe] at hlt2
      simp only [Bool.not_true, columnRank_e_false] at hlt2
      omega

lemma oddBlock1Mid_vals {n b k : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hk1 : mu n b + 1 ≤ k) (hkn : k ≤ n) :
    let f := oddBlock1MidFun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    G1Val n hn V = Gm n b 1 ∧
    BPrev n hn V k = Gm n b (mu n b) ∧
    valAt n hn V .c n = Gm n b 1 := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, _, _⟩
  have hb0 : b.testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  intro f V
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j _ _ hbj => by
        dsimp [f, oddBlock1MidFun]
        exact ⟨by split_ifs <;> first | rfl | exact hbj,
          by split_ifs <;> first | rfl | exact hbj⟩)
  have he1 : f .e 1 = true := by
    dsimp [f, oddBlock1MidFun]; rw [if_neg (by omega)]; exact hb0
  have hg1 : G1Val n hn V = Gm n b 1 := by
    rw [G1Val_of_e_one_true hn f he1, hva 2 (le_refl 2)]; rfl
  have hbp : BPrev n hn V k = Gm n b (mu n b) := by
    have hbm : f .b (mu n b) = true := by dsimp [f, oddBlock1MidFun]; simp
    have hdm : f .d (mu n b) = true := by dsimp [f, oddBlock1MidFun]; rw [if_neg (by omega)]
    have hem : f .e (mu n b) = true := by dsimp [f, oddBlock1MidFun]; rw [if_pos (Or.inl rfl)]
    rw [BPrev_eq_Gm hn f hmu2 hbm hdm hem k (by omega) hkn
      (fun j hj1 _ => by dsimp [f, oddBlock1MidFun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega)]
    rfl
  have hcn : valAt n hn V .c n = Gm n b 1 := by
    rw [valAt_c_n_eq_G1Val hn f (fun _ _ _ => rfl), hg1]
  exact ⟨hva, hg1, hbp, hcn⟩

lemma odd_block1_step {n b k m : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hk1 : mu n b + 1 ≤ k) (hkn : k ≤ n)
    {s : MDPState n} (hs : StateAt n (oddBlock1Fun n b k) m s)
    (hm1 : 4 * (mu n b - 2) + 2 ≤ m) (hm2 : m + 1 ≤ 4 * (k - 2)) (hm3 : m ≤ 4 * n - 6) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      4 * (mu n b - 2) + 2 ≤ m' ∧ m' + 1 ≤ 4 * (k + 1 - 2) ∧ m' ≤ 4 * n - 6 ∧
      StateAt n (oddBlock1Fun n b (k + 1)) m' s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, _, _⟩
  cases hbk : b.testBit (k - 1)
  · rcases oddBlock1_vals hn hodd hb hk1 (by omega) with ⟨hva, _, _, hbp_gt, _, hcn⟩
    have hv₁ : ValidRow n (.d, k) := ⟨by omega, hkn⟩
    have hfd : oddBlock1Fun n b k .d k = true := by dsimp [oddBlock1Fun]; rw [if_neg (by omega)]
    have hfe : oddBlock1Fun n b k .e k = false := by dsimp [oddBlock1Fun]; rw [if_neg (by omega), hbk]
    have hrank₁ : columnRank n ⟨.d, k, !oddBlock1Fun n b k .d k⟩ = 4 * (k - 2) + 1 := by
      rw [hfd, Bool.not_true, columnRank_d_false]
    have himp₁ : mdpImproving n hn (policyOf n (oddBlock1Fun n b k)) (mkRow n hn (.d, k) hv₁) := by
      rw [mdpImproving_d_iff hn _ hv₁, hfd, if_pos rfl, hbp_gt k (by omega) hkn]
      have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b) (b := b) (m := 1) (i := k)
        hn (oddBlock1Fun n b k) (by omega) hkn (le_refl 1) (by omega) hfd hfe
        (hva (k + 1) (by omega)) hcn
      have hF_up := (abs_lt.mp hFG.1).2
      have hmu := Gm_one_lt_Gm_mu_of_odd hn hodd hb
      linarith
    have hup₁ : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .d ∧ i = k then !oddBlock1Fun n b k .d k else oddBlock1Fun n b k kind i) =
          oddBlock1MidFun n b k kind i := by
      intro kind i _
      by_cases h : kind = .d ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hfd]
        dsimp [oddBlock1MidFun]; rw [if_pos ⟨by omega, le_refl _⟩, hbk]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [oddBlock1Fun, oddBlock1MidFun]
        have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
        by_cases h1 : mu n b < i ∧ i < k
        · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs .d k hv₁ (by rw [hrank₁]; omega) himp₁
      (fun kind i hv h1 h2 => by
        rw [hrank₁] at h2
        exact oddBlock1_nonImproving_lt hn hodd hb hk1 (by omega) hv (by omega) h2 (by omega))
      hup₁ with ⟨s₁, hp₁, hs₁⟩
    rw [hrank₁] at hs₁
    rcases oddBlock1Mid_vals hn hodd hb hk1 hkn with ⟨hva₂, _, hbp₂, hcn₂⟩
    set f₂ := oddBlock1MidFun n b k
    have hv₂ : ValidRow n (.e, k) := ⟨by omega, hkn⟩
    have hfd₂ : f₂ .d k = false := by
      dsimp [f₂, oddBlock1MidFun]; rw [if_pos ⟨by omega, le_refl _⟩, hbk]
    have hfe₂ : f₂ .e k = false := by
      dsimp [f₂, oddBlock1MidFun]; rw [if_neg (by omega), hbk]
    have hrank₂ : columnRank n ⟨.e, k, !f₂ .e k⟩ = 4 * (k - 2) + 2 := by
      rw [hfe₂, Bool.not_false, columnRank_e_true, if_neg (by omega)]
    have himp₂ : mdpImproving n hn (policyOf n f₂) (mkRow n hn (.e, k) hv₂) := by
      rw [mdpImproving_e_iff hn f₂ hv₂ (by omega), hfe₂, if_neg (by decide)]
      apply FRhs_gt_one_add_cn_of_de_false_false hn f₂ (by omega) hkn hfd₂ hfe₂
      · unfold HVal
        rw [hcn₂, hva₂ (k + 1) (by omega)]
        have := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ k) hkn
        linarith
      · rw [hcn₂, hbp₂]
        have := Gm_one_lt_Gm_mu_of_odd hn hodd hb
        linarith
    have hup₂ : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .e ∧ i = k then !f₂ .e k else f₂ kind i) = oddBlock1Fun n b (k + 1) kind i := by
      intro kind i _
      by_cases h : kind = .e ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hfe₂]
        dsimp [oddBlock1Fun]; rw [if_pos (Or.inr ⟨by omega, by omega⟩)]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [f₂, oddBlock1MidFun, oddBlock1Fun]
        · by_cases h1 : mu n b < i ∧ i ≤ k
          · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
          · rw [if_neg h1, if_neg (by omega)]
        · have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
          by_cases h1 : i = mu n b ∨ mu n b < i ∧ i < k
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs₁ .e k hv₂ (by rw [hrank₂]; omega) himp₂
      (fun _ _ _ h1 h2 => by rw [hrank₂] at h2; omega) hup₂ with ⟨s₂, hp₂, hs₂⟩
    rw [hrank₂] at hs₂
    exact ⟨2, s₂, 4 * (k - 2) + 2, hp₁.trans hp₂, by omega, by omega, by omega, hs₂⟩
  · have hfeq : oddBlock1Fun n b (k + 1) = oddBlock1Fun n b k := by
      funext kind i
      cases kind <;> dsimp [oddBlock1Fun]
      · by_cases hi : i = k
        · subst hi
          rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega), hbk]
        · by_cases h1 : mu n b < i ∧ i < k
          · rw [if_pos ⟨h1.1, by omega⟩, if_pos h1]
          · rw [if_neg (by omega), if_neg h1]
      · by_cases hi : i = k
        · subst hi
          rw [if_pos (Or.inr ⟨by omega, by omega⟩), if_neg (by omega), hbk]
        · by_cases h1 : i = mu n b ∨ mu n b < i ∧ i < k
          · rw [if_pos (by omega), if_pos h1]
          · rw [if_neg (by omega), if_neg h1]
    refine ⟨0, s, m, MdpPath.refl s, hm1, by omega, hm3, ?_⟩
    rw [hfeq]; exact hs

lemma odd_block1_loop {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1) :
    ∀ k, mu n b + 1 ≤ k → k ≤ n + 1 →
      ∀ {s m}, StateAt n (oddBlock1Fun n b k) m s →
        4 * (mu n b - 2) + 2 ≤ m → m + 1 ≤ 4 * (k - 2) → m ≤ 4 * n - 6 →
        ∃ t s' m', MdpPath n hn t s s' ∧
          4 * (mu n b - 2) + 2 ≤ m' ∧ m' ≤ 4 * n - 6 ∧
          StateAt n (oddBlock1Fun n b (n + 1)) m' s' := by
  intro k hk1 hkn
  induction h : n + 1 - k generalizing k with
  | zero =>
    have hk : k = n + 1 := by omega
    subst hk
    intro s m hs hm1 _ hm3
    exact ⟨0, s, m, MdpPath.refl s, hm1, hm3, hs⟩
  | succ d ih =>
    intro s m hs hm1 hm2 hm3
    have hkn' : k ≤ n := by omega
    rcases odd_block1_step hn hodd hb hk1 hkn' hs hm1 hm2 hm3 with
      ⟨t₁, s₁, m₁, hp₁, hm₁1, hm₁2, hm₁3, hs₁⟩
    rcases ih (k + 1) (by omega) (by omega) (by omega) hs₁ hm₁1 hm₁2 hm₁3 with
      ⟨t₂, s₂, m₂, hp₂, hm₂1, hm₂3, hs₂⟩
    exact ⟨t₁ + t₂, s₂, m₂, hp₁.trans hp₂, hm₂1, hm₂3, hs₂⟩

def oddBlock3Fun (n b k : ℕ) (kind : Kind) (i : ℕ) : Bool :=
  match kind with
  | .a => b.testBit (i - 1)
  | .b => decide (i = mu n b)
  | .c => decide (i = mu n b)
  | .d => if mu n b < i then b.testBit (i - 1) else true
  | .e => if i < k then (b + 1).testBit (i - 1) else true

lemma odd_block2_step {n b m : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    {s : MDPState n} (hs : StateAt n (oddBlock1Fun n b (n + 1)) m s)
    (hm1 : 4 * (mu n b - 2) + 2 ≤ m) (hm3 : m ≤ 4 * n - 6) :
    ∃ s' : MDPState n, MdpPath n hn 1 s s' ∧
      StateAt n (oddBlock3Fun n b 1) (4 * n - 5 + 2 * (mu n b - 2) + 1) s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, hmumin⟩
  rcases oddBlock1_vals (k := n + 1) hn hodd hb (by omega) (le_refl _) with
    ⟨hva, _, _, _, hcp, _⟩
  set f := oddBlock1Fun n b (n + 1)
  have hv₀ : ValidRow n (.c, mu n b) := ⟨hmu2, hmun⟩
  have hf₀ : f .c (mu n b) = false := rfl
  have hrank : columnRank n ⟨.c, mu n b, !f .c (mu n b)⟩ = 4 * n - 5 + 2 * (mu n b - 2) + 1 := rfl
  have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.c, mu n b) hv₀) := by
    have hfd : f .d (mu n b) = true := by dsimp [f, oddBlock1Fun]; rw [if_neg (by omega)]
    have hfe : f .e (mu n b) = true := by dsimp [f, oddBlock1Fun]; rw [if_pos (Or.inl rfl)]
    rw [mdpImproving_c_iff hn f hv₀, hf₀, if_neg (by decide), hcp (mu n b) hmu2 hmun,
      GRhs_eq_Gm_of_de_true_true hn f hmu2 hmun hfd hfe (hva (mu n b + 1) (by omega))]
    have := Gm_one_lt_Gm_mu_of_odd hn hodd hb
    linarith
  have hno : ∀ kind i (hv : ValidRow n (kind, i)),
      m < columnRank n ⟨kind, i, !f kind i⟩ →
      columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.c, mu n b, !f .c (mu n b)⟩ →
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
    intro kind i hv hgt hlt
    rw [hrank] at hlt
    by_cases hlt4 : columnRank n ⟨kind, i, !oddBlock1Fun n b (n + 1) kind i⟩ < 4 * n - 5
    · change m < columnRank n ⟨kind, i, !oddBlock1Fun n b (n + 1) kind i⟩ at hgt
      exact oddBlock1_nonImproving_lt hn hodd hb (by omega) (le_refl _) hv
        (by omega) (by omega) hlt4
    · change ¬ columnRank n ⟨kind, i, !f kind i⟩ < 4 * n - 5 at hlt4
      cases kind
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfa : f .a i <;> rw [hfa] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n - 1 := hv
        cases hfb : f .b i <;> rw [hfb] at hlt4 <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hlt4 <;>
          omega
      · have hi2 : 2 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        have hfc : f .c i = false := rfl
        rw [hfc] at hlt
        simp only [Bool.not_false, columnRank_c_true] at hlt
        have hilt : i < mu n b := by omega
        have hbi := hmumin i (by omega) hilt
        have hfd : f .d i = true := by dsimp [f, oddBlock1Fun]; rw [if_neg (by omega)]
        have hfe : f .e i = true := by dsimp [f, oddBlock1Fun]; rw [if_neg (by omega)]; exact hbi
        rw [mdpStrictNonImproving_c_iff, hfc, if_neg (by decide), hcp i hi2 hin,
          GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
        have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (le_refl 1) (by omega : 1 < i) hin hbi
        linarith
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfd : f .d i <;> rw [hfd] at hlt4 hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hlt4 hlt <;>
          omega
      · have : 1 ≤ i ∧ i ≤ n := hv
        cases hfe : f .e i <;> rw [hfe] at hlt4 hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hlt4 hlt
        · split_ifs at hlt4 <;> omega
        · omega
  have hup : ∀ kind i, ValidRow n (kind, i) →
      (if kind = .c ∧ i = mu n b then !f .c (mu n b) else f kind i) = oddBlock3Fun n b 1 kind i := by
    intro kind i hv
    by_cases h : kind = .c ∧ i = mu n b
    · rcases h with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩, hf₀]
      dsimp [oddBlock3Fun]; simp
    · rw [if_neg h]
      cases kind <;> dsimp [f, oddBlock1Fun, oddBlock3Fun, ValidRow] at hv ⊢
      · have hi : i ≠ mu n b := fun heq => h ⟨rfl, heq⟩
        rw [decide_eq_false hi]
      · by_cases h1 : mu n b < i
        · rw [if_pos ⟨h1, by omega⟩, if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
      · have hnot1 : ¬ i < 1 := by have := hv.1; omega
        rw [if_neg hnot1]
        by_cases h1 : i = mu n b ∨ mu n b < i ∧ i < n + 1
        · rw [if_pos h1]
        · have hilt : i < mu n b := by have := hv.2; omega
          rw [if_neg h1]; exact hmumin i hv.1 hilt
  rcases step_stateAt_of_le hn hs .c (mu n b) hv₀ (by rw [hrank]; omega) himp hno hup with
    ⟨s', hp, hs'⟩
  rw [hrank] at hs'
  exact ⟨s', hp, hs'⟩

lemma oddBlock3_vals {n b k : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (_hk1 : 1 ≤ k) (_hkn : k ≤ n + 1) :
    let f := oddBlock3Fun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → (k ≤ i ∨ mu n b ≤ i) → valAt n hn V .a i = vaBase n b i) ∧
    (∀ i, mu n b < i → i ≤ n → BPrev n hn V i = Gm n b (mu n b)) ∧
    (∀ i, mu n b < i → i ≤ n → CPrev n hn V i = Gm n b (mu n b)) ∧
    valAt n hn V .c n = Gm n b (mu n b) := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨_, hsucc_eq, hsucc_gt, _⟩
  intro f V
  have hva : ∀ i, 2 ≤ i → (k ≤ i ∨ mu n b ≤ i) → valAt n hn V .a i = vaBase n b i := by
    intro i hi2 hki
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j hij _ hbj => by
        dsimp [f, oddBlock3Fun]
        refine ⟨by split_ifs <;> first | rfl | exact hbj, ?_⟩
        split_ifs with hjk
        · have hjmu : mu n b < j := by
            have : mu n b ≤ j := by omega
            rcases eq_or_lt_of_le this with rfl | hlt
            · rw [hmubit] at hbj; contradiction
            · exact hlt
          rw [hsucc_gt j hjmu, hbj]
        · rfl)
  have hbm : f .b (mu n b) = true := by dsimp [f, oddBlock3Fun]; simp
  have hcm : f .c (mu n b) = true := by dsimp [f, oddBlock3Fun]; simp
  have hdm : f .d (mu n b) = true := by dsimp [f, oddBlock3Fun]; rw [if_neg (by omega)]
  have hem : f .e (mu n b) = true := by
    dsimp [f, oddBlock3Fun]; split_ifs <;> first | exact hsucc_eq | rfl
  have hbp : ∀ i, mu n b < i → i ≤ n → BPrev n hn V i = Gm n b (mu n b) := by
    intro i higt hin
    rw [BPrev_eq_Gm hn f hmu2 hbm hdm hem i higt hin
      (fun j hj1 _ => by dsimp [f, oddBlock3Fun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega) (Or.inr (by omega))]
    rfl
  have hcp : ∀ i, mu n b < i → i ≤ n → CPrev n hn V i = Gm n b (mu n b) := by
    intro i higt hin
    rw [CPrev_eq_Gm hn f hmu2 hcm hdm hem i higt hin
      (fun j hj1 _ => by dsimp [f, oddBlock3Fun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega) (Or.inr (by omega))]
    rfl
  have hcn : valAt n hn V .c n = Gm n b (mu n b) := by
    rw [valAt_c_n_eq_Gm hn f hmu2 hmun hcm hdm hem
      (fun j hj1 _ => by dsimp [f, oddBlock3Fun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega) (Or.inr (by omega))]
    rfl
  exact ⟨hva, hbp, hcp, hcn⟩

lemma odd_block3_step1 {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    {s : MDPState n} (hs : StateAt n (oddBlock3Fun n b 1) (4 * n - 5 + 2 * (mu n b - 2) + 1) s) :
    ∃ s' : MDPState n, MdpPath n hn 1 s s' ∧
      StateAt n (oddBlock3Fun n b 2) (6 * n - 7) s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨hsucc_lt, _, _, _⟩
  rcases oddBlock3_vals (k := 1) hn hodd hb (le_refl 1) (by omega) with
    ⟨hva, hbp, hcp, hcn⟩
  set f := oddBlock3Fun n b 1
  set V := policyValue n hn (policyOf n f)
  have hv₀ : ValidRow n (.e, 1) := ⟨le_refl 1, by omega⟩
  have hf₀ : f .e 1 = true := rfl
  have hrank : columnRank n ⟨.e, 1, !f .e 1⟩ = 6 * n - 7 := rfl
  have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.e, 1) hv₀) := by
    rw [mdpImproving_e_one_iff hn f, hf₀, if_pos rfl, hcn]
    have hH : HVal n hn V 1 = rewardH n 1 + vaBase n b 2 := by
      unfold HVal; rw [hva 2 (le_refl 2) (Or.inl (by omega))]
    rw [hH]
    have := HVal_lt_Gm_of_lt (b := b) hn (le_refl 1) hmu2 hmun hmubit
    linarith
  have hno : ∀ kind i (hv : ValidRow n (kind, i)),
      4 * n - 5 + 2 * (mu n b - 2) + 1 < columnRank n ⟨kind, i, !f kind i⟩ →
      columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.e, 1, !f .e 1⟩ →
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
    intro kind i hv hgt hlt
    rw [hrank] at hlt
    cases kind
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfa : f .a i <;> rw [hfa] at hlt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
        omega
    · have : 2 ≤ i ∧ i ≤ n - 1 := hv
      cases hfb : f .b i <;> rw [hfb] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hgt <;>
        omega
    · have hi2 : 2 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      by_cases himu : i = mu n b
      · subst himu
        have hfc : f .c (mu n b) = true := by dsimp [f, oddBlock3Fun]; simp
        rw [hfc] at hgt
        simp only [Bool.not_true, columnRank_c_false] at hgt
        omega
      · have hfc : f .c i = false := by dsimp [f, oddBlock3Fun]; exact decide_eq_false himu
        rw [hfc] at hgt
        simp only [Bool.not_false, columnRank_c_true] at hgt
        have higt : mu n b < i := by omega
        have hfe : f .e i = true := by dsimp [f, oddBlock3Fun]; rw [if_neg (by omega)]
        rw [mdpStrictNonImproving_c_iff, hfc, if_neg (by decide), hcp i higt hin]
        cases hbi : b.testBit (i - 1)
        · have hfd : f .d i = false := by dsimp [f, oddBlock3Fun]; rw [if_pos higt, hbi]
          have hFG := FRhs_GRhs_of_de_false_true_Gm (b' := b) (b := b) (m := mu n b) (i := i)
            hn f hi2 hin (by omega) hmun hfd hfe (hva (i + 1) (by omega) (Or.inl (by omega)))
            (hbp i higt hin)
          linarith [hFG.2.2.2]
        · have hfd : f .d i = true := by dsimp [f, oddBlock3Fun]; rw [if_pos higt, hbi]
          rw [GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega) (Or.inl (by omega)))]
          have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (by omega : 1 ≤ mu n b) higt hin hbi
          linarith
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfd : f .d i <;> rw [hfd] at hgt hlt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hgt hlt <;>
        omega
    · have : 1 ≤ i ∧ i ≤ n := hv
      cases hfe : f .e i <;> rw [hfe] at hgt hlt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hgt hlt
      · split_ifs at hgt <;> omega
      · omega
  have hup : ∀ kind i, ValidRow n (kind, i) →
      (if kind = .e ∧ i = 1 then !f .e 1 else f kind i) = oddBlock3Fun n b 2 kind i := by
    intro kind i hv
    by_cases h : kind = .e ∧ i = 1
    · rcases h with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩, hf₀]
      dsimp [oddBlock3Fun]
      symm; exact hsucc_lt 1 (le_refl 1) hmu2
    · rw [if_neg h]
      cases kind <;> dsimp [f, oddBlock3Fun]
      have hi : i ≠ 1 := fun heq => h ⟨rfl, heq⟩
      have hi1 : 1 ≤ i := hv.1
      rw [if_neg (by omega), if_neg (by omega)]
  rcases step_stateAt_of_le hn hs .e 1 hv₀ (by rw [hrank]; omega) himp hno hup with
    ⟨s', hp, hs'⟩
  rw [hrank] at hs'
  exact ⟨s', hp, hs'⟩

lemma odd_block3_step {n b k m : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hk2 : 2 ≤ k) (hkn : k ≤ n)
    {s : MDPState n} (hs : StateAt n (oddBlock3Fun n b k) m s)
    (hm1 : 6 * n - 7 ≤ m) (hm2 : m + 1 ≤ 6 * n - 7 + (k - 1)) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      6 * n - 7 ≤ m' ∧ m' + 1 ≤ 6 * n - 7 + k ∧
      StateAt n (oddBlock3Fun n b (k + 1)) m' s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨hsucc_lt, hsucc_eq, hsucc_gt, _⟩
  cases hbk : (b + 1).testBit (k - 1)
  · rcases oddBlock3_vals (k := k) hn hodd hb (by omega) (by omega) with ⟨hva, hbp, _, hcn⟩
    set f := oddBlock3Fun n b k
    set V := policyValue n hn (policyOf n f)
    have hv₀ : ValidRow n (.e, k) := ⟨by omega, hkn⟩
    have hf₀ : f .e k = true := by dsimp [f, oddBlock3Fun]; rw [if_neg (by omega)]
    have hrank : columnRank n ⟨.e, k, !f .e k⟩ = 6 * n - 7 + (k - 1) := by
      rw [hf₀, Bool.not_true, columnRank_e_false]
    have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.e, k) hv₀) := by
      rw [mdpImproving_e_iff hn f hv₀ hk2, hf₀, if_pos rfl, hcn]
      have hk_ne_mu : k ≠ mu n b := by
        intro heq; subst heq; rw [hsucc_eq] at hbk; contradiction
      rcases lt_or_gt_of_ne hk_ne_mu with hklt | hkgt
      · have hfd : f .d k = true := by dsimp [f, oddBlock3Fun]; rw [if_neg (by omega)]
        rw [FRhs_eq_HVal_of_de_true_true hn f hk2 hkn hfd hf₀ (hva (k + 1) (by omega) (Or.inl (by omega)))]
        have := HVal_lt_Gm_of_lt (b := b) hn (by omega : 1 ≤ k) hklt hmun hmubit
        linarith
      · have hbi : b.testBit (k - 1) = false := by
          rw [← hsucc_gt k hkgt]; exact hbk
        have hfd : f .d k = false := by dsimp [f, oddBlock3Fun]; rw [if_pos hkgt, hbi]
        have hFG := FRhs_GRhs_of_de_false_true_Gm (b' := b) (b := b) (m := mu n b) (i := k)
          hn f hk2 hkn (by omega) hmun hfd hf₀ (hva (k + 1) (by omega) (Or.inl (by omega)))
          (hbp k hkgt hkn)
        have hF_up := (abs_lt.mp hFG.1).2
        linarith
    have hno : ∀ kind i (hv : ValidRow n (kind, i)),
        m < columnRank n ⟨kind, i, !f kind i⟩ →
        columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.e, k, !f .e k⟩ →
        mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
      intro kind i hv hgt hlt
      rw [hrank] at hlt
      cases kind
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfa : f .a i <;> rw [hfa] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n - 1 := hv
        cases hfb : f .b i <;> rw [hfb] at hgt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hgt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfc : f .c i <;> rw [hfc] at hgt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hgt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfd : f .d i <;> rw [hfd] at hgt hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hgt hlt <;>
          omega
      · have hi1 : 1 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        cases hfe : f .e i
        · rw [hfe] at hgt
          simp only [Bool.not_false, columnRank_e_true] at hgt
          split_ifs at hgt <;> omega
        · rw [hfe] at hgt hlt
          simp only [Bool.not_true, columnRank_e_false] at hgt hlt
          have hi2 : 2 ≤ i := by omega
          have hilt : i < k := by omega
          have hsucc_i : (b + 1).testBit (i - 1) = true := by
            dsimp [f, oddBlock3Fun] at hfe
            rw [if_pos hilt] at hfe
            exact hfe
          have himu : mu n b ≤ i := by
            by_contra hlt_mu
            have := hsucc_lt i hi1 (by omega)
            rw [this] at hsucc_i; contradiction
          have hfd : f .d i = true := by
            dsimp [f, oddBlock3Fun]
            split_ifs with h1
            · rw [← hsucc_gt i h1]; exact hsucc_i
            · rfl
          rw [mdpStrictNonImproving_e_iff hn f hv hi2, hfe, if_pos rfl, hcn,
            FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega) (Or.inr (by omega)))]
          have := HVal_gt_Gm (b := b) hn (by omega : 1 ≤ mu n b) himu hin
          linarith
    have hup : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .e ∧ i = k then !f .e k else f kind i) = oddBlock3Fun n b (k + 1) kind i := by
      intro kind i _
      by_cases h : kind = .e ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hf₀]
        dsimp [oddBlock3Fun]; rw [if_pos (by omega), hbk]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [f, oddBlock3Fun]
        have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
        by_cases h1 : i < k
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs .e k hv₀ (by rw [hrank]; omega) himp hno hup with
      ⟨s', hp, hs'⟩
    rw [hrank] at hs'
    exact ⟨1, s', 6 * n - 7 + (k - 1), hp, by omega, by omega, hs'⟩
  · have hfeq : oddBlock3Fun n b (k + 1) = oddBlock3Fun n b k := by
      funext kind i
      cases kind <;> dsimp [oddBlock3Fun]
      by_cases hi : i = k
      · subst hi; rw [if_pos (by omega), if_neg (by omega), hbk]
      · by_cases h1 : i < k
        · rw [if_pos (by omega), if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
    refine ⟨0, s, m, MdpPath.refl s, hm1, by omega, ?_⟩
    rw [hfeq]; exact hs

lemma odd_block3_loop {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1) :
    ∀ k, 2 ≤ k → k ≤ n + 1 →
      ∀ {s m}, StateAt n (oddBlock3Fun n b k) m s →
        6 * n - 7 ≤ m → m + 1 ≤ 6 * n - 7 + (k - 1) →
        ∃ t s' m', MdpPath n hn t s s' ∧
          6 * n - 7 ≤ m' ∧ m' < 7 * n - 7 ∧
          StateAt n (oddBlock3Fun n b (n + 1)) m' s' := by
  intro k hk2 hkn
  induction h : n + 1 - k generalizing k with
  | zero =>
    have hk : k = n + 1 := by omega
    subst hk
    intro s m hs hm1 hm2
    exact ⟨0, s, m, MdpPath.refl s, hm1, by omega, hs⟩
  | succ d ih =>
    intro s m hs hm1 hm2
    have hkn' : k ≤ n := by omega
    rcases odd_block3_step hn hodd hb hk2 hkn' hs hm1 hm2 with
      ⟨t₁, s₁, m₁, hp₁, hm₁1, hm₁2, hs₁⟩
    rcases ih (k + 1) (by omega) (by omega) (by omega) hs₁ hm₁1 hm₁2 with
      ⟨t₂, s₂, m₂, hp₂, hm₂1, hm₂2, hs₂⟩
    exact ⟨t₁ + t₂, s₂, m₂, hp₁.trans hp₂, hm₂1, hm₂2, hs₂⟩

def oddBlock4Fun (n b k : ℕ) (kind : Kind) (i : ℕ) : Bool :=
  match kind with
  | .a => b.testBit (i - 1)
  | .b => decide (i = mu n b)
  | .c => decide (i = mu n b)
  | .d => if mu n b < i ∧ k ≤ i then b.testBit (i - 1) else true
  | .e => (b + 1).testBit (i - 1)

lemma oddBlock4_vals {n b k : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (_hk1 : mu n b + 1 ≤ k) (_hkn : k ≤ n + 1) :
    let f := oddBlock4Fun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, mu n b ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    (∀ i, mu n b < i → i ≤ n → BPrev n hn V i = Gm n b (mu n b)) ∧
    valAt n hn V .c n = Gm n b (mu n b) := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨_, hsucc_eq, hsucc_gt, _⟩
  intro f V
  have hva : ∀ i, mu n b ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i himu
    exact valAt_a_eq_vaBase hn f b i (by omega) (fun _ _ _ => rfl)
      (fun j hij _ hbj => by
        dsimp [f, oddBlock4Fun]
        have hjmu : mu n b < j := by
          have : mu n b ≤ j := by omega
          rcases eq_or_lt_of_le this with rfl | hlt
          · rw [hmubit] at hbj; contradiction
          · exact hlt
        exact ⟨by split_ifs <;> first | rfl | exact hbj,
          by rw [hsucc_gt j hjmu, hbj]⟩)
  have hbm : f .b (mu n b) = true := by dsimp [f, oddBlock4Fun]; simp
  have hcm : f .c (mu n b) = true := by dsimp [f, oddBlock4Fun]; simp
  have hdm : f .d (mu n b) = true := by dsimp [f, oddBlock4Fun]; rw [if_neg (by omega)]
  have hem : f .e (mu n b) = true := hsucc_eq
  have hbp : ∀ i, mu n b < i → i ≤ n → BPrev n hn V i = Gm n b (mu n b) := by
    intro i higt hin
    rw [BPrev_eq_Gm hn f hmu2 hbm hdm hem i higt hin
      (fun j hj1 _ => by dsimp [f, oddBlock4Fun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega)]
    rfl
  have hcn : valAt n hn V .c n = Gm n b (mu n b) := by
    rw [valAt_c_n_eq_Gm hn f hmu2 hmun hcm hdm hem
      (fun j hj1 _ => by dsimp [f, oddBlock4Fun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega)]
    rfl
  exact ⟨hva, hbp, hcn⟩

lemma odd_block4_step {n b k m : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hk1 : mu n b + 1 ≤ k) (hkn : k ≤ n)
    {s : MDPState n} (hs : StateAt n (oddBlock4Fun n b k) m s)
    (hm1 : 6 * n - 7 ≤ m) (hm2 : m + 1 ≤ 7 * n - 7 + (k - 2)) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      6 * n - 7 ≤ m' ∧ m' + 1 ≤ 7 * n - 7 + (k + 1 - 2) ∧
      StateAt n (oddBlock4Fun n b (k + 1)) m' s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨hsucc_lt, hsucc_eq, hsucc_gt, _⟩
  cases hbk : b.testBit (k - 1)
  · rcases oddBlock4_vals hn hodd hb hk1 (by omega) with ⟨hva, hbp, hcn⟩
    set f := oddBlock4Fun n b k
    set V := policyValue n hn (policyOf n f)
    have hv₀ : ValidRow n (.d, k) := ⟨by omega, hkn⟩
    have hfd : f .d k = false := by
      dsimp [f, oddBlock4Fun]; rw [if_pos ⟨by omega, le_refl _⟩, hbk]
    have hfe : f .e k = false := by
      dsimp [f, oddBlock4Fun]; rw [hsucc_gt k (by omega), hbk]
    have hrank : columnRank n ⟨.d, k, !f .d k⟩ = 7 * n - 7 + (k - 2) := by
      rw [hfd, Bool.not_false, columnRank_d_true]
    have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.d, k) hv₀) := by
      rw [mdpImproving_d_iff hn f hv₀, hfd, if_neg (by decide), hbp k (by omega) hkn]
      have hH := HVal_gt_Gm (b := b) hn (by omega : 1 ≤ mu n b) (by omega : mu n b ≤ k) hkn
      have hFG := FRhs_GRhs_of_de_false_false_same_Gm (b' := b) (b := b) (m := mu n b) (i := k)
        hn f (by omega) hkn (by omega) hmun hfd hfe (hva (k + 1) (by omega))
        (hbp k (by omega) hkn) hcn (by linarith)
      exact hFG.1
    have hno : ∀ kind i (hv : ValidRow n (kind, i)),
        m < columnRank n ⟨kind, i, !f kind i⟩ →
        columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.d, k, !f .d k⟩ →
        mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
      intro kind i hv hgt hlt
      rw [hrank] at hlt
      cases kind
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfa : f .a i <;> rw [hfa] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n - 1 := hv
        cases hfb : f .b i <;> rw [hfb] at hgt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hgt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfc : f .c i <;> rw [hfc] at hgt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hgt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfdi : f .d i
        · rw [hfdi] at hlt
          simp only [Bool.not_false, columnRank_d_true] at hlt
          have hilt : i < k := by omega
          dsimp [f, oddBlock4Fun] at hfdi
          rw [if_neg (by omega)] at hfdi
          contradiction
        · rw [hfdi] at hgt
          simp only [Bool.not_true, columnRank_d_false] at hgt
          omega
      · have hi1 : 1 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        cases hfei : f .e i
        · rw [hfei] at hgt
          simp only [Bool.not_false, columnRank_e_true] at hgt
          split_ifs at hgt <;> omega
        · rw [hfei] at hgt
          simp only [Bool.not_true, columnRank_e_false] at hgt
          have hi2 : 2 ≤ i := by omega
          have hsucc_i : (b + 1).testBit (i - 1) = true := hfei
          have himu : mu n b ≤ i := by
            by_contra hlt_mu
            have := hsucc_lt i hi1 (by omega)
            rw [this] at hsucc_i; contradiction
          have hfdi : f .d i = true := by
            dsimp [f, oddBlock4Fun]
            split_ifs with h1
            · rw [← hsucc_gt i h1.1]; exact hsucc_i
            · rfl
          rw [mdpStrictNonImproving_e_iff hn f hv hi2, hfei, if_pos rfl, hcn,
            FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfdi hfei (hva (i + 1) (by omega))]
          have := HVal_gt_Gm (b := b) hn (by omega : 1 ≤ mu n b) himu hin
          linarith
    have hup : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .d ∧ i = k then !f .d k else f kind i) = oddBlock4Fun n b (k + 1) kind i := by
      intro kind i _
      by_cases h : kind = .d ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hfd]
        dsimp [oddBlock4Fun]; rw [if_neg (by omega)]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [f, oddBlock4Fun]
        have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
        by_cases h1 : mu n b < i ∧ k ≤ i
        · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs .d k hv₀ (by rw [hrank]; omega) himp hno hup with
      ⟨s', hp, hs'⟩
    rw [hrank] at hs'
    exact ⟨1, s', 7 * n - 7 + (k - 2), hp, by omega, by omega, hs'⟩
  · have hfeq : oddBlock4Fun n b (k + 1) = oddBlock4Fun n b k := by
      funext kind i
      cases kind <;> dsimp [oddBlock4Fun]
      by_cases hi : i = k
      · subst hi; rw [if_neg (by omega), if_pos ⟨by omega, le_refl _⟩, hbk]
      · by_cases h1 : mu n b < i ∧ k ≤ i
        · rw [if_pos ⟨h1.1, by omega⟩, if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
    refine ⟨0, s, m, MdpPath.refl s, hm1, by omega, ?_⟩
    rw [hfeq]; exact hs

lemma odd_block4_loop {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1) :
    ∀ k, mu n b + 1 ≤ k → k ≤ n + 1 →
      ∀ {s m}, StateAt n (oddBlock4Fun n b k) m s →
        6 * n - 7 ≤ m → m + 1 ≤ 7 * n - 7 + (k - 2) →
        ∃ t s' m', MdpPath n hn t s s' ∧
          6 * n - 7 ≤ m' ∧ m' < 8 * n - 8 ∧
          StateAt n (oddBlock4Fun n b (n + 1)) m' s' := by
  intro k hk1 hkn
  induction h : n + 1 - k generalizing k with
  | zero =>
    have hk : k = n + 1 := by omega
    subst hk
    intro s m hs hm1 hm2
    exact ⟨0, s, m, MdpPath.refl s, hm1, by omega, hs⟩
  | succ d ih =>
    intro s m hs hm1 hm2
    have hkn' : k ≤ n := by omega
    rcases odd_block4_step hn hodd hb hk1 hkn' hs hm1 hm2 with
      ⟨t₁, s₁, m₁, hp₁, hm₁1, hm₁2, hs₁⟩
    rcases ih (k + 1) (by omega) (by omega) (by omega) hs₁ hm₁1 hm₁2 with
      ⟨t₂, s₂, m₂, hp₂, hm₂1, hm₂2, hs₂⟩
    exact ⟨t₁ + t₂, s₂, m₂, hp₁.trans hp₂, hm₂1, hm₂2, hs₂⟩

def oddBlock5Fun (n b k : ℕ) (kind : Kind) (i : ℕ) : Bool :=
  match kind with
  | .a => if k < i then (b + 1).testBit (i - 1) else true
  | .b => decide (i = mu n b)
  | .c => decide (i = mu n b)
  | .d => true
  | .e => (b + 1).testBit (i - 1)

lemma odd_block5_first {n b m : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    {s : MDPState n} (hs : StateAt n (oddBlock4Fun n b (n + 1)) m s)
    (hm1 : 6 * n - 7 ≤ m) (hm2 : m < 8 * n - 8) :
    ∃ s' : MDPState n, MdpPath n hn 1 s s' ∧
      StateAt n (oddBlock5Fun n b (mu n b - 1)) (8 * n - 8 + 2 * (n - mu n b)) s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, hmumin⟩
  rcases odd_succ_bits hn hodd hb with ⟨hsucc_lt, hsucc_eq, hsucc_gt, _⟩
  rcases oddBlock4_vals (k := n + 1) hn hodd hb (by omega) (le_refl _) with ⟨hva, _, hcn⟩
  set f := oddBlock4Fun n b (n + 1)
  set V := policyValue n hn (policyOf n f)
  have hv₀ : ValidRow n (.a, mu n b) := ⟨hmu2, hmun⟩
  have hf₀ : f .a (mu n b) = false := hmubit
  have hrank : columnRank n ⟨.a, mu n b, !f .a (mu n b)⟩ = 8 * n - 8 + 2 * (n - mu n b) := by
    rw [hf₀, Bool.not_false, columnRank_a_true]
  have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.a, mu n b) hv₀) := by
    have hfd : f .d (mu n b) = true := by dsimp [f, oddBlock4Fun]; rw [if_neg (by omega)]
    have hfe : f .e (mu n b) = true := hsucc_eq
    rw [mdpImproving_a_iff hn f hv₀, hf₀, if_neg (by decide), hva (mu n b + 1) (by omega),
      GRhs_eq_Gm_of_de_true_true hn f hmu2 hmun hfd hfe (hva (mu n b + 1) (by omega))]
    unfold Gm
    have := rewardGH_ge_42 (n := n) hn (by omega : 1 ≤ mu n b)
    linarith
  have hno : ∀ kind i (hv : ValidRow n (kind, i)),
      m < columnRank n ⟨kind, i, !f kind i⟩ →
      columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.a, mu n b, !f .a (mu n b)⟩ →
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
    intro kind i hv hgt hlt
    rw [hrank] at hlt
    cases kind
    · have hi2 : 2 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      have higt : mu n b < i := by
        cases hfa : f .a i <;> rw [hfa] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
          omega
      have hfd : f .d i = true := by dsimp [f, oddBlock4Fun]; rw [if_neg (by omega)]
      rw [mdpStrictNonImproving_a_iff hn f hv, hva (i + 1) (by omega)]
      change if b.testBit (i - 1) = true then vaBase n b (i + 1) < GRhs n hn V i
        else GRhs n hn V i < vaBase n b (i + 1)
      cases hbi : b.testBit (i - 1)
      · rw [if_neg (by decide)]
        have hfe : f .e i = false := by
          dsimp [f, oddBlock4Fun]; rw [hsucc_gt i higt, hbi]
        have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b) (b := b) (m := mu n b) (i := i)
          hn f hi2 hin (by omega) hmun hfd hfe (hva (i + 1) (by omega)) hcn
        have hF_up := (abs_lt.mp hFG.1).2
        have hrg := rewardG_add_Gm_lt_vaBase (b := b) hn (by omega : 1 ≤ mu n b) higt hin hbi
        unfold GRhs
        linarith
      · rw [if_pos rfl]
        have hfe : f .e i = true := by
          dsimp [f, oddBlock4Fun]; rw [hsucc_gt i higt, hbi]
        rw [GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
        unfold Gm
        have := rewardGH_ge_42 (n := n) hn (by omega : 1 ≤ i)
        linarith
    · have : 2 ≤ i ∧ i ≤ n - 1 := hv
      cases hfb : f .b i <;> rw [hfb] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hgt <;>
        omega
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfc : f .c i <;> rw [hfc] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hgt <;>
        omega
    · have : 2 ≤ i ∧ i ≤ n := hv
      have hfdi : f .d i = true := by dsimp [f, oddBlock4Fun]; rw [if_neg (by omega)]
      rw [hfdi] at hgt
      simp only [Bool.not_true, columnRank_d_false] at hgt
      omega
    · have hi1 : 1 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      cases hfei : f .e i
      · rw [hfei] at hgt
        simp only [Bool.not_false, columnRank_e_true] at hgt
        split_ifs at hgt <;> omega
      · rw [hfei] at hgt
        simp only [Bool.not_true, columnRank_e_false] at hgt
        have hi2 : 2 ≤ i := by omega
        have hsucc_i : (b + 1).testBit (i - 1) = true := hfei
        have himu : mu n b ≤ i := by
          by_contra hlt_mu
          have := hsucc_lt i hi1 (by omega)
          rw [this] at hsucc_i; contradiction
        have hfdi : f .d i = true := by dsimp [f, oddBlock4Fun]; rw [if_neg (by omega)]
        rw [mdpStrictNonImproving_e_iff hn f hv hi2, hfei, if_pos rfl, hcn,
          FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfdi hfei (hva (i + 1) (by omega))]
        have := HVal_gt_Gm (b := b) hn (by omega : 1 ≤ mu n b) himu hin
        linarith
  have hup : ∀ kind i, ValidRow n (kind, i) →
      (if kind = .a ∧ i = mu n b then !f .a (mu n b) else f kind i) =
        oddBlock5Fun n b (mu n b - 1) kind i := by
    intro kind i hv
    by_cases h : kind = .a ∧ i = mu n b
    · rcases h with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩, hf₀]
      dsimp [oddBlock5Fun]; rw [if_pos (by omega), hsucc_eq]; rfl
    · rw [if_neg h]
      cases kind <;> dsimp [f, oddBlock4Fun, oddBlock5Fun, ValidRow] at hv ⊢
      · have hi : i ≠ mu n b := fun heq => h ⟨rfl, heq⟩
        rcases lt_or_gt_of_ne hi with hilt | higt
        · rw [if_neg (by omega)]; exact hmumin i (by omega) hilt
        · rw [if_pos (by omega), hsucc_gt i higt]
      · rw [if_neg (by omega)]
  rcases step_stateAt_of_le hn hs .a (mu n b) hv₀ (by rw [hrank]; omega) himp hno hup with
    ⟨s', hp, hs'⟩
  rw [hrank] at hs'
  exact ⟨s', hp, hs'⟩

lemma oddBlock5_vals {n b k : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (_hk1 : 1 ≤ k) (_hkn : k ≤ mu n b - 1) :
    let f := oddBlock5Fun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, k + 1 ≤ i → valAt n hn V .a i = vaBase n (b + 1) i) ∧
    valAt n hn V .c n = Gm n b (mu n b) := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, _, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨_, hsucc_eq, _, _⟩
  intro f V
  have hva : ∀ i, k + 1 ≤ i → valAt n hn V .a i = vaBase n (b + 1) i := by
    intro i hik
    exact valAt_a_eq_vaBase hn f (b + 1) i (by omega)
      (fun j hij _ => by dsimp [f, oddBlock5Fun]; rw [if_pos (by omega)])
      (fun j _ _ hbj => ⟨rfl, hbj⟩)
  have hcm : f .c (mu n b) = true := by dsimp [f, oddBlock5Fun]; simp
  have hem : f .e (mu n b) = true := hsucc_eq
  have hcn : valAt n hn V .c n = Gm n b (mu n b) := by
    rw [valAt_c_n_eq_Gm hn f hmu2 hmun hcm rfl hem
      (fun j hj1 _ => by dsimp [f, oddBlock5Fun]; exact decide_eq_false (by omega)),
      hva (mu n b + 1) (by omega), vaBase_odd_succ_gt hn hodd hb (by omega)]
    rfl
  exact ⟨hva, hcn⟩

lemma odd_block5_step {n b k m : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    (hk1 : 1 ≤ k) (hkm : k + 1 < mu n b)
    {s : MDPState n} (hs : StateAt n (oddBlock5Fun n b (k + 1)) m s)
    (hm1 : 8 * n - 8 + 2 * (n - (k + 2)) ≤ m)
    (hm2 : m + 1 ≤ 8 * n - 8 + 2 * (n - (k + 1))) :
    ∃ s' : MDPState n, MdpPath n hn 1 s s' ∧
      StateAt n (oddBlock5Fun n b k) (8 * n - 8 + 2 * (n - (k + 1)) + 1) s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, _, _⟩
  rcases odd_succ_bits hn hodd hb with ⟨hsucc_lt, hsucc_eq, _, _⟩
  rcases oddBlock5_vals (k := k + 1) hn hodd hb (by omega) (by omega) with ⟨hva, hcn⟩
  set f := oddBlock5Fun n b (k + 1)
  set V := policyValue n hn (policyOf n f)
  have hv₀ : ValidRow n (.a, k + 1) := ⟨by omega, by omega⟩
  have hf₀ : f .a (k + 1) = true := by dsimp [f, oddBlock5Fun]; rw [if_neg (by omega)]
  have hfe : f .e (k + 1) = false := hsucc_lt (k + 1) (by omega) hkm
  have hrank : columnRank n ⟨.a, k + 1, !f .a (k + 1)⟩ = 8 * n - 8 + 2 * (n - (k + 1)) + 1 := by
    rw [hf₀, Bool.not_true, columnRank_a_false]
  have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.a, k + 1) hv₀) := by
    have hva_k2 : valAt n hn V .a (k + 2) = Gm n b (mu n b) := by
      rw [hva (k + 2) (le_refl _), vaBase_odd_succ_le hn hodd hb (by omega) (by omega)]
      rfl
    rw [mdpImproving_a_iff hn f hv₀, hf₀, if_pos rfl, hva_k2]
    have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b + 1) (b := b) (m := mu n b) (i := k + 1)
      hn f (by omega) (by omega) (by omega) hmun rfl hfe (hva (k + 2) (le_refl _)) hcn
    linarith [hFG.2.2.2]
  have hno : ∀ kind i (hv : ValidRow n (kind, i)),
      m < columnRank n ⟨kind, i, !f kind i⟩ →
      columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.a, k + 1, !f .a (k + 1)⟩ →
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
    intro kind i hv hgt hlt
    rw [hrank] at hlt
    cases kind
    · have hi2 : 2 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      have himu : i = mu n b := by
        rcases lt_trichotomy i (mu n b) with hilt | rfl | higt
        · rcases lt_or_ge i (k + 2) with hik | hik
          · rcases eq_or_lt_of_le (by omega : i ≤ k + 1) with rfl | hlt_k1
            · rw [hf₀, Bool.not_true, columnRank_a_false] at hlt; omega
            · cases hfa : f .a i <;> rw [hfa] at hlt <;>
                simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
                omega
          · have hfa : f .a i = false := by
              dsimp [f, oddBlock5Fun]; rw [if_pos (by omega)]; exact hsucc_lt i (by omega) hilt
            rw [hfa] at hgt
            simp only [Bool.not_false, columnRank_a_true] at hgt
            omega
        · rfl
        · cases hfa : f .a i <;> rw [hfa] at hgt <;>
            simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hgt <;>
            omega
      subst himu
      have hfa : f .a (mu n b) = true := by
        dsimp [f, oddBlock5Fun]; rw [if_pos hkm, hsucc_eq]
      have hfe_mu : f .e (mu n b) = true := hsucc_eq
      rw [mdpStrictNonImproving_a_iff hn f hv, hfa, if_pos rfl, hva (mu n b + 1) (by omega),
        GRhs_eq_Gm_of_de_true_true hn f hmu2 hmun rfl hfe_mu (hva (mu n b + 1) (by omega))]
      unfold Gm
      have := rewardGH_ge_42 (n := n) hn (by omega : 1 ≤ mu n b)
      linarith
    · have : 2 ≤ i ∧ i ≤ n - 1 := hv
      cases hfb : f .b i <;> rw [hfb] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hgt <;>
        omega
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfc : f .c i <;> rw [hfc] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hgt <;>
        omega
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfd : f .d i <;> rw [hfd] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hgt <;>
        omega
    · have : 1 ≤ i ∧ i ≤ n := hv
      cases hfei : f .e i <;> rw [hfei] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hgt
      · split_ifs at hgt <;> omega
      · omega
  have hup : ∀ kind i, ValidRow n (kind, i) →
      (if kind = .a ∧ i = k + 1 then !f .a (k + 1) else f kind i) = oddBlock5Fun n b k kind i := by
    intro kind i _
    by_cases h : kind = .a ∧ i = k + 1
    · rcases h with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩, hf₀]
      dsimp [oddBlock5Fun]; rw [if_pos (by omega)]
      symm; exact hfe
    · rw [if_neg h]
      cases kind <;> dsimp [f, oddBlock5Fun]
      have hi : i ≠ k + 1 := fun heq => h ⟨rfl, heq⟩
      by_cases h1 : k + 1 < i
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  rcases step_stateAt_of_le hn hs .a (k + 1) hv₀ (by rw [hrank]; omega) himp hno hup with
    ⟨s', hp, hs'⟩
  rw [hrank] at hs'
  exact ⟨s', hp, hs'⟩

lemma odd_block5_loop {n b : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1) :
    ∀ d, d ≤ mu n b - 2 →
      ∀ {s m}, StateAt n (oddBlock5Fun n b (d + 1)) m s →
        8 * n - 8 + 2 * (n - (d + 2)) ≤ m →
        m + 1 ≤ 8 * n - 8 + 2 * (n - (d + 1)) →
        ∃ t s' m', MdpPath n hn t s s' ∧
          10 * n - 12 ≤ m' ∧ m' < 10 * n - 10 ∧
          StateAt n (oddBlock5Fun n b 1) m' s' := by
  intro d hd
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, _, _⟩
  induction d with
  | zero =>
    intro s m hs hm1 hm2
    exact ⟨0, s, m, MdpPath.refl s, by omega, by omega, hs⟩
  | succ d ih =>
    intro s m hs hm1 hm2
    rcases odd_block5_step hn hodd hb (by omega) (by omega) hs hm1 hm2 with ⟨s₁, hp₁, hs₁⟩
    rcases ih (by omega) hs₁ (by omega) (by omega) with ⟨t₂, s₂, m₂, hp₂, hm₂1, hm₂2, hs₂⟩
    exact ⟨1 + t₂, s₂, m₂, hp₁.trans hp₂, hm₂1, hm₂2, hs₂⟩

lemma odd_sweep {n b m₀ : ℕ} (hn : 3 ≤ n) (hodd : b % 2 = 1) (hb : b < 2 ^ n - 1)
    {s₀ : MDPState n} (hs₀ : StateAt n (counterFun n b) m₀ s₀)
    (hm₀ : m₀ = 0 ∨ (7 * n - 7 ≤ m₀ ∧ m₀ < 8 * n - 8)) :
    ∃ t s' m', 4 ≤ t ∧ MdpPath n hn t s₀ s' ∧
      10 * n - 12 ≤ m' ∧ m' < 10 * n - 10 ∧
      StateAt n (counterFun n (b + 1)) m' s' := by
  rcases mu_spec hn hodd hb with ⟨hmu2, hmun, hmubit, hmumin⟩
  rcases odd_succ_bits hn hodd hb with ⟨hsucc_lt, hsucc_eq, hsucc_gt, hnu_succ⟩
  rcases odd_step_e_mu hn hodd hb hs₀ hm₀ with ⟨s₁, hp₁, hs₁⟩
  rcases odd_step_b_mu hn hodd hb hs₁ with ⟨t₂, s₂, m₂, hp₂, hm₂1, hm₂2, hm₂3, hs₂⟩
  rcases odd_block1_loop hn hodd hb (mu n b + 1) (le_refl _) (by omega) hs₂ hm₂1 (by omega) hm₂3
    with ⟨t₃, s₃, m₃, hp₃, hm₃1, hm₃3, hs₃⟩
  rcases odd_block2_step hn hodd hb hs₃ hm₃1 hm₃3 with ⟨s₄, hp₄, hs₄⟩
  rcases odd_block3_step1 hn hodd hb hs₄ with ⟨s₅, hp₅, hs₅⟩
  rcases odd_block3_loop hn hodd hb 2 (le_refl 2) (by omega) hs₅ (le_refl _) (by omega)
    with ⟨t₆, s₆, m₆, hp₆, hm₆1, hm₆2, hs₆⟩
  have hs₆' : StateAt n (oddBlock4Fun n b (mu n b + 1)) m₆ s₆ := by
    have hpol : policyOf n (oddBlock3Fun n b (n + 1)) = policyOf n (oddBlock4Fun n b (mu n b + 1)) := by
      apply policyOf_ext hn
      intro k i hv
      cases k <;> dsimp [oddBlock3Fun, oddBlock4Fun, ValidRow] at hv ⊢
      · by_cases h1 : mu n b < i
        · rw [if_pos h1, if_pos ⟨h1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
      · rw [if_pos (by omega)]
    rcases hs₆ with ⟨hspol, hslast, k₀, i₀, hv₀, hrank₀⟩
    refine ⟨by rw [hspol, hpol], hslast, k₀, i₀, hv₀, ?_⟩
    rw [hrank₀]
    congr 2
    cases k₀ <;> dsimp [oddBlock3Fun, oddBlock4Fun, ValidRow] at hv₀ ⊢
    · by_cases h1 : mu n b < i₀
      · rw [if_pos h1, if_pos ⟨h1, by omega⟩]
      · rw [if_neg h1, if_neg (by omega)]
    · rw [if_pos (by omega)]
  rcases odd_block4_loop hn hodd hb (mu n b + 1) (le_refl _) (by omega) hs₆' hm₆1 (by omega)
    with ⟨t₇, s₇, m₇, hp₇, hm₇1, hm₇2, hs₇⟩
  rcases odd_block5_first hn hodd hb hs₇ hm₇1 hm₇2 with ⟨s₈, hp₈, hs₈⟩
  have h8 : mu n b - 1 = (mu n b - 2) + 1 := by omega
  rw [h8] at hs₈
  rcases odd_block5_loop hn hodd hb (mu n b - 2) (le_refl _) hs₈ (by omega) (by omega)
    with ⟨t₉, s₉, m₉, hp₉, hm₉1, hm₉2, hs₉⟩
  have hsucc0 : (b + 1).testBit 0 = false := hsucc_lt 1 (le_refl 1) hmu2
  have hfeq : ∀ k i, ValidRow n (k, i) → oddBlock5Fun n b 1 k i = counterFun n (b + 1) k i := by
    intro k i hv
    cases k <;> unfold oddBlock5Fun counterFun <;> dsimp [ValidRow] at hv ⊢
    · rw [if_pos (by omega)]
    · rw [if_neg (by rw [hsucc0]; decide), hnu_succ]
    · rw [if_neg (by rw [hsucc0]; decide), hnu_succ]
  rcases hs₉ with ⟨hspol₉, hslast₉, k₉, i₉, hv₉, hrank₉⟩
  have hs₉' : StateAt n (counterFun n (b + 1)) m₉ s₉ := by
    refine ⟨?_, hslast₉, k₉, i₉, hv₉, ?_⟩
    · rw [hspol₉]; exact policyOf_ext hn hfeq
    · rw [hrank₉, hfeq k₉ i₉ hv₉]
  refine ⟨1 + t₂ + t₃ + 1 + 1 + t₆ + t₇ + 1 + t₉, s₉, m₉, by omega, ?_, hm₉1, hm₉2, hs₉'⟩
  exact (((((((hp₁.trans hp₂).trans hp₃).trans hp₄).trans hp₅).trans hp₆).trans hp₇).trans hp₈).trans hp₉

/-! ### Part 6: Even Sweep (`b % 2 = 0`, `0 < b ≤ 2 ^ n - 2`) -/

def evenBlock1Fun (n b k : ℕ) : Kind → ℕ → Bool
  | .a, i => b.testBit (i - 1)
  | .b, i => decide (i = nu n b ∧ i < n ∧ k ≤ i)
  | .c, i => decide (i = nu n b)
  | .d, i => if 2 ≤ i ∧ i < k then b.testBit (i - 1) else true
  | .e, i => if i < k then true else b.testBit (i - 1)

def evenBlock1MidFun (n b k : ℕ) : Kind → ℕ → Bool
  | .a, i => b.testBit (i - 1)
  | .b, i => decide (i = nu n b ∧ i < n ∧ k ≤ i)
  | .c, i => decide (i = nu n b)
  | .d, i => if 2 ≤ i ∧ i ≤ k then b.testBit (i - 1) else true
  | .e, i => if i < k then true else b.testBit (i - 1)

lemma counterFun_even_vals {n b : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) :
    let f := counterFun n b
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    valAt n hn V .c n = Gm n b (nu n b) := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, _⟩
  have hb0 : b.testBit 0 = false := by
    rw [Nat.testBit_zero]; exact decide_eq_false (by omega)
  intro f V
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j _ _ hbj => ⟨rfl, hbj⟩)
  have hcm : f .c (nu n b) = true := by
    unfold f counterFun; dsimp only; rw [if_neg (by rw [hb0]; decide)]; simp
  have hdm : f .d (nu n b) = true := rfl
  have hem : f .e (nu n b) = true := hnubit
  have hcn : valAt n hn V .c n = Gm n b (nu n b) := by
    rw [valAt_c_n_eq_Gm hn f hnu2 hnun hcm hdm hem
      (fun j hj1 _ => by
        unfold f counterFun; dsimp only
        rw [if_neg (by rw [hb0]; decide)]
        exact decide_eq_false (by omega)),
      hva (nu n b + 1) (by omega)]
    rfl
  exact ⟨hva, hcn⟩

lemma even_step_e_one {n b m₀ : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hm₀1 : 10 * n - 12 ≤ m₀) (_hm₀2 : m₀ < 10 * n - 10)
    {s₀ : MDPState n} (hs₀ : StateAt n (counterFun n b) m₀ s₀) :
    ∃ s₁ : MDPState n, MdpPath n hn 1 s₀ s₁ ∧
      StateAt n (evenBlock1Fun n b 2) 0 s₁ := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, _⟩
  rcases counterFun_even_vals hn heven hbpos hb with ⟨hva, hcn⟩
  have hb0 : b.testBit 0 = false := by
    rw [Nat.testBit_zero]; exact decide_eq_false (by omega)
  set f := counterFun n b
  set V := policyValue n hn (policyOf n f)
  have hv₀ : ValidRow n (.e, 1) := ⟨le_refl 1, by omega⟩
  have hf₀ : f .e 1 = false := hb0
  have hrank : columnRank n ⟨.e, 1, !f .e 1⟩ = 0 := by
    rw [hf₀, Bool.not_false, columnRank_e_true, if_pos rfl]
  have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.e, 1) hv₀) := by
    rw [mdpImproving_e_one_iff hn f, hf₀, if_neg (by decide), hcn]
    have hH : HVal n hn V 1 = rewardH n 1 + Gm n b (nu n b) := by
      unfold HVal
      rw [hva 2 (le_refl 2), vaBase_eq_Gm_nu_of_even hn heven hbpos hb (by omega) hnu2]
    have hrh : (1 : ℚ) < rewardH n 1 := by
      have : (2 * (n : ℚ) + 1) ^ 2 ≤ rewardH n 1 := by
        unfold rewardH scale
        rw [show (-((2 * (n : ℚ)) + 1)) ^ (2 * 1) = (2 * (n : ℚ) + 1) ^ 2 by ring]
      have hn3 : (3 : ℚ) ≤ n := by exact_mod_cast hn
      nlinarith
    have heps : 0 < epsilon n := epsilon_pos n
    nlinarith
  have hno : ∀ kind i (hv : ValidRow n (kind, i)),
      (m₀ < columnRank n ⟨kind, i, !f kind i⟩ ∨
        columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.e, 1, !f .e 1⟩) →
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
    intro kind i hv hor
    rw [hrank] at hor
    have hgt : 10 * n - 12 < columnRank n ⟨kind, i, !f kind i⟩ := by omega
    cases kind
    · have hi2 : 2 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      cases hfa : f .a i <;> rw [hfa] at hgt
      · simp only [Bool.not_false, columnRank_a_true] at hgt; omega
      · simp only [Bool.not_true, columnRank_a_false] at hgt
        have hi_eq : i = 2 := by omega
        subst hi_eq
        have hfd : f .d 2 = true := rfl
        have hfe : f .e 2 = true := hfa
        rw [mdpStrictNonImproving_a_iff hn f hv, hfa, if_pos rfl,
          GRhs_eq_Gm_of_de_true_true hn f (le_refl 2) (by omega) hfd hfe (hva 3 (by omega)),
          hva 3 (by omega)]
        unfold Gm
        have := rewardGH_ge_42 (n := n) hn (by omega : 1 ≤ 2)
        linarith
    · have : 2 ≤ i ∧ i ≤ n - 1 := hv
      cases hfb : f .b i <;> rw [hfb] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hgt <;>
        omega
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfc : f .c i <;> rw [hfc] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hgt <;>
        omega
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfd : f .d i <;> rw [hfd] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hgt <;>
        omega
    · have : 1 ≤ i ∧ i ≤ n := hv
      cases hfe : f .e i <;> rw [hfe] at hgt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hgt
      · split_ifs at hgt <;> omega
      · omega
  have hup : ∀ kind i, ValidRow n (kind, i) →
      (if kind = .e ∧ i = 1 then !f .e 1 else f kind i) = evenBlock1Fun n b 2 kind i := by
    intro kind i hv
    by_cases h : kind = .e ∧ i = 1
    · rcases h with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩, hf₀]; rfl
    · rw [if_neg h]
      cases kind <;> unfold f counterFun evenBlock1Fun <;> dsimp only
      · rw [if_neg (by rw [hb0]; decide)]
        have hin : i ≤ n - 1 := hv.2
        by_cases hi : i = nu n b
        · subst hi; rw [decide_eq_true rfl, decide_eq_true ⟨rfl, by omega, hnu2⟩]
        · rw [decide_eq_false hi, decide_eq_false (by tauto)]
      · rw [if_neg (by rw [hb0]; decide)]
      · rw [if_neg (by omega)]
      · have hi : i ≠ 1 := fun heq => h ⟨rfl, heq⟩
        have hi1 : 1 ≤ i := hv.1
        rw [if_neg (by omega)]
  rcases step_stateAt_of_wrap hn hs₀ .e 1 hv₀ (by rw [hrank]; omega) himp hno hup with
    ⟨s₁, hp, hs₁⟩
  rw [hrank] at hs₁
  exact ⟨s₁, hp, hs₁⟩

lemma evenBlock1_vals {n b k : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hk2 : 2 ≤ k) (_hkn : k ≤ n + 1) :
    let f := evenBlock1Fun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    G1Val n hn V = Gm n b 1 ∧
    (∀ i, 2 ≤ i → i ≤ n → (i ≤ k ∨ i ≤ nu n b) → BPrev n hn V i = Gm n b 1) ∧
    (∀ i, 2 ≤ i → i ≤ n → i ≤ nu n b → CPrev n hn V i = Gm n b 1) ∧
    (∀ i, nu n b < i → i ≤ n → CPrev n hn V i = Gm n b (nu n b)) ∧
    valAt n hn V .c n = Gm n b (nu n b) := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, _⟩
  intro f V
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j _ _ hbj => by
        dsimp [f, evenBlock1Fun]
        exact ⟨by split_ifs <;> first | exact hbj | rfl, by split_ifs <;> first | rfl | exact hbj⟩)
  have he1 : f .e 1 = true := by dsimp [f, evenBlock1Fun]; rw [if_pos (by omega)]
  have hg1 : G1Val n hn V = Gm n b 1 := by
    rw [G1Val_of_e_one_true hn f he1, hva 2 (le_refl 2)]; rfl
  have hbp : ∀ i, 2 ≤ i → i ≤ n → (i ≤ k ∨ i ≤ nu n b) → BPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin hik
    rw [BPrev_eq_G1Val hn f i hi2 hin (fun j _ hji => by
      dsimp [f, evenBlock1Fun]; exact decide_eq_false (by omega)), hg1]
  have hcp_le : ∀ i, 2 ≤ i → i ≤ n → i ≤ nu n b → CPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin hinu
    rw [CPrev_eq_G1Val hn f i hi2 hin (fun j _ hji => by
      dsimp [f, evenBlock1Fun]; exact decide_eq_false (by omega)), hg1]
  have hcm : f .c (nu n b) = true := by dsimp [f, evenBlock1Fun]; simp
  have hdm : f .d (nu n b) = true := by
    dsimp [f, evenBlock1Fun]; split_ifs <;> first | exact hnubit | rfl
  have hem : f .e (nu n b) = true := by
    dsimp [f, evenBlock1Fun]; split_ifs <;> first | rfl | exact hnubit
  have hcp_gt : ∀ i, nu n b < i → i ≤ n → CPrev n hn V i = Gm n b (nu n b) := by
    intro i higt hin
    rw [CPrev_eq_Gm hn f hnu2 hcm hdm hem i higt hin
      (fun j hj1 _ => by dsimp [f, evenBlock1Fun]; exact decide_eq_false (by omega)),
      hva (nu n b + 1) (by omega)]
    rfl
  have hcn : valAt n hn V .c n = Gm n b (nu n b) := by
    rw [valAt_c_n_eq_Gm hn f hnu2 hnun hcm hdm hem
      (fun j hj1 _ => by dsimp [f, evenBlock1Fun]; exact decide_eq_false (by omega)),
      hva (nu n b + 1) (by omega)]
    rfl
  exact ⟨hva, hg1, hbp, hcp_le, hcp_gt, hcn⟩

lemma evenBlock1_nonImproving_lt {n b k i : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (hi2 : 2 ≤ i) (hik : i < k) :
    let f := evenBlock1Fun n b k
    (∀ hv : ValidRow n (.b, i), mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.b, i) hv)) ∧
    (i ≠ nu n b → ∀ hv : ValidRow n (.c, i), mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.c, i) hv)) ∧
    (f .d i = true → ∀ hv : ValidRow n (.d, i), mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.d, i) hv)) := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, hnumin⟩
  rcases evenBlock1_vals hn heven hbpos hb hk2 hkn with ⟨hva, _, hbp, hcp_le, hcp_gt, _⟩
  intro f
  have hin : i ≤ n := by omega
  have hfb : f .b i = false := by dsimp [f, evenBlock1Fun]; exact decide_eq_false (by omega)
  have hfd : f .d i = b.testBit (i - 1) := by dsimp [f, evenBlock1Fun]; rw [if_pos ⟨hi2, hik⟩]
  have hfe : f .e i = true := by dsimp [f, evenBlock1Fun]; rw [if_pos hik]
  have hbpi : BPrev n hn (policyValue n hn (policyOf n f)) i = Gm n b 1 :=
    hbp i hi2 hin (Or.inl (by omega))
  have hnu_lt_g1 := Gm_nu_lt_Gm_one_of_even hn heven hbpos hb
  cases hbi : b.testBit (i - 1)
  · rw [hbi] at hfd
    have hi_ne_nu : i ≠ nu n b := by intro heq; subst heq; rw [hnubit] at hbi; contradiction
    have hfc : f .c i = false := by dsimp [f, evenBlock1Fun]; exact decide_eq_false hi_ne_nu
    have hFG := FRhs_GRhs_of_de_false_true_Gm (b' := b) (b := b) (m := 1) (i := i)
      hn f hi2 hin (le_refl 1) (by omega) hfd hfe (hva (i + 1) (by omega)) hbpi
    have hG_lt_nu : GRhs n hn (policyValue n hn (policyOf n f)) i < Gm n b (nu n b) := by
      have hF_up := (abs_lt.mp hFG.1).2
      have hG1_eq : Gm n b 1 = rewardG n 1 + rewardH n 1 + Gm n b (nu n b) := by
        rw [show Gm n b 1 = rewardG n 1 + rewardH n 1 + vaBase n b 2 from rfl,
          vaBase_eq_Gm_nu_of_even hn heven hbpos hb (by omega) hnu2]
      have hrg_i : rewardG n i ≤ -(scale n) ^ 3 := by
        rw [rewardG_eq (by omega : 1 ≤ i)]
        have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
        have hp : (scale n) ^ 3 ≤ (scale n) ^ (2 * i - 1) :=
          pow_le_pow_right₀ (by linarith) (by omega)
        linarith
      have hgh1 : rewardG n 1 + rewardH n 1 = -(scale n) + (scale n) ^ 2 := by
        rw [rewardG_eq (le_refl 1), rewardH_eq]; ring
      have hs : (7 : ℚ) ≤ scale n := scale_ge_seven hn
      have hscube : (scale n) ^ 2 * 7 ≤ (scale n) ^ 3 := by
        have : (scale n) ^ 3 = (scale n) ^ 2 * scale n := by ring
        nlinarith
      have hs2 : (49 : ℚ) ≤ (scale n) ^ 2 := by nlinarith
      unfold GRhs
      linarith
    refine ⟨fun hv => ?_, fun _ hv => ?_, fun hfd_t => by rw [hfd] at hfd_t; contradiction⟩
    · rw [mdpStrictNonImproving_b_iff hn f hv, hfb, if_neg (by decide), hbpi]
      linarith [hFG.2.2.2]
    · rw [mdpStrictNonImproving_c_iff hn f hv, hfc, if_neg (by decide)]
      rcases lt_or_gt_of_ne hi_ne_nu with hilt | higt
      · rw [hcp_le i hi2 hin (by omega)]; linarith [hFG.2.2.2]
      · rw [hcp_gt i higt hin]; exact hG_lt_nu
  · rw [hbi] at hfd
    have hinu : nu n b ≤ i := by
      by_contra hlt
      have := hnumin i (by omega) (by omega)
      rw [this] at hbi; contradiction
    have hFG_G := GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))
    have hFG_F := FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))
    have hH := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ i) hin
    refine ⟨fun hv => ?_, fun hne hv => ?_, fun _ hv => ?_⟩
    · rw [mdpStrictNonImproving_b_iff hn f hv, hfb, if_neg (by decide), hbpi, hFG_G]
      rcases eq_or_lt_of_le hinu with rfl | higt
      · linarith
      · have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (by omega : 1 ≤ nu n b) higt hin hbi
        linarith
    · have higt : nu n b < i := by omega
      have hfc : f .c i = false := by dsimp [f, evenBlock1Fun]; exact decide_eq_false hne
      rw [mdpStrictNonImproving_c_iff hn f hv, hfc, if_neg (by decide), hcp_gt i higt hin, hFG_G]
      have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (by omega : 1 ≤ nu n b) higt hin hbi
      linarith
    · rw [mdpStrictNonImproving_d_iff hn f hv, hfd, if_pos rfl, hbpi, hFG_F]
      linarith

lemma evenBlock1Mid_vals {n b k : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hk2 : 2 ≤ k) (hkn : k ≤ n) (_hbk : b.testBit (k - 1) = false) :
    let f := evenBlock1MidFun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    BPrev n hn V k = Gm n b 1 ∧
    valAt n hn V .c n = Gm n b (nu n b) := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, _⟩
  intro f V
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j _ _ hbj => by
        dsimp [f, evenBlock1MidFun]
        exact ⟨by split_ifs <;> first | exact hbj | rfl, by split_ifs <;> first | rfl | exact hbj⟩)
  have he1 : f .e 1 = true := by dsimp [f, evenBlock1MidFun]; rw [if_pos (by omega)]
  have hg1 : G1Val n hn V = Gm n b 1 := by
    rw [G1Val_of_e_one_true hn f he1, hva 2 (le_refl 2)]; rfl
  have hbpk : BPrev n hn V k = Gm n b 1 := by
    rw [BPrev_eq_G1Val hn f k hk2 hkn (fun j _ hjk => by
      dsimp [f, evenBlock1MidFun]; exact decide_eq_false (by omega)), hg1]
  have hcm : f .c (nu n b) = true := by dsimp [f, evenBlock1MidFun]; simp
  have hdm : f .d (nu n b) = true := by
    dsimp [f, evenBlock1MidFun]; split_ifs <;> first | exact hnubit | rfl
  have hem : f .e (nu n b) = true := by
    dsimp [f, evenBlock1MidFun]; split_ifs <;> first | rfl | exact hnubit
  have hcn : valAt n hn V .c n = Gm n b (nu n b) := by
    rw [valAt_c_n_eq_Gm hn f hnu2 hnun hcm hdm hem
      (fun j hj1 _ => by dsimp [f, evenBlock1MidFun]; exact decide_eq_false (by omega)),
      hva (nu n b + 1) (by omega)]
    rfl
  exact ⟨hva, hbpk, hcn⟩
lemma even_block1_step {n b k m : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    {s : MDPState n} (hs : StateAt n (evenBlock1Fun n b k) m s)
    (hm : m + 1 ≤ 4 * (k - 2) + 1) (hm_max : m ≤ 4 * n - 6) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      m' + 1 ≤ 4 * (k + 1 - 2) + 1 ∧ m' ≤ 4 * n - 6 ∧
      StateAt n (evenBlock1Fun n b (k + 1)) m' s' := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, _⟩
  have hnu_lt_g1 := Gm_nu_lt_Gm_one_of_even hn heven hbpos hb
  cases hbk : b.testBit (k - 1)
  · rcases evenBlock1_vals (k := k) hn heven hbpos hb hk2 (by omega) with
      ⟨hva, _, hbp, hcp_le, hcp_gt, hcn⟩
    set f := evenBlock1Fun n b k
    set V := policyValue n hn (policyOf n f)
    have hk_ne_nu : k ≠ nu n b := by intro heq; subst heq; rw [hnubit] at hbk; contradiction
    have hv_d : ValidRow n (.d, k) := ⟨hk2, hkn⟩
    have hfd : f .d k = true := by dsimp [f, evenBlock1Fun]; rw [if_neg (by omega)]
    have hfe : f .e k = false := by dsimp [f, evenBlock1Fun]; rw [if_neg (by omega), hbk]
    have hrank_d : columnRank n ⟨.d, k, !f .d k⟩ = 4 * (k - 2) + 1 := by
      rw [hfd, Bool.not_true, columnRank_d_false]
    have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b) (b := b) (m := nu n b) (i := k)
      hn f hk2 hkn (by omega) hnun hfd hfe (hva (k + 1) (by omega)) hcn
    have hbpk : BPrev n hn V k = Gm n b 1 := hbp k hk2 hkn (Or.inl (le_refl k))
    have himp_d : mdpImproving n hn (policyOf n f) (mkRow n hn (.d, k) hv_d) := by
      rw [mdpImproving_d_iff hn f hv_d, hfd, if_pos rfl, hbpk]
      have habs := (abs_lt.mp hFG.1).2
      linarith
    have hno_d : ∀ kind i (hv : ValidRow n (kind, i)),
        m < columnRank n ⟨kind, i, !f kind i⟩ →
        columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.d, k, !f .d k⟩ →
        mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
      intro kind i hv _ hlt
      rw [hrank_d] at hlt
      cases kind
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfa : f .a i <;> rw [hfa] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
          omega
      · have hi2 : 2 ≤ i := hv.1
        cases hfbi : f .b i <;> rw [hfbi] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hlt
        · exact (evenBlock1_nonImproving_lt hn heven hbpos hb hk2 (by omega) hi2 (by omega)).1 hv
        · have : i = nu n b ∧ i < n ∧ k ≤ i := of_decide_eq_true hfbi
          omega
      · have hi2 : 2 ≤ i := hv.1
        cases hfci : f .c i <;> rw [hfci] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hlt
        · have hi_ne : i ≠ nu n b := of_decide_eq_false hfci
          have hik_le : i ≤ k := by omega
          rcases eq_or_lt_of_le hik_le with rfl | hilt
          · rw [mdpStrictNonImproving_c_iff hn f hv, hfci, if_neg (by decide)]
            rcases lt_or_gt_of_ne hk_ne_nu with hklt | hkgt
            · rw [hcp_le i hi2 hkn (by omega)]; linarith [hFG.2.2.2]
            · rw [hcp_gt i hkgt hkn]; linarith [hFG.2.2.2]
          · exact (evenBlock1_nonImproving_lt hn heven hbpos hb hk2 (by omega) hi2 hilt).2.1 hi_ne hv
        · omega
      · have hi2 : 2 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        cases hfdi : f .d i <;> rw [hfdi] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hlt
        · omega
        · exact (evenBlock1_nonImproving_lt hn heven hbpos hb hk2 (by omega) hi2 (by omega)).2.2 hfdi hv
      · have hi1 : 1 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        cases hfei : f .e i <;> rw [hfei] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hlt
        · have hik_le : k ≤ i := by
            by_contra hlt'
            have : f .e i = true := by dsimp [f, evenBlock1Fun]; rw [if_pos (by omega)]
            rw [this] at hfei; contradiction
          split_ifs at hlt <;> omega
        · omega
    have hup_d : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .d ∧ i = k then !f .d k else f kind i) = evenBlock1MidFun n b k kind i := by
      intro kind i _
      by_cases h : kind = .d ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hfd]
        dsimp [evenBlock1MidFun]; rw [if_pos ⟨hk2, le_refl _⟩, hbk]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [f, evenBlock1Fun, evenBlock1MidFun]
        have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
        by_cases h1 : 2 ≤ i ∧ i < k
        · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs .d k hv_d (by rw [hrank_d]; omega) himp_d hno_d hup_d with
      ⟨s₁, hp₁, hs₁⟩
    rw [hrank_d] at hs₁
    rcases evenBlock1Mid_vals hn heven hbpos hb hk2 hkn hbk with ⟨hva_m, hbpk_m, hcn_m⟩
    set fm := evenBlock1MidFun n b k
    set Vm := policyValue n hn (policyOf n fm)
    have hv_e : ValidRow n (.e, k) := ⟨by omega, hkn⟩
    have hfd_m : fm .d k = false := by
      dsimp [fm, evenBlock1MidFun]; rw [if_pos ⟨hk2, le_refl k⟩, hbk]
    have hfe_m : fm .e k = false := by
      dsimp [fm, evenBlock1MidFun]; rw [if_neg (by omega), hbk]
    have hrank_e : columnRank n ⟨.e, k, !fm .e k⟩ = 4 * (k - 2) + 2 := by
      rw [hfe_m, Bool.not_false, columnRank_e_true, if_neg (by omega)]
    have himp_e : mdpImproving n hn (policyOf n fm) (mkRow n hn (.e, k) hv_e) := by
      rw [mdpImproving_e_iff hn fm hv_e hk2, hfe_m, if_neg (by decide)]
      have hH_m : 1 + valAt n hn Vm .c n < HVal n hn Vm k := by
        rw [hcn_m]; unfold HVal; rw [hva_m (k + 1) (by omega)]
        have := HVal_gt_Gm_nu_of_even hn heven hbpos hb (by omega : 1 ≤ k) hkn
        linarith
      have hB_m : 1 + valAt n hn Vm .c n < BPrev n hn Vm k := by
        rw [hcn_m, hbpk_m]; linarith
      exact FRhs_gt_one_add_cn_of_de_false_false hn fm hk2 hkn hfd_m hfe_m hH_m hB_m
    have hno_e : ∀ kind i (hv : ValidRow n (kind, i)),
        4 * (k - 2) + 1 < columnRank n ⟨kind, i, !fm kind i⟩ →
        columnRank n ⟨kind, i, !fm kind i⟩ < columnRank n ⟨.e, k, !fm .e k⟩ →
        mdpStrictNonImproving n hn (policyOf n fm) (mkRow n hn (kind, i) hv) := by
      intro _ _ _ hgt hlt; rw [hrank_e] at hlt; omega
    have hup_e : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .e ∧ i = k then !fm .e k else fm kind i) = evenBlock1Fun n b (k + 1) kind i := by
      intro kind i _
      by_cases h : kind = .e ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hfe_m]
        dsimp [evenBlock1Fun]; rw [if_pos (by omega)]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [fm, evenBlock1MidFun, evenBlock1Fun]
        · by_cases hi : i = nu n b ∧ i < n ∧ k ≤ i
          · rw [decide_eq_true hi, decide_eq_true ⟨hi.1, hi.2.1, by omega⟩]
          · rw [decide_eq_false hi, decide_eq_false (by omega)]
        · by_cases h1 : 2 ≤ i ∧ i ≤ k
          · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
          · rw [if_neg h1, if_neg (by omega)]
        · have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
          by_cases h1 : i < k
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs₁ .e k hv_e (by rw [hrank_e]; omega) himp_e hno_e hup_e with
      ⟨s₂, hp₂, hs₂⟩
    rw [hrank_e] at hs₂
    exact ⟨2, s₂, 4 * (k - 2) + 2, hp₁.trans hp₂, by omega, by omega, hs₂⟩
  · by_cases hknu : k = nu n b ∧ k < n
    · rcases hknu with ⟨rfl, hkn_lt⟩
      rcases evenBlock1_vals (k := nu n b) hn heven hbpos hb hk2 (by omega) with
        ⟨hva, _, hbp, _, _, _⟩
      set f := evenBlock1Fun n b (nu n b)
      set V := policyValue n hn (policyOf n f)
      have hv_b : ValidRow n (.b, nu n b) := ⟨hk2, by omega⟩
      have hfb : f .b (nu n b) = true := by
        dsimp [f, evenBlock1Fun]; exact decide_eq_true ⟨rfl, hkn_lt, le_refl _⟩
      have hfd : f .d (nu n b) = true := by dsimp [f, evenBlock1Fun]; rw [if_neg (by omega)]
      have hfe : f .e (nu n b) = true := by dsimp [f, evenBlock1Fun]; rw [if_neg (by omega), hbk]
      have hrank_b : columnRank n ⟨.b, nu n b, !f .b (nu n b)⟩ = 4 * (nu n b - 2) + 4 := by
        rw [hfb, Bool.not_true, columnRank_b_false]
      have hbpk : BPrev n hn V (nu n b) = Gm n b 1 := hbp (nu n b) hk2 hkn (Or.inl (le_refl _))
      have himp_b : mdpImproving n hn (policyOf n f) (mkRow n hn (.b, nu n b) hv_b) := by
        rw [mdpImproving_b_iff hn f hv_b, hfb, if_pos rfl, hbpk,
          GRhs_eq_Gm_of_de_true_true hn f hk2 hkn hfd hfe (hva (nu n b + 1) (by omega))]
        linarith
      have hno_b : ∀ kind i (hv : ValidRow n (kind, i)),
          m < columnRank n ⟨kind, i, !f kind i⟩ →
          columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.b, nu n b, !f .b (nu n b)⟩ →
          mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
        intro kind i hv _ hlt
        rw [hrank_b] at hlt
        cases kind
        · have : 2 ≤ i ∧ i ≤ n := hv
          cases hfa : f .a i <;> rw [hfa] at hlt <;>
            simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
            omega
        · have hi2 : 2 ≤ i := hv.1
          cases hfbi : f .b i <;> rw [hfbi] at hlt <;>
            simp only [Bool.not_true, Bool.not_false, columnRank_b_true, columnRank_b_false] at hlt
          · have : i ≠ nu n b := by
              intro heq; subst heq; rw [hfb] at hfbi; contradiction
            exact (evenBlock1_nonImproving_lt hn heven hbpos hb hk2 (by omega) hi2 (by omega)).1 hv
          · have : i = nu n b ∧ i < n ∧ nu n b ≤ i := of_decide_eq_true hfbi
            omega
        · have hi2 : 2 ≤ i := hv.1
          cases hfci : f .c i <;> rw [hfci] at hlt <;>
            simp only [Bool.not_true, Bool.not_false, columnRank_c_true, columnRank_c_false] at hlt
          · have hi_ne : i ≠ nu n b := of_decide_eq_false hfci
            exact (evenBlock1_nonImproving_lt hn heven hbpos hb hk2 (by omega) hi2 (by omega)).2.1 hi_ne hv
          · omega
        · have hi2 : 2 ≤ i := hv.1
          have hin : i ≤ n := hv.2
          cases hfdi : f .d i <;> rw [hfdi] at hlt <;>
            simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hlt
          · omega
          · have hik_le : i ≤ nu n b := by omega
            rcases eq_or_lt_of_le hik_le with rfl | hilt
            · rw [mdpStrictNonImproving_d_iff hn f hv, hfd, if_pos rfl, hbpk,
                FRhs_eq_HVal_of_de_true_true hn f hk2 hkn hfd hfe (hva (nu n b + 1) (by omega))]
              have := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ nu n b) hkn
              linarith
            · exact (evenBlock1_nonImproving_lt hn heven hbpos hb hk2 (by omega) hi2 hilt).2.2 hfdi hv
        · have hi1 : 1 ≤ i := hv.1
          have hin : i ≤ n := hv.2
          cases hfei : f .e i <;> rw [hfei] at hlt <;>
            simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hlt
          · have hik_lt : nu n b < i := by
              have hik_le : nu n b ≤ i := by
                by_contra hlt'
                have : f .e i = true := by dsimp [f, evenBlock1Fun]; rw [if_pos (by omega)]
                rw [this] at hfei; contradiction
              rcases eq_or_lt_of_le hik_le with rfl | hgt'
              · rw [hfe] at hfei; contradiction
              · exact hgt'
            split_ifs at hlt <;> omega
          · omega
      have hup_b : ∀ kind i, ValidRow n (kind, i) →
          (if kind = .b ∧ i = nu n b then !f .b (nu n b) else f kind i) =
            evenBlock1Fun n b (nu n b + 1) kind i := by
        intro kind i _
        by_cases h : kind = .b ∧ i = nu n b
        · rcases h with ⟨rfl, rfl⟩
          rw [if_pos ⟨rfl, rfl⟩, hfb]
          dsimp [evenBlock1Fun]; exact (decide_eq_false (by omega)).symm
        · rw [if_neg h]
          cases kind <;> dsimp [f, evenBlock1Fun]
          · have hi : i ≠ nu n b := fun heq => h ⟨rfl, heq⟩
            rw [decide_eq_false (by tauto), decide_eq_false (by tauto)]
          · by_cases hi : i = nu n b
            · subst hi; rw [if_neg (by omega), if_pos ⟨hk2, by omega⟩, hbk]
            · by_cases h1 : 2 ≤ i ∧ i < nu n b
              · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
              · rw [if_neg h1, if_neg (by omega)]
          · by_cases hi : i = nu n b
            · subst hi; rw [if_neg (by omega), if_pos (by omega), hbk]
            · by_cases h1 : i < nu n b
              · rw [if_pos h1, if_pos (by omega)]
              · rw [if_neg h1, if_neg (by omega)]
      rcases step_stateAt_of_le hn hs .b (nu n b) hv_b (by rw [hrank_b]; omega) himp_b hno_b hup_b with
        ⟨s₁, hp₁, hs₁⟩
      rw [hrank_b] at hs₁
      exact ⟨1, s₁, 4 * (nu n b - 2) + 4, hp₁, by omega, by omega, hs₁⟩
    · have hfeq : evenBlock1Fun n b (k + 1) = evenBlock1Fun n b k := by
        funext kind i
        cases kind <;> dsimp [evenBlock1Fun]
        · by_cases hi : i = nu n b ∧ i < n ∧ k ≤ i
          · rw [decide_eq_true ⟨hi.1, hi.2.1, by omega⟩, decide_eq_true hi]
          · rw [decide_eq_false (by omega), decide_eq_false hi]
        · by_cases hi : i = k
          · subst hi; rw [if_pos ⟨hk2, by omega⟩, if_neg (by omega), hbk]
          · by_cases h1 : 2 ≤ i ∧ i < k
            · rw [if_pos ⟨h1.1, by omega⟩, if_pos h1]
            · rw [if_neg (by omega), if_neg h1]
        · by_cases hi : i = k
          · subst hi; rw [if_pos (by omega), if_neg (by omega), hbk]
          · by_cases h1 : i < k
            · rw [if_pos (by omega), if_pos h1]
            · rw [if_neg (by omega), if_neg h1]
      refine ⟨0, s, m, MdpPath.refl s, by omega, hm_max, ?_⟩
      rw [hfeq]; exact hs

lemma even_block1_loop {n b : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    {m : ℕ} {s : MDPState n} (hs : StateAt n (evenBlock1Fun n b k) m s)
    (hm : m + 1 ≤ 4 * (k - 2) + 1) (hm_max : m ≤ 4 * n - 6) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      m' ≤ 4 * n - 6 ∧
      StateAt n (evenBlock1Fun n b (n + 1)) m' s' := by
  by_cases hlt : k ≤ n
  · rcases even_block1_step hn heven hbpos hb hk2 hlt hs hm hm_max with
      ⟨t₁, s₁, m₁, hp₁, hm₁, hm₁_max, hs₁⟩
    rcases even_block1_loop hn heven hbpos hb (k + 1) (by omega) (by omega) hs₁ hm₁ hm₁_max with
      ⟨t₂, s₂, m₂, hp₂, hm₂_max, hs₂⟩
    exact ⟨t₁ + t₂, s₂, m₂, hp₁.trans hp₂, hm₂_max, hs₂⟩
  · have hk_eq : k = n + 1 := by omega
    subst hk_eq
    exact ⟨0, s, m, MdpPath.refl s, hm_max, hs⟩
termination_by (n + 1) - k
decreasing_by omega

def evenBlock3Fun (_n b k : ℕ) : Kind → ℕ → Bool
  | .a, i => b.testBit (i - 1)
  | .b, _ => false
  | .c, _ => false
  | .d, i => b.testBit (i - 1)
  | .e, i => if 2 ≤ i ∧ i < k then b.testBit (i - 1) else true

lemma even_block2_step {n b m : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n)
    {s : MDPState n} (hs : StateAt n (evenBlock1Fun n b (n + 1)) m s)
    (hm : m ≤ 4 * n - 6) :
    ∃ s' : MDPState n, MdpPath n hn 1 s s' ∧
      StateAt n (evenBlock3Fun n b 2) (4 * n - 5 + 2 * (nu n b - 2)) s' := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, _⟩
  rcases evenBlock1_vals (k := n + 1) hn heven hbpos hb (by omega) (le_refl _) with
    ⟨hva, _, _, hcp_le, hcp_gt, hcn⟩
  have hnu_lt_g1 := Gm_nu_lt_Gm_one_of_even hn heven hbpos hb
  set f := evenBlock1Fun n b (n + 1)
  set V := policyValue n hn (policyOf n f)
  have hv₀ : ValidRow n (.c, nu n b) := ⟨hnu2, hnun⟩
  have hf₀ : f .c (nu n b) = true := by dsimp [f, evenBlock1Fun]; simp
  have hfd₀ : f .d (nu n b) = true := by
    dsimp [f, evenBlock1Fun]; rw [if_pos ⟨hnu2, by omega⟩, hnubit]
  have hfe₀ : f .e (nu n b) = true := by dsimp [f, evenBlock1Fun]; rw [if_pos (by omega)]
  have hrank : columnRank n ⟨.c, nu n b, !f .c (nu n b)⟩ = 4 * n - 5 + 2 * (nu n b - 2) := by
    rw [hf₀, Bool.not_true, columnRank_c_false]
  have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.c, nu n b) hv₀) := by
    rw [mdpImproving_c_iff hn f hv₀, hf₀, if_pos rfl,
      hcp_le (nu n b) hnu2 hnun (le_refl _),
      GRhs_eq_Gm_of_de_true_true hn f hnu2 hnun hfd₀ hfe₀ (hva (nu n b + 1) (by omega))]
    linarith
  have hno : ∀ kind i (hv : ValidRow n (kind, i)),
      m < columnRank n ⟨kind, i, !f kind i⟩ →
      columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.c, nu n b, !f .c (nu n b)⟩ →
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
    intro kind i hv _ hlt
    rw [hrank] at hlt
    cases kind
    · have : 2 ≤ i ∧ i ≤ n := hv
      cases hfa : f .a i <;> rw [hfa] at hlt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
        omega
    · have hi2 : 2 ≤ i := hv.1
      have hin : i ≤ n - 1 := hv.2
      exact (evenBlock1_nonImproving_lt hn heven hbpos hb (by omega) (le_refl _) hi2 (by omega)).1 hv
    · have hi2 : 2 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      have hi_ne : i ≠ nu n b := by
        intro heq; subst heq; rw [hf₀] at hlt
        simp only [Bool.not_true, columnRank_c_false] at hlt; omega
      exact (evenBlock1_nonImproving_lt hn heven hbpos hb (by omega) (le_refl _) hi2 (by omega)).2.1 hi_ne hv
    · have hi2 : 2 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      cases hfdi : f .d i <;> rw [hfdi] at hlt <;>
        simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hlt
      · omega
      · exact (evenBlock1_nonImproving_lt hn heven hbpos hb (by omega) (le_refl _) hi2 (by omega)).2.2 hfdi hv
    · have hi1 : 1 ≤ i := hv.1
      have hin : i ≤ n := hv.2
      have hfei : f .e i = true := by dsimp [f, evenBlock1Fun]; rw [if_pos (by omega)]
      rw [hfei] at hlt
      simp only [Bool.not_true, columnRank_e_false] at hlt; omega
  have hup : ∀ kind i, ValidRow n (kind, i) →
      (if kind = .c ∧ i = nu n b then !f .c (nu n b) else f kind i) = evenBlock3Fun n b 2 kind i := by
    intro kind i hv
    by_cases h : kind = .c ∧ i = nu n b
    · rcases h with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩, hf₀]; rfl
    · rw [if_neg h]
      cases kind <;> dsimp [f, evenBlock1Fun, evenBlock3Fun, ValidRow] at hv ⊢
      · exact decide_eq_false (by omega)
      · have hi : i ≠ nu n b := fun heq => h ⟨rfl, heq⟩
        exact decide_eq_false hi
      · rw [if_pos ⟨hv.1, by omega⟩]
      · rw [if_pos (by omega), if_neg (by omega)]
  rcases step_stateAt_of_le hn hs .c (nu n b) hv₀ (by rw [hrank]; omega) himp hno hup with
    ⟨s', hp, hs'⟩
  rw [hrank] at hs'
  exact ⟨s', hp, hs'⟩
lemma evenBlock3_vals {n b k : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (_hk2 : 2 ≤ k) (_hkn : k ≤ n + 1) :
    let f := evenBlock3Fun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    G1Val n hn V = Gm n b 1 ∧
    (∀ i, 2 ≤ i → i ≤ n → BPrev n hn V i = Gm n b 1) ∧
    (∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1) ∧
    valAt n hn V .c n = Gm n b 1 ∧
    (∀ i (hv : ValidRow n (.c, i)), mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.c, i) hv)) := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, hnumin⟩
  have hnu_lt_g1 := Gm_nu_lt_Gm_one_of_even hn heven hbpos hb
  intro f V
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j _ _ hbj => by
        dsimp [f, evenBlock3Fun]
        refine ⟨hbj, ?_⟩
        split_ifs
        · exact hbj
        · rfl)
  have he1 : f .e 1 = true := rfl
  have hg1 : G1Val n hn V = Gm n b 1 := by
    rw [G1Val_of_e_one_true hn f he1, hva 2 (le_refl 2)]; rfl
  have hbp : ∀ i, 2 ≤ i → i ≤ n → BPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin
    rw [BPrev_eq_G1Val hn f i hi2 hin (fun _ _ _ => rfl), hg1]
  have hcp : ∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin
    rw [CPrev_eq_G1Val hn f i hi2 hin (fun _ _ _ => rfl), hg1]
  have hcn : valAt n hn V .c n = Gm n b 1 := by
    rw [valAt_c_n_eq_G1Val hn f (fun _ _ _ => rfl), hg1]
  have hc_no : ∀ i (hv : ValidRow n (.c, i)),
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.c, i) hv) := by
    intro i hv
    have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    have hfc : f .c i = false := rfl
    rw [mdpStrictNonImproving_c_iff hn f hv, hfc, if_neg (by decide), hcp i hi2 hin]
    have hfd : f .d i = b.testBit (i - 1) := rfl
    cases hbi : b.testBit (i - 1)
    · rw [hbi] at hfd
      cases hfe : f .e i
      · have hH := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ i) hin
        have hFG := FRhs_GRhs_of_de_false_false_same_Gm (b' := b) (b := b) (m := 1) (i := i)
          hn f hi2 hin (le_refl 1) (by omega) hfd hfe (hva (i + 1) (by omega))
          (hbp i hi2 hin) hcn (by linarith)
        linarith [hFG.2.2]
      · have hFG := FRhs_GRhs_of_de_false_true_Gm (b' := b) (b := b) (m := 1) (i := i)
          hn f hi2 hin (le_refl 1) (by omega) hfd hfe (hva (i + 1) (by omega)) (hbp i hi2 hin)
        linarith [hFG.2.2.2]
    · rw [hbi] at hfd
      have hfe : f .e i = true := by
        dsimp [f, evenBlock3Fun]; split_ifs <;> first | exact hbi | rfl
      have hinu : nu n b ≤ i := by
        by_contra hlt
        have := hnumin i (by omega) (by omega)
        rw [this] at hbi; contradiction
      rw [GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
      rcases eq_or_lt_of_le hinu with rfl | higt
      · linarith
      · have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (by omega : 1 ≤ nu n b) higt hin hbi
        linarith
  exact ⟨hva, hg1, hbp, hcp, hcn, hc_no⟩

lemma even_block3_step {n b k m : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    {s : MDPState n} (hs : StateAt n (evenBlock3Fun n b k) m s)
    (hm1 : 4 * n - 5 + 2 * (nu n b - 2) ≤ m) (hm2 : m ≤ 6 * n - 7 + (k - 2)) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      4 * n - 5 + 2 * (nu n b - 2) ≤ m' ∧ m' ≤ 6 * n - 7 + (k - 1) ∧
      StateAt n (evenBlock3Fun n b (k + 1)) m' s' := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, _, _⟩
  cases hbk : b.testBit (k - 1)
  · rcases evenBlock3_vals (k := k) hn heven hbpos hb hk2 (by omega) with
      ⟨hva, _, hbp, _, hcn, hc_no⟩
    set f := evenBlock3Fun n b k
    set V := policyValue n hn (policyOf n f)
    have hv₀ : ValidRow n (.e, k) := ⟨by omega, hkn⟩
    have hfd : f .d k = false := hbk
    have hf₀ : f .e k = true := by dsimp [f, evenBlock3Fun]; rw [if_neg (by omega)]
    have hrank : columnRank n ⟨.e, k, !f .e k⟩ = 6 * n - 7 + (k - 1) := by
      rw [hf₀, Bool.not_true, columnRank_e_false]
    have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.e, k) hv₀) := by
      rw [mdpImproving_e_iff hn f hv₀ hk2, hf₀, if_pos rfl, hcn]
      have hFG := FRhs_GRhs_of_de_false_true_Gm (b' := b) (b := b) (m := 1) (i := k)
        hn f hk2 hkn (le_refl 1) (by omega) hfd hf₀ (hva (k + 1) (by omega)) (hbp k hk2 hkn)
      have habs := (abs_lt.mp hFG.1).2
      linarith
    have hno : ∀ kind i (hv : ValidRow n (kind, i)),
        m < columnRank n ⟨kind, i, !f kind i⟩ →
        columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.e, k, !f .e k⟩ →
        mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
      intro kind i hv hgt hlt
      rw [hrank] at hlt
      cases kind
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfa : f .a i <;> rw [hfa] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n - 1 := hv
        have hfb : f .b i = false := rfl
        rw [hfb] at hgt
        simp only [Bool.not_false, columnRank_b_true] at hgt; omega
      · exact hc_no i hv
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfdi : f .d i <;> rw [hfdi] at hgt hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hgt hlt <;>
          omega
      · have hi1 : 1 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        cases hfei : f .e i <;> rw [hfei] at hgt hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hgt hlt
        · split_ifs at hgt <;> omega
        · rcases eq_or_lt_of_le hi1 with rfl | hi2_lt
          · rw [mdpStrictNonImproving_e_one_iff hn f, hfei, if_pos rfl, hcn]
            unfold HVal; rw [hva 2 (le_refl 2)]
            have hrg1 : rewardG n 1 ≤ -7 := by
              rw [rewardG_eq (le_refl 1), pow_one]
              have := scale_ge_seven hn
              linarith
            unfold Gm
            linarith
          · have hi2 : 2 ≤ i := by omega
            have hik_lt : i < k := by omega
            have hbi : b.testBit (i - 1) = true := by
              dsimp [f, evenBlock3Fun] at hfei; rw [if_pos ⟨hi2, hik_lt⟩] at hfei; exact hfei
            have hfdi : f .d i = true := hbi
            rw [mdpStrictNonImproving_e_iff hn f hv hi2, hfei, if_pos rfl, hcn,
              FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfdi hfei (hva (i + 1) (by omega))]
            have := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ i) hin
            linarith
    have hup : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .e ∧ i = k then !f .e k else f kind i) = evenBlock3Fun n b (k + 1) kind i := by
      intro kind i _
      by_cases h : kind = .e ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hf₀]
        dsimp [evenBlock3Fun]; rw [if_pos ⟨hk2, by omega⟩, hbk]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [f, evenBlock3Fun]
        have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
        by_cases h1 : 2 ≤ i ∧ i < k
        · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs .e k hv₀ (by rw [hrank]; omega) himp hno hup with
      ⟨s', hp, hs'⟩
    rw [hrank] at hs'
    exact ⟨1, s', 6 * n - 7 + (k - 1), hp, by omega, le_refl _, hs'⟩
  · have hfeq : evenBlock3Fun n b (k + 1) = evenBlock3Fun n b k := by
      funext kind i
      cases kind <;> dsimp [evenBlock3Fun]
      by_cases hi : i = k
      · subst hi; rw [if_pos ⟨hk2, by omega⟩, if_neg (by omega), hbk]
      · by_cases h1 : 2 ≤ i ∧ i < k
        · rw [if_pos ⟨h1.1, by omega⟩, if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
    refine ⟨0, s, m, MdpPath.refl s, hm1, by omega, ?_⟩
    rw [hfeq]; exact hs

lemma even_block3_loop {n b : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    {m : ℕ} {s : MDPState n} (hs : StateAt n (evenBlock3Fun n b k) m s)
    (hm1 : 4 * n - 5 + 2 * (nu n b - 2) ≤ m) (hm2 : m ≤ 6 * n - 7 + (k - 2)) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      4 * n - 5 + 2 * (nu n b - 2) ≤ m' ∧ m' ≤ 7 * n - 8 ∧
      StateAt n (evenBlock3Fun n b (n + 1)) m' s' := by
  by_cases hlt : k ≤ n
  · rcases even_block3_step hn heven hbpos hb hk2 hlt hs hm1 hm2 with
      ⟨t₁, s₁, m₁, hp₁, hm₁1, hm₁2, hs₁⟩
    rcases even_block3_loop hn heven hbpos hb (k + 1) (by omega) (by omega) hs₁ hm₁1
      (by rw [show k + 1 - 2 = k - 1 by omega]; exact hm₁2) with
      ⟨t₂, s₂, m₂, hp₂, hm₂1, hm₂2, hs₂⟩
    exact ⟨t₁ + t₂, s₂, m₂, hp₁.trans hp₂, hm₂1, hm₂2, hs₂⟩
  · have hk_eq : k = n + 1 := by omega
    subst hk_eq
    exact ⟨0, s, m, MdpPath.refl s, hm1, by omega, hs⟩
termination_by (n + 1) - k
decreasing_by omega

def evenBlock4Fun (_n b k : ℕ) : Kind → ℕ → Bool
  | .a, i => b.testBit (i - 1)
  | .b, _ => false
  | .c, _ => false
  | .d, i => if 2 ≤ i ∧ i < k then true else b.testBit (i - 1)
  | .e, i => if i = 1 then true else b.testBit (i - 1)

lemma evenBlock4_vals {n b k : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (_hk2 : 2 ≤ k) (_hkn : k ≤ n + 1) :
    let f := evenBlock4Fun n b k
    let V := policyValue n hn (policyOf n f)
    (∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i) ∧
    G1Val n hn V = Gm n b 1 ∧
    (∀ i, 2 ≤ i → i ≤ n → BPrev n hn V i = Gm n b 1) ∧
    (∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1) ∧
    valAt n hn V .c n = Gm n b 1 ∧
    (∀ i (hv : ValidRow n (.c, i)), mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.c, i) hv)) := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, hnubit, hnumin⟩
  have hnu_lt_g1 := Gm_nu_lt_Gm_one_of_even hn heven hbpos hb
  intro f V
  have hva : ∀ i, 2 ≤ i → valAt n hn V .a i = vaBase n b i := by
    intro i hi2
    exact valAt_a_eq_vaBase hn f b i hi2 (fun _ _ _ => rfl)
      (fun j hj2 _ hbj => by
        dsimp [f, evenBlock4Fun]
        exact ⟨by split_ifs <;> first | rfl | exact hbj, by rw [if_neg (by omega), hbj]⟩)
  have he1 : f .e 1 = true := rfl
  have hg1 : G1Val n hn V = Gm n b 1 := by
    rw [G1Val_of_e_one_true hn f he1, hva 2 (le_refl 2)]; rfl
  have hbp : ∀ i, 2 ≤ i → i ≤ n → BPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin
    rw [BPrev_eq_G1Val hn f i hi2 hin (fun _ _ _ => rfl), hg1]
  have hcp : ∀ i, 2 ≤ i → i ≤ n → CPrev n hn V i = Gm n b 1 := by
    intro i hi2 hin
    rw [CPrev_eq_G1Val hn f i hi2 hin (fun _ _ _ => rfl), hg1]
  have hcn : valAt n hn V .c n = Gm n b 1 := by
    rw [valAt_c_n_eq_G1Val hn f (fun _ _ _ => rfl), hg1]
  have hc_no : ∀ i (hv : ValidRow n (.c, i)),
      mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (.c, i) hv) := by
    intro i hv
    have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    have hfc : f .c i = false := rfl
    rw [mdpStrictNonImproving_c_iff hn f hv, hfc, if_neg (by decide), hcp i hi2 hin]
    have hfe : f .e i = b.testBit (i - 1) := by dsimp [f, evenBlock4Fun]; rw [if_neg (by omega)]
    cases hbi : b.testBit (i - 1)
    · rw [hbi] at hfe
      cases hfd : f .d i
      · have hH := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ i) hin
        have hFG := FRhs_GRhs_of_de_false_false_same_Gm (b' := b) (b := b) (m := 1) (i := i)
          hn f hi2 hin (le_refl 1) (by omega) hfd hfe (hva (i + 1) (by omega))
          (hbp i hi2 hin) hcn (by linarith)
        linarith [hFG.2.2]
      · have hFG := FRhs_GRhs_of_de_true_false_Gm (b' := b) (b := b) (m := 1) (i := i)
          hn f hi2 hin (le_refl 1) (by omega) hfd hfe (hva (i + 1) (by omega)) hcn
        linarith [hFG.2.2.2]
    · rw [hbi] at hfe
      have hfd : f .d i = true := by
        dsimp [f, evenBlock4Fun]; split_ifs <;> first | rfl | exact hbi
      have hinu : nu n b ≤ i := by
        by_contra hlt
        have := hnumin i (by omega) (by omega)
        rw [this] at hbi; contradiction
      rw [GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
      rcases eq_or_lt_of_le hinu with rfl | higt
      · linarith
      · have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (by omega : 1 ≤ nu n b) higt hin hbi
        linarith
  exact ⟨hva, hg1, hbp, hcp, hcn, hc_no⟩

lemma even_block4_step {n b k m : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    {s : MDPState n} (hs : StateAt n (evenBlock4Fun n b k) m s)
    (hm1 : 4 * n - 5 + 2 * (nu n b - 2) ≤ m) (hm2 : m + 1 ≤ 7 * n - 7 + (k - 2)) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      4 * n - 5 + 2 * (nu n b - 2) ≤ m' ∧ m' + 1 ≤ 7 * n - 7 + (k - 1) ∧
      (7 * n - 7 ≤ m ∨ b.testBit (k - 1) = false → 7 * n - 7 ≤ m') ∧
      StateAt n (evenBlock4Fun n b (k + 1)) m' s' := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, _, _⟩
  cases hbk : b.testBit (k - 1)
  · rcases evenBlock4_vals (k := k) hn heven hbpos hb hk2 (by omega) with
      ⟨hva, _, hbp, _, hcn, hc_no⟩
    set f := evenBlock4Fun n b k
    set V := policyValue n hn (policyOf n f)
    have hv₀ : ValidRow n (.d, k) := ⟨hk2, hkn⟩
    have hf₀ : f .d k = false := by dsimp [f, evenBlock4Fun]; rw [if_neg (by omega), hbk]
    have hfe₀ : f .e k = false := by dsimp [f, evenBlock4Fun]; rw [if_neg (by omega), hbk]
    have hrank : columnRank n ⟨.d, k, !f .d k⟩ = 7 * n - 7 + (k - 2) := by
      rw [hf₀, Bool.not_false, columnRank_d_true]
    have himp : mdpImproving n hn (policyOf n f) (mkRow n hn (.d, k) hv₀) := by
      rw [mdpImproving_d_iff hn f hv₀, hf₀, if_neg (by decide), hbp k hk2 hkn]
      have hH := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ k) hkn
      have hFG := FRhs_GRhs_of_de_false_false_same_Gm (b' := b) (b := b) (m := 1) (i := k)
        hn f hk2 hkn (le_refl 1) (by omega) hf₀ hfe₀ (hva (k + 1) (by omega))
        (hbp k hk2 hkn) hcn (by linarith)
      exact hFG.1
    have hno : ∀ kind i (hv : ValidRow n (kind, i)),
        m < columnRank n ⟨kind, i, !f kind i⟩ →
        columnRank n ⟨kind, i, !f kind i⟩ < columnRank n ⟨.d, k, !f .d k⟩ →
        mdpStrictNonImproving n hn (policyOf n f) (mkRow n hn (kind, i) hv) := by
      intro kind i hv hgt hlt
      rw [hrank] at hlt
      cases kind
      · have : 2 ≤ i ∧ i ≤ n := hv
        cases hfa : f .a i <;> rw [hfa] at hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_a_true, columnRank_a_false] at hlt <;>
          omega
      · have : 2 ≤ i ∧ i ≤ n - 1 := hv
        have hfb : f .b i = false := rfl
        rw [hfb] at hgt
        simp only [Bool.not_false, columnRank_b_true] at hgt; omega
      · exact hc_no i hv
      · have hi2 : 2 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        cases hfdi : f .d i <;> rw [hfdi] at hgt hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_d_true, columnRank_d_false] at hgt hlt
        · have hik_le : k ≤ i := by
            by_contra hlt'
            have : f .d i = true := by dsimp [f, evenBlock4Fun]; rw [if_pos ⟨hi2, by omega⟩]
            rw [this] at hfdi; contradiction
          omega
        · omega
      · have hi1 : 1 ≤ i := hv.1
        have hin : i ≤ n := hv.2
        cases hfei : f .e i <;> rw [hfei] at hgt hlt <;>
          simp only [Bool.not_true, Bool.not_false, columnRank_e_true, columnRank_e_false] at hgt hlt
        · split_ifs at hgt <;> omega
        · rcases eq_or_lt_of_le hi1 with rfl | hi2_lt
          · rw [mdpStrictNonImproving_e_one_iff hn f, hfei, if_pos rfl, hcn]
            unfold HVal; rw [hva 2 (le_refl 2)]
            have hrg1 : rewardG n 1 ≤ -7 := by
              rw [rewardG_eq (le_refl 1), pow_one]
              have := scale_ge_seven hn
              linarith
            unfold Gm
            linarith
          · have hi2 : 2 ≤ i := by omega
            have hbi : b.testBit (i - 1) = true := by
              dsimp [f, evenBlock4Fun] at hfei; rw [if_neg (by omega)] at hfei; exact hfei
            have hfdi : f .d i = true := by
              dsimp [f, evenBlock4Fun]; split_ifs <;> first | rfl | exact hbi
            rw [mdpStrictNonImproving_e_iff hn f hv hi2, hfei, if_pos rfl, hcn,
              FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfdi hfei (hva (i + 1) (by omega))]
            have := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ i) hin
            linarith
    have hup : ∀ kind i, ValidRow n (kind, i) →
        (if kind = .d ∧ i = k then !f .d k else f kind i) = evenBlock4Fun n b (k + 1) kind i := by
      intro kind i _
      by_cases h : kind = .d ∧ i = k
      · rcases h with ⟨rfl, rfl⟩
        rw [if_pos ⟨rfl, rfl⟩, hf₀]
        dsimp [evenBlock4Fun]; rw [if_pos ⟨hk2, by omega⟩]; rfl
      · rw [if_neg h]
        cases kind <;> dsimp [f, evenBlock4Fun]
        have hi : i ≠ k := fun heq => h ⟨rfl, heq⟩
        by_cases h1 : 2 ≤ i ∧ i < k
        · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
    rcases step_stateAt_of_le hn hs .d k hv₀ (by rw [hrank]; omega) himp hno hup with
      ⟨s', hp, hs'⟩
    rw [hrank] at hs'
    exact ⟨1, s', 7 * n - 7 + (k - 2), hp, by omega, by omega, fun _ => by omega, hs'⟩
  · have hfeq : evenBlock4Fun n b (k + 1) = evenBlock4Fun n b k := by
      funext kind i
      cases kind <;> dsimp [evenBlock4Fun]
      by_cases hi : i = k
      · subst hi; rw [if_pos ⟨hk2, by omega⟩, if_neg (by omega), hbk]
      · by_cases h1 : 2 ≤ i ∧ i < k
        · rw [if_pos ⟨h1.1, by omega⟩, if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
    refine ⟨0, s, m, MdpPath.refl s, hm1, by omega, ?_, ?_⟩
    · intro hor; rcases hor with h1 | h2; exact h1; contradiction
    · rw [hfeq]; exact hs

lemma even_block4_loop {n b : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    {m : ℕ} {s : MDPState n} (hs : StateAt n (evenBlock4Fun n b k) m s)
    (hm1 : 4 * n - 5 + 2 * (nu n b - 2) ≤ m) (hm2 : m + 1 ≤ 7 * n - 7 + (k - 2)) :
    ∃ t s' m', MdpPath n hn t s s' ∧
      m' < 8 * n - 8 ∧
      (7 * n - 7 ≤ m ∨ (∃ j, k ≤ j ∧ j ≤ n ∧ b.testBit (j - 1) = false) → 7 * n - 7 ≤ m') ∧
      StateAt n (evenBlock4Fun n b (n + 1)) m' s' := by
  by_cases hlt : k ≤ n
  · rcases even_block4_step hn heven hbpos hb hk2 hlt hs hm1 hm2 with
      ⟨t₁, s₁, m₁, hp₁, hm₁1, hm₁2, hm₁_ge, hs₁⟩
    rcases even_block4_loop hn heven hbpos hb (k + 1) (by omega) (by omega) hs₁ hm₁1
      (by rw [show k + 1 - 2 = k - 1 by omega]; exact hm₁2) with
      ⟨t₂, s₂, m₂, hp₂, hm₂_lt, hm₂_ge, hs₂⟩
    refine ⟨t₁ + t₂, s₂, m₂, hp₁.trans hp₂, hm₂_lt, ?_, hs₂⟩
    intro hor
    apply hm₂_ge
    rcases hor with hm_ge | ⟨j, hkj, hjn, hbj⟩
    · exact Or.inl (hm₁_ge (Or.inl hm_ge))
    · rcases eq_or_lt_of_le hkj with rfl | hkj_lt
      · exact Or.inl (hm₁_ge (Or.inr hbj))
      · exact Or.inr ⟨j, by omega, hjn, hbj⟩
  · have hk_eq : k = n + 1 := by omega
    subst hk_eq
    refine ⟨0, s, m, MdpPath.refl s, by omega, ?_, hs⟩
    intro hor
    rcases hor with hm_ge | ⟨j, hkj, hjn, _⟩
    · exact hm_ge
    · omega
termination_by (n + 1) - k
decreasing_by omega

lemma even_sweep {n b m₀ : ℕ} (hn : 3 ≤ n) (heven : b % 2 = 0) (hbpos : 0 < b)
    (hb : b < 2 ^ n) (hm₀1 : 10 * n - 12 ≤ m₀) (hm₀2 : m₀ < 10 * n - 10)
    {s₀ : MDPState n} (hs₀ : StateAt n (counterFun n b) m₀ s₀) :
    ∃ t s' m', 2 ≤ t ∧ MdpPath n hn t s₀ s' ∧
      (b < 2 ^ n - 2 → 7 * n - 7 ≤ m' ∧ m' < 8 * n - 8) ∧
      StateAt n (counterFun n (b + 1)) m' s' := by
  rcases nu_spec hn heven hbpos hb with ⟨hnu2, hnun, _, _⟩
  rcases even_succ_bits heven with ⟨hsucc0, hsucc_gt⟩
  rcases even_step_e_one hn heven hbpos hb hm₀1 hm₀2 hs₀ with ⟨s₁, hp₁, hs₁⟩
  rcases even_block1_loop hn heven hbpos hb 2 (le_refl 2) (by omega) hs₁ (by omega) (by omega) with
    ⟨t₂, s₂, m₂, hp₂, hm₂, hs₂⟩
  rcases even_block2_step hn heven hbpos hb hs₂ hm₂ with ⟨s₃, hp₃, hs₃⟩
  rcases even_block3_loop hn heven hbpos hb 2 (le_refl 2) (by omega) hs₃ (le_refl _) (by omega) with
    ⟨t₄, s₄, m₄, hp₄, hm₄1, hm₄2, hs₄⟩
  have hfeq34 : ∀ k i, ValidRow n (k, i) →
      evenBlock3Fun n b (n + 1) k i = evenBlock4Fun n b 2 k i := by
    intro k i hv
    cases k <;> dsimp [evenBlock3Fun, evenBlock4Fun, ValidRow] at hv ⊢
    · rw [if_neg (by omega)]
    · by_cases hi1 : i = 1
      · subst hi1; rw [if_neg (by omega), if_pos rfl]
      · rw [if_pos ⟨by omega, by omega⟩, if_neg hi1]
  rcases hs₄ with ⟨hspol₄, hslast₄, k₄, i₄, hv₄, hrank₄⟩
  have hs₄' : StateAt n (evenBlock4Fun n b 2) m₄ s₄ := by
    refine ⟨?_, hslast₄, k₄, i₄, hv₄, ?_⟩
    · rw [hspol₄]; exact policyOf_ext hn hfeq34
    · rw [hrank₄, hfeq34 k₄ i₄ hv₄]
  rcases even_block4_loop hn heven hbpos hb 2 (le_refl 2) (by omega) hs₄' hm₄1 (by omega) with
    ⟨t₅, s₅, m₅, hp₅, hm₅_lt, hm₅_ge, hs₅⟩
  have hfeq4c : ∀ k i, ValidRow n (k, i) →
      evenBlock4Fun n b (n + 1) k i = counterFun n (b + 1) k i := by
    intro k i hv
    cases k <;> unfold evenBlock4Fun counterFun <;> dsimp [ValidRow] at hv ⊢
    · exact (hsucc_gt i hv.1).symm
    · rw [if_pos hsucc0]
    · rw [if_pos hsucc0]
    · rw [if_pos ⟨hv.1, by omega⟩]
    · by_cases hi1 : i = 1
      · subst hi1; rw [if_pos rfl, hsucc0]
      · rw [if_neg hi1]; exact (hsucc_gt i (by omega)).symm
  rcases hs₅ with ⟨hspol₅, hslast₅, k₅, i₅, hv₅, hrank₅⟩
  have hs₅' : StateAt n (counterFun n (b + 1)) m₅ s₅ := by
    refine ⟨?_, hslast₅, k₅, i₅, hv₅, ?_⟩
    · rw [hspol₅]; exact policyOf_ext hn hfeq4c
    · rw [hrank₅, hfeq4c k₅ i₅ hv₅]
  refine ⟨1 + t₂ + 1 + t₄ + t₅, s₅, m₅, by omega, ?_, ?_, hs₅'⟩
  · exact (((hp₁.trans hp₂).trans hp₃).trans hp₄).trans hp₅
  · intro hblt
    have hodd_succ : (b + 1) % 2 = 1 := by omega
    have hb_succ : b + 1 < 2 ^ n - 1 := by omega
    rcases mu_spec hn hodd_succ hb_succ with ⟨hmu2, hmun, hmubit, _⟩
    rw [hsucc_gt (mu n (b + 1)) hmu2] at hmubit
    exact ⟨hm₅_ge (Or.inr ⟨mu n (b + 1), hmu2, hmun, hmubit⟩), hm₅_lt⟩

/-! ### Part 7: Terminal Optimality and Full Exponential Run -/

lemma two_pow_ge_eight {n : ℕ} (hn : 3 ≤ n) : 8 ≤ 2 ^ n := by
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  omega

lemma two_pow_sub_one_odd {n : ℕ} (hn : 3 ≤ n) : (2 ^ n - 1) % 2 = 1 := by
  have hdiv : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  rcases hdiv with ⟨k, hk⟩
  have h8 := two_pow_ge_eight hn
  omega

lemma terminal_nonImproving {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) :
    mdpStrictNonImproving n hn (policyOf n (counterFun n (2 ^ n - 1))) r := by
  have hodd : (2 ^ n - 1) % 2 = 1 := two_pow_sub_one_odd hn
  have hb0 : (2 ^ n - 1).testBit 0 = true := by
    rw [Nat.testBit_zero]; exact decide_eq_true hodd
  have hbit : ∀ i, 1 ≤ i → i ≤ n → (2 ^ n - 1).testBit (i - 1) = true := by
    intro i _ hin
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (by omega)
  rcases counterFun_odd_vals hn hodd with ⟨hva, _, hbp, hcp, hcn⟩
  set b := 2 ^ n - 1
  set f := counterFun n b
  set V := policyValue n hn (policyOf n f)
  rw [← mkRow_rowName hn r]
  generalize rowName_valid hn r = hv
  revert hv
  rcases rowName n r with ⟨k, i⟩
  intro hv
  cases k
  · have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    have hbi : b.testBit (i - 1) = true := hbit i (by omega) hin
    have hfa : f .a i = true := hbi
    have hfd : f .d i = true := rfl
    have hfe : f .e i = true := hbi
    rw [mdpStrictNonImproving_a_iff hn f hv, hfa, if_pos rfl, hva (i + 1) (by omega),
      GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
    unfold Gm
    have := rewardGH_ge_42 (n := n) hn (by omega : 1 ≤ i)
    linarith
  · have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n - 1 := hv.2
    have hbi : b.testBit (i - 1) = true := hbit i (by omega) (by omega)
    have hfb : f .b i = false := by unfold f counterFun; dsimp only; rw [if_pos hb0]
    have hfd : f .d i = true := rfl
    have hfe : f .e i = true := hbi
    rw [mdpStrictNonImproving_b_iff hn f hv, hfb, if_neg (by decide), hbp i hi2 (by omega),
      GRhs_eq_Gm_of_de_true_true hn f hi2 (by omega) hfd hfe (hva (i + 1) (by omega))]
    have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (le_refl 1) (by omega : 1 < i) (by omega) hbi
    linarith
  · have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    have hbi : b.testBit (i - 1) = true := hbit i (by omega) hin
    have hfc : f .c i = false := by unfold f counterFun; dsimp only; rw [if_pos hb0]
    have hfd : f .d i = true := rfl
    have hfe : f .e i = true := hbi
    rw [mdpStrictNonImproving_c_iff hn f hv, hfc, if_neg (by decide), hcp i hi2 hin,
      GRhs_eq_Gm_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
    have := Gm_lt_Gm_of_lt_of_testBit (b := b) hn (le_refl 1) (by omega : 1 < i) hin hbi
    linarith
  · have hi2 : 2 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    have hbi : b.testBit (i - 1) = true := hbit i (by omega) hin
    have hfd : f .d i = true := rfl
    have hfe : f .e i = true := hbi
    rw [mdpStrictNonImproving_d_iff hn f hv, hfd, if_pos rfl, hbp i hi2 hin,
      FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
    have := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ i) hin
    linarith
  · have hi1 : 1 ≤ i := hv.1
    have hin : i ≤ n := hv.2
    have hbi : b.testBit (i - 1) = true := hbit i hi1 hin
    have hfe : f .e i = true := hbi
    rcases eq_or_lt_of_le hi1 with rfl | hi2_lt
    · rw [mdpStrictNonImproving_e_one_iff hn f, hfe, if_pos rfl, hcn]
      unfold HVal; rw [hva 2 (le_refl 2)]
      have hrg1 : rewardG n 1 ≤ -7 := by
        rw [rewardG_eq (le_refl 1), pow_one]
        have := scale_ge_seven hn
        linarith
      unfold Gm
      linarith
    · have hi2 : 2 ≤ i := by omega
      have hfd : f .d i = true := rfl
      rw [mdpStrictNonImproving_e_iff hn f hv hi2, hfe, if_pos rfl, hcn,
        FRhs_eq_HVal_of_de_true_true hn f hi2 hin hfd hfe (hva (i + 1) (by omega))]
      have := HVal_gt_Gm (b := b) hn (le_refl 1) (by omega : 1 ≤ i) hin
      linarith

lemma double_sweep_loop {n : ℕ} (hn : 3 ≤ n) (p : ℕ) (hp : 2 * p + 1 ≤ 2 ^ n - 3) :
    ∃ t s m, 4 * p ≤ t ∧
      MdpPath n hn t (initialMDPState n hn) s ∧
      (m = 0 ∨ (7 * n - 7 ≤ m ∧ m < 8 * n - 8)) ∧
      StateAt n (counterFun n (2 * p + 1)) m s := by
  induction p with
  | zero =>
    exact ⟨0, initialMDPState n hn, 0, le_refl 0, MdpPath.refl _, Or.inl rfl,
      initialMDPState_stateAt hn⟩
  | succ p ih =>
    rcases ih (by omega) with ⟨t₀, s₀, m₀, ht₀, hp₀, hm₀, hs₀⟩
    have hodd : (2 * p + 1) % 2 = 1 := by omega
    have hblt : 2 * p + 1 < 2 ^ n - 1 := by omega
    rcases odd_sweep hn hodd hblt hs₀ hm₀ with ⟨t₁, s₁, m₁, ht₁, hp₁, hm₁1, hm₁2, hs₁⟩
    have heven : (2 * p + 1 + 1) % 2 = 0 := by omega
    have hbpos : 0 < 2 * p + 1 + 1 := by omega
    have hblt2 : 2 * p + 1 + 1 < 2 ^ n := by omega
    rcases even_sweep hn heven hbpos hblt2 hm₁1 hm₁2 hs₁ with
      ⟨t₂, s₂, m₂, ht₂, hp₂, hm₂_cond, hs₂⟩
    have hm₂ : 7 * n - 7 ≤ m₂ ∧ m₂ < 8 * n - 8 := hm₂_cond (by omega)
    refine ⟨t₀ + t₁ + t₂, s₂, m₂, by omega, (hp₀.trans hp₁).trans hp₂, Or.inr hm₂, ?_⟩
    rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by omega]
    exact hs₂

theorem mdp_lower_bound_strict (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → MDPState n),
      s 0 = initialMDPState n hn ∧
      (∀ t < T, mdpStrictStep n hn (s t) (s (t + 1))) ∧
      (∀ r : Fin (rows n), mdpStrictNonImproving n hn (s T).policy r) ∧
      2 ^ n ≤ T := by
  have h8 := two_pow_ge_eight hn
  have hdiv : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  rcases hdiv with ⟨half, hhalf⟩
  have hhalf_ge : 4 ≤ half := by omega
  set p := half - 2
  have hp : 2 * p + 1 ≤ 2 ^ n - 3 := by omega
  have hp_eq : 2 * p + 1 = 2 ^ n - 3 := by omega
  rcases double_sweep_loop hn p hp with ⟨t₀, s₀, m₀, ht₀, hp₀, hm₀, hs₀⟩
  rw [hp_eq] at hs₀
  have hodd : (2 ^ n - 3) % 2 = 1 := by omega
  have hblt : 2 ^ n - 3 < 2 ^ n - 1 := by omega
  rcases odd_sweep hn hodd hblt hs₀ hm₀ with ⟨t₁, s₁, m₁, ht₁, hp₁, hm₁1, hm₁2, hs₁⟩
  rw [show 2 ^ n - 3 + 1 = 2 ^ n - 2 by omega] at hs₁
  have heven : (2 ^ n - 2) % 2 = 0 := by omega
  have hbpos : 0 < 2 ^ n - 2 := by omega
  have hblt2 : 2 ^ n - 2 < 2 ^ n := by omega
  rcases even_sweep hn heven hbpos hblt2 hm₁1 hm₁2 hs₁ with
    ⟨t₂, s₂, m₂, ht₂, hp₂, _, hs₂⟩
  rw [show 2 ^ n - 2 + 1 = 2 ^ n - 1 by omega] at hs₂
  have hpath := (hp₀.trans hp₁).trans hp₂
  have hterm : ∀ r : Fin (rows n), mdpStrictNonImproving n hn s₂.policy r := by
    intro r
    rw [hs₂.1]
    exact terminal_nonImproving hn r
  rcases mdpStrictRun_of_mdpPath hpath hterm with ⟨s, hs0, hstep, hsterm⟩
  exact ⟨t₀ + t₁ + t₂, s, hs0, hstep, hsterm, by omega⟩

theorem mdp_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → MDPState n), mdpRun n hn s T ∧ 2 ^ n ≤ T := by
  rcases mdp_lower_bound_strict n hn with ⟨T, s, hs0, hstep, hterm, hT⟩
  exact ⟨T, s, ⟨hs0, fun t ht => mdpStep_of_strictStep (hstep t ht),
    fun r => not_mdpImproving_of_strict (hterm r)⟩, hT⟩

end FriedmannCunningham

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → FriedmannCunningham.MDPState n),
      FriedmannCunningham.mdpRun n hn s T ∧ 2 ^ n ≤ T :=
  FriedmannCunningham.mdp_lower_bound n hn





