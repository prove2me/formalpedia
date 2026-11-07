-- Prove2me | solution 1 for FriedmannCunningham.lp_valid
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:21:46.388054+00:00
-- url     : https://prove2.me/submissions/09e06788-21a2-40f8-a277-2799d3a235bf

import Definitions.Def_friedmann_cunningham
import Theorems.Thm_FriedmannCunningham_mdp_valid
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

/-! ### Part 1: Row and Column Roundtrip Infrastructure -/

def ValidRow (n : ℕ) (p : Kind × ℕ) : Prop :=
  match p.1 with
  | .a => 2 ≤ p.2 ∧ p.2 ≤ n
  | .b => 2 ≤ p.2 ∧ p.2 ≤ n - 1
  | .c => 2 ≤ p.2 ∧ p.2 ≤ n
  | .d => 2 ≤ p.2 ∧ p.2 ≤ n
  | .e => 1 ≤ p.2 ∧ p.2 ≤ n

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
  have hlt : columnRank n ⟨k, i, b⟩ < cols n := by
    cases k <;> cases b <;> dsimp [ValidRow, columnRank, cols] at hp ⊢ <;>
      (try split_ifs) <;> omega
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

lemma policyBasis_injective (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    Function.Injective (policyBasis n hn σ) :=
  fun _ _ h => (actionColumn_inj hn h).1

lemma exists_actionColumn (n : ℕ) (hn : 3 ≤ n) (j : Fin (cols n)) :
    ∃ (r : Fin (rows n)) (b : Bool), actionColumn n hn r b = j := by
  let f : Fin (rows n) × Bool → Fin (cols n) := fun p => actionColumn n hn p.1 p.2
  have hinj : Function.Injective f := by
    rintro ⟨r₁, b₁⟩ ⟨r₂, b₂⟩ h
    rcases actionColumn_inj hn h with ⟨rfl, rfl⟩
    rfl
  have hcard : Fintype.card (Fin (rows n) × Bool) = Fintype.card (Fin (cols n)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]
    unfold rows cols
    omega
  have hbij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  rcases hbij.2 j with ⟨⟨r, b⟩, hr⟩
  exact ⟨r, b, hr⟩

/-! ### Part 2: Explicit Transition Formula and Outgoing Transitions -/

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

lemma valid_a_two {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.a, 2) := by
  dsimp [ValidRow]; omega

lemma valid_e_one {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.e, 1) := by
  dsimp [ValidRow]; omega

lemma valid_c_n {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.c, n) := by
  dsimp [ValidRow]; omega

lemma valid_d_n {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.d, n) := by
  dsimp [ValidRow]; omega

lemma valid_e_n {n : ℕ} (hn : 3 ≤ n) : ValidRow n (.e, n) := by
  dsimp [ValidRow]; omega

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

/-! ### Part 3: Strictly Positive Basic Values via Maximum Principle -/

lemma lt_of_eq_zero {n : ℕ} {f : Fin (rows n) → ℚ} {z : Fin (rows n) → ℚ}
    {M : ℚ} (hf : ∀ q, f q = 0) (hMpos : 0 < M) :
    ∑ q, f q * z q < M := by
  simp [hf, hMpos]

lemma lt_of_eq_ite_one {n : ℕ} {f : Fin (rows n) → ℚ} {z : Fin (rows n) → ℚ}
    {q₁ : Fin (rows n)} {M : ℚ}
    (hf : ∀ q, f q = if q = q₁ then 1 else 0)
    (hq₁ : z q₁ < M) :
    ∑ q, f q * z q < M := by
  simp only [hf, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact hq₁

lemma lt_of_eq_ite_two_half {n : ℕ} (hn : 3 ≤ n) {f : Fin (rows n) → ℚ} {z : Fin (rows n) → ℚ}
    {q₁ q₂ : Fin (rows n)} {M : ℚ}
    (hf : ∀ q, f q = (if q = q₁ then (1 - epsilon n) / 2 else 0) +
                     (if q = q₂ then (1 - epsilon n) / 2 else 0))
    (hM : ∀ q, z q ≤ M) (hMpos : 0 < M) :
    ∑ q, f q * z q < M := by
  simp only [hf, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have heps : 0 < epsilon n := epsilon_pos n
  have heps1 : epsilon n < 1 := epsilon_lt_one hn
  have hpos : 0 < (1 - epsilon n) / 2 := by linarith
  have hm1 : (1 - epsilon n) / 2 * z q₁ ≤ (1 - epsilon n) / 2 * M :=
    mul_le_mul_of_nonneg_left (hM q₁) (le_of_lt hpos)
  have hm2 : (1 - epsilon n) / 2 * z q₂ ≤ (1 - epsilon n) / 2 * M :=
    mul_le_mul_of_nonneg_left (hM q₂) (le_of_lt hpos)
  have hm3 : epsilon n * 0 < epsilon n * M := mul_lt_mul_of_pos_left hMpos heps
  linarith

lemma lt_of_eq_ite_eps {n : ℕ} (hn : 3 ≤ n) {f : Fin (rows n) → ℚ} {z : Fin (rows n) → ℚ}
    {q₁ q₂ : Fin (rows n)} {M : ℚ}
    (hf : ∀ q, f q = (if q = q₁ then epsilon n else 0) +
                     (if q = q₂ then 1 - epsilon n else 0))
    (hM : ∀ q, z q ≤ M) (hq₁ : z q₁ < M) :
    ∑ q, f q * z q < M := by
  simp only [hf, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have heps : 0 < epsilon n := epsilon_pos n
  have heps1 : 0 < 1 - epsilon n := sub_pos.mpr (epsilon_lt_one hn)
  have hm1 : epsilon n * z q₁ < epsilon n * M :=
    mul_lt_mul_of_pos_left hq₁ heps
  have hm2 : (1 - epsilon n) * z q₂ ≤ (1 - epsilon n) * M :=
    mul_le_mul_of_nonneg_left (hM q₂) (le_of_lt heps1)
  linarith

lemma lt_of_eq_ite_three {n : ℕ} (hn : 3 ≤ n) {f : Fin (rows n) → ℚ} {z : Fin (rows n) → ℚ}
    {q₁ q₂ q₃ : Fin (rows n)} {M : ℚ}
    (hf : ∀ q, f q = (if q = q₁ then epsilon n else 0) +
                     (if q = q₂ then (1 - epsilon n) / 2 else 0) +
                     (if q = q₃ then (1 - epsilon n) / 2 else 0))
    (hM : ∀ q, z q ≤ M) (hq₁ : z q₁ < M) :
    ∑ q, f q * z q < M := by
  simp only [hf, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have heps : 0 < epsilon n := epsilon_pos n
  have heps1 : epsilon n < 1 := epsilon_lt_one hn
  have hpos : 0 < (1 - epsilon n) / 2 := by linarith
  have hm1 : epsilon n * z q₁ < epsilon n * M :=
    mul_lt_mul_of_pos_left hq₁ heps
  have hm2 : (1 - epsilon n) / 2 * z q₂ ≤ (1 - epsilon n) / 2 * M :=
    mul_le_mul_of_nonneg_left (hM q₂) (le_of_lt hpos)
  have hm3 : (1 - epsilon n) / 2 * z q₃ ≤ (1 - epsilon n) / 2 * M :=
    mul_le_mul_of_nonneg_left (hM q₃) (le_of_lt hpos)
  linarith

lemma lt_all_of_subharmonic {n : ℕ} (hn : 3 ≤ n) (σ : Policy n) (z : Fin (rows n) → ℚ)
    (hsub : ∀ r, z r ≤ ∑ q, transition n hn r (σ r) q * z q)
    {M : ℚ} (hM : ∀ q, z q ≤ M) (hMpos : 0 < M) :
    ∀ r : Fin (rows n), z r < M := by
  have ha_step : ∀ d : ℕ, ∀ i : ℕ, n - i = d → ∀ hi : ValidRow n (.a, i),
      z (mkRow n hn (.a, i) hi) < M := by
    intro d
    induction d with
    | zero =>
      intro i hd hi
      have hin : i = n := by dsimp [ValidRow] at hi; omega
      subst i
      set r := mkRow n hn (.a, n) hi
      have hr : rowName n r = (.a, n) := rowName_mkRow hn (.a, n) hi
      refine lt_of_le_of_lt (hsub r) ?_
      cases hσ : σ r
      · exact lt_of_eq_zero (trans_a_false_eq hn hr) hMpos
      · exact lt_of_eq_ite_two_half hn (trans_true_eq hn hr) hM hMpos
    | succ d ih =>
      intro i hd hi
      have hilt : i < n := by dsimp [ValidRow] at hi; omega
      have hi2 : 2 ≤ i := by dsimp [ValidRow] at hi; omega
      have ha' : ValidRow n (.a, i + 1) := by dsimp [ValidRow]; omega
      have hnext : z (mkRow n hn (.a, i + 1) ha') < M := ih (i + 1) (by omega) ha'
      set r := mkRow n hn (.a, i) hi
      have hr : rowName n r = (.a, i) := rowName_mkRow hn (.a, i) hi
      refine lt_of_le_of_lt (hsub r) ?_
      cases hσ : σ r
      · exact lt_of_eq_ite_one (trans_a_false_lt hn hr hilt ha') hnext
      · have hd' : ValidRow n (.d, i) := by dsimp [ValidRow]; omega
        have he' : ValidRow n (.e, i) := by dsimp [ValidRow]; omega
        exact lt_of_eq_ite_three hn (trans_true_lt hn hr hi2 hilt ha' hd' he') hM hnext
  have ha_all : ∀ i : ℕ, ∀ hi : ValidRow n (.a, i), z (mkRow n hn (.a, i) hi) < M :=
    fun i hi => ha_step (n - i) i rfl hi
  have htrue_all : ∀ r : Fin (rows n), σ r = true → z r < M := by
    intro r hσ
    have hp := rowName_valid hn r
    rcases hr : rowName n r with ⟨k, j⟩
    rw [hr] at hp
    refine lt_of_le_of_lt (hsub r) ?_
    rw [hσ]
    have hj_cases : (k = .e ∧ j = 1) ∨ (2 ≤ j ∧ j ≤ n) := by
      cases k <;> dsimp [ValidRow] at hp <;> simp <;> omega
    rcases hj_cases with ⟨rfl, rfl⟩ | ⟨hj2, hjn⟩
    · exact lt_of_eq_ite_eps hn (trans_e_true_one hn hr) hM (ha_all 2 (valid_a_two hn))
    · by_cases hjlt : j < n
      · have ha' : ValidRow n (.a, j + 1) := by dsimp [ValidRow]; omega
        have hd' : ValidRow n (.d, j) := by dsimp [ValidRow]; omega
        have he' : ValidRow n (.e, j) := by dsimp [ValidRow]; omega
        exact lt_of_eq_ite_three hn (trans_true_lt hn hr hj2 hjlt ha' hd' he') hM
          (ha_all (j + 1) ha')
      · have hjeq : j = n := by omega
        subst j
        exact lt_of_eq_ite_two_half hn (trans_true_eq hn hr) hM hMpos
  have hb_all : ∀ i : ℕ, ∀ hi : ValidRow n (.b, i), z (mkRow n hn (.b, i) hi) < M := by
    intro i
    induction i with
    | zero => intro hi; dsimp [ValidRow] at hi; omega
    | succ m ih =>
      intro hi
      set r := mkRow n hn (.b, m + 1) hi
      have hr : rowName n r = (.b, m + 1) := rowName_mkRow hn (.b, m + 1) hi
      cases hσ : σ r
      · refine lt_of_le_of_lt (hsub r) ?_
        rw [hσ]
        by_cases hm : m + 1 = 2
        · have hr2 : rowName n r = (.b, 2) := by rw [hr, hm]
          exact lt_of_eq_ite_eps hn (trans_bcd_false_two hn hr2 (Or.inl rfl)) hM
            (ha_all 2 (valid_a_two hn))
        · have hmgt : 2 < m + 1 := by dsimp [ValidRow] at hi; omega
          have hb' : ValidRow n (.b, m) := by dsimp [ValidRow] at hi ⊢; omega
          exact lt_of_eq_ite_one (trans_bd_false_gt hn hr (Or.inl rfl) hmgt hb') (ih hb')
      · exact htrue_all r hσ
  have hc_all : ∀ i : ℕ, ∀ hi : ValidRow n (.c, i), z (mkRow n hn (.c, i) hi) < M := by
    intro i
    induction i with
    | zero => intro hi; dsimp [ValidRow] at hi; omega
    | succ m ih =>
      intro hi
      set r := mkRow n hn (.c, m + 1) hi
      have hr : rowName n r = (.c, m + 1) := rowName_mkRow hn (.c, m + 1) hi
      cases hσ : σ r
      · refine lt_of_le_of_lt (hsub r) ?_
        rw [hσ]
        by_cases hm : m + 1 = 2
        · have hr2 : rowName n r = (.c, 2) := by rw [hr, hm]
          exact lt_of_eq_ite_eps hn (trans_bcd_false_two hn hr2 (Or.inr (Or.inl rfl))) hM
            (ha_all 2 (valid_a_two hn))
        · have hmgt : 2 < m + 1 := by dsimp [ValidRow] at hi; omega
          have hc' : ValidRow n (.c, m) := by dsimp [ValidRow] at hi ⊢; omega
          exact lt_of_eq_ite_one (trans_c_false_gt hn hr hmgt hc') (ih hc')
      · exact htrue_all r hσ
  have hd_all : ∀ i : ℕ, ∀ hi : ValidRow n (.d, i), z (mkRow n hn (.d, i) hi) < M := by
    intro i hi
    set r := mkRow n hn (.d, i) hi
    have hr : rowName n r = (.d, i) := rowName_mkRow hn (.d, i) hi
    cases hσ : σ r
    · refine lt_of_le_of_lt (hsub r) ?_
      rw [hσ]
      by_cases hi2 : i = 2
      · subst i
        exact lt_of_eq_ite_eps hn (trans_bcd_false_two hn hr (Or.inr (Or.inr rfl))) hM
          (ha_all 2 (valid_a_two hn))
      · have higt : 2 < i := by dsimp [ValidRow] at hi; omega
        have hb' : ValidRow n (.b, i - 1) := by dsimp [ValidRow] at hi ⊢; omega
        exact lt_of_eq_ite_one (trans_bd_false_gt hn hr (Or.inr rfl) higt hb')
          (hb_all (i - 1) hb')
    · exact htrue_all r hσ
  have he_all : ∀ i : ℕ, ∀ hi : ValidRow n (.e, i), z (mkRow n hn (.e, i) hi) < M := by
    intro i hi
    set r := mkRow n hn (.e, i) hi
    have hr : rowName n r = (.e, i) := rowName_mkRow hn (.e, i) hi
    cases hσ : σ r
    · refine lt_of_le_of_lt (hsub r) ?_
      rw [hσ]
      exact lt_of_eq_ite_one (trans_e_false hn hr) (hc_all n (valid_c_n hn))
    · exact htrue_all r hσ
  have h_mkRow : ∀ (p : Kind × ℕ) (hp : ValidRow n p), z (mkRow n hn p hp) < M := by
    rintro ⟨k, i⟩ hp
    cases k
    · exact ha_all i hp
    · exact hb_all i hp
    · exact hc_all i hp
    · exact hd_all i hp
    · exact he_all i hp
  intro r
  rw [← mkRow_rowName hn r]
  exact h_mkRow (rowName n r) (rowName_valid hn r)

lemma nonpos_of_subharmonic {n : ℕ} (hn : 3 ≤ n) (σ : Policy n) (z : Fin (rows n) → ℚ)
    (hsub : ∀ r, z r ≤ ∑ q, transition n hn r (σ r) q * z q) :
    ∀ r, z r ≤ 0 := by
  have hne : (Finset.univ : Finset (Fin (rows n))).Nonempty :=
    ⟨⟨0, by unfold rows; omega⟩, Finset.mem_univ _⟩
  set M := Finset.univ.sup' hne z
  have hM : ∀ q, z q ≤ M := fun q => Finset.le_sup' z (Finset.mem_univ q)
  obtain ⟨r₀, _, hr₀⟩ := Finset.exists_mem_eq_sup' hne z
  by_cases hMpos : 0 < M
  · have hall := lt_all_of_subharmonic hn σ z hsub hM hMpos r₀
    linarith
  · intro r
    exact le_trans (hM r) (not_lt.mp hMpos)

lemma basisMatrix_inv_entry_eq {n : ℕ} (hn : 3 ≤ n) (σ : Policy n) (i r : Fin (rows n)) :
    (basisMatrix (program n) (policyBasis n hn σ))⁻¹ i r -
      ∑ q : Fin (rows n),
        transition n hn r (σ r) q * (basisMatrix (program n) (policyBasis n hn σ))⁻¹ i q =
      if i = r then 1 else 0 := by
  set M := basisMatrix (program n) (policyBasis n hn σ)
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr ((mdp_valid n hn).2.2 σ)
  have hmul := congrFun (congrFun (Matrix.nonsing_inv_mul M hdet) i) r
  rw [Matrix.mul_apply, Matrix.one_apply] at hmul
  have hA : ∀ q, M⁻¹ i q * M q r =
      (if q = r then M⁻¹ i q else 0) - transition n hn r (σ r) q * M⁻¹ i q := by
    intro q
    change M⁻¹ i q * (program n).A q (actionColumn n hn r (σ r)) = _
    unfold transition
    split_ifs <;> ring
  simp only [hA, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hmul
  exact hmul

lemma basisMatrix_inv_nonneg (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (i q : Fin (rows n)) :
    0 ≤ (basisMatrix (program n) (policyBasis n hn σ))⁻¹ i q := by
  set M := basisMatrix (program n) (policyBasis n hn σ)
  have hsub : ∀ r, -M⁻¹ i r ≤ ∑ q', transition n hn r (σ r) q' * (-M⁻¹ i q') := by
    intro r
    have heq := basisMatrix_inv_entry_eq hn σ i r
    have hnonneg : (0 : ℚ) ≤ if i = r then 1 else 0 := by split_ifs <;> norm_num
    simp only [mul_neg, Finset.sum_neg_distrib]
    linarith
  have hle := nonpos_of_subharmonic hn σ (fun q' => -M⁻¹ i q') hsub q
  linarith

lemma basicValues_pos (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (i : Fin (rows n)) :
    0 < basicValues (program n) (policyBasis n hn σ) i := by
  set M := basisMatrix (program n) (policyBasis n hn σ)
  have hdiag := basisMatrix_inv_entry_eq hn σ i i
  rw [if_pos rfl] at hdiag
  have hsum_nonneg : 0 ≤ ∑ q : Fin (rows n), transition n hn i (σ i) q * M⁻¹ i q := by
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg ((mdp_valid n hn).1 i (σ i) q) (basisMatrix_inv_nonneg n hn σ i q)
  have hMii : 1 ≤ M⁻¹ i i := by linarith
  have hbv : basicValues (program n) (policyBasis n hn σ) i = ∑ q : Fin (rows n), M⁻¹ i q := by
    dsimp [basicValues, mulVec, dotProduct]
    have hb : (program n).b = fun _ => 1 := rfl
    simp [hb, M]
  rw [hbv]
  have hle : M⁻¹ i i ≤ ∑ q : Fin (rows n), M⁻¹ i q :=
    Finset.single_le_sum (fun q _ => basisMatrix_inv_nonneg n hn σ i q) (Finset.mem_univ i)
  linarith

lemma policyBasis_basicFeasible (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    basicFeasible (program n) (policyBasis n hn σ) :=
  ⟨policyBasis_injective n hn σ,
   (mdp_valid n hn).2.2 σ,
   fun i => le_of_lt (basicValues_pos n hn σ i)⟩

/-! ### Part 4: Boundedness of `program n` via Strict Superharmonic Weight -/

def eta (n k : ℕ) : ℚ := (epsilon n / 2) ^ k

def delta (n : ℕ) : ℚ := eta n n / (2 * n)

def rowWeight (n : ℕ) (r : Fin (rows n)) : ℚ :=
  let p := rowName n r
  match p.1 with
  | .a => 1 - eta n (n + 1 - p.2)
  | .b => 1 - eta n n + ((p.2 : ℚ) - 2) * delta n
  | .c => 1 - eta n n + ((p.2 : ℚ) - 2) * delta n
  | .d => if p.2 = 2 then 1 - eta n n else 1 - eta n n + ((p.2 : ℚ) - 1) * delta n
  | .e => 1

lemma eta_pos (n k : ℕ) : 0 < eta n k := by
  unfold eta
  have := epsilon_pos n
  positivity

lemma eta_succ (n k : ℕ) : eta n (k + 1) = (epsilon n / 2) * eta n k := by
  unfold eta
  rw [pow_succ']

lemma eps_mul_eta (n k : ℕ) : epsilon n * eta n k = 2 * eta n (k + 1) := by
  rw [eta_succ]
  ring

lemma eta_succ_le_half {n : ℕ} (hn : 3 ≤ n) (k : ℕ) : eta n (k + 1) ≤ eta n k / 2 := by
  rw [eta_succ]
  have heps : epsilon n < 1 := epsilon_lt_one hn
  have hpos : 0 ≤ eta n k := le_of_lt (eta_pos n k)
  nlinarith

lemma eta_anti {n : ℕ} (hn : 3 ≤ n) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    eta n k₂ ≤ eta n k₁ := by
  unfold eta
  have heps0 : 0 ≤ epsilon n / 2 := by have := epsilon_pos n; positivity
  have heps1 : epsilon n / 2 ≤ 1 := by have := epsilon_lt_one hn; linarith
  exact pow_le_pow_of_le_one heps0 heps1 hk

lemma delta_pos (n : ℕ) (hn : 3 ≤ n) : 0 < delta n := by
  unfold delta
  have := eta_pos n n
  have : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  positivity

lemma two_n_mul_delta {n : ℕ} (hn : 3 ≤ n) : 2 * (n : ℚ) * delta n = eta n n := by
  unfold delta
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

lemma delta_le_eta_half {n : ℕ} (hn : 3 ≤ n) : delta n ≤ eta n n / 2 := by
  have heq := two_n_mul_delta hn
  have hd : 0 < delta n := delta_pos n hn
  have hn3 : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

lemma delta_le_eta {n : ℕ} (hn : 3 ≤ n) : delta n ≤ eta n n := by
  have := delta_le_eta_half hn
  have := eta_pos n n
  linarith

lemma rowWeight_le_one {n : ℕ} (hn : 3 ≤ n) (q : Fin (rows n)) :
    rowWeight n q ≤ 1 := by
  have hv := rowName_valid hn q
  unfold rowWeight
  rcases hq : rowName n q with ⟨k, i⟩
  rw [hq] at hv
  dsimp only
  have heta := two_n_mul_delta hn
  have hd : 0 < delta n := delta_pos n hn
  cases k <;> dsimp [ValidRow] at hv
  · have := eta_pos n (n + 1 - i); linarith
  · have hi : (i : ℚ) ≤ n := by exact_mod_cast (by omega : i ≤ n)
    nlinarith
  · have hi : (i : ℚ) ≤ n := by exact_mod_cast hv.2
    nlinarith
  · split_ifs
    · have := eta_pos n n; linarith
    · have hi : (i : ℚ) ≤ n := by exact_mod_cast hv.2
      nlinarith
  · linarith

lemma one_sub_eta_le_rowWeight {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) :
    1 - eta n (n + 1 - (rowName n r).2) ≤ rowWeight n r := by
  have hv := rowName_valid hn r
  unfold rowWeight
  rcases hr : rowName n r with ⟨k, i⟩
  rw [hr] at hv
  dsimp only
  have heta_le : eta n n ≤ eta n (n + 1 - i) := by
    apply eta_anti hn
    cases k <;> dsimp [ValidRow] at hv <;> omega
  have hd : 0 ≤ delta n := le_of_lt (delta_pos n hn)
  cases k <;> dsimp [ValidRow] at hv
  · linarith
  · have hi : (2 : ℚ) ≤ i := by exact_mod_cast hv.1
    nlinarith
  · have hi : (2 : ℚ) ≤ i := by exact_mod_cast hv.1
    nlinarith
  · split_ifs
    · linarith
    · have hi : (2 : ℚ) ≤ i := by exact_mod_cast hv.1
      nlinarith
  · have := eta_pos n (n + 1 - i)
    linarith

lemma transition_rowWeight_bound (n : ℕ) (hn : 3 ≤ n) (r : Fin (rows n)) (b : Bool) :
    delta n ≤ rowWeight n r - ∑ q : Fin (rows n), transition n hn r b q * rowWeight n q := by
  have hp := rowName_valid hn r
  rcases hr : rowName n r with ⟨k, j⟩
  rw [hr] at hp
  have heps : 0 < epsilon n := epsilon_pos n
  have heps1 : epsilon n < 1 := epsilon_lt_one hn
  have hd : 0 < delta n := delta_pos n hn
  have hd_half : delta n ≤ eta n n / 2 := delta_le_eta_half hn
  have hd_eta : delta n ≤ eta n n := delta_le_eta hn
  cases b
  · cases k <;> dsimp [ValidRow] at hp
    · by_cases hj : j < n
      · have ha : ValidRow n (.a, j + 1) := by dsimp [ValidRow]; omega
        simp only [trans_a_false_lt hn hr hj ha, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        unfold rowWeight
        rw [hr, rowName_mkRow]
        dsimp only
        have hsub : n + 1 - j = (n - j) + 1 := by omega
        have hsub2 : n + 1 - (j + 1) = n - j := by omega
        have hstep : eta n (n + 1 - j) ≤ eta n (n - j) / 2 := by
          rw [hsub]; exact eta_succ_le_half hn (n - j)
        have hanti : eta n n ≤ eta n (n - j) := eta_anti hn (by omega)
        rw [hsub2]
        linarith
      · have hjn : j = n := by omega
        subst j
        simp only [trans_a_false_eq hn hr, zero_mul, Finset.sum_const_zero, sub_zero]
        unfold rowWeight
        rw [hr]
        dsimp only
        have hsub : n + 1 - n = 1 := by omega
        rw [hsub]
        have h1 : eta n 1 = epsilon n / 2 := by unfold eta; ring
        have hanti : eta n n ≤ eta n 1 := eta_anti hn (by omega)
        linarith
    · by_cases hj : j = 2
      · subst j
        simp only [trans_bcd_false_two hn hr (Or.inl rfl), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        unfold rowWeight
        rw [hr, rowName_mkRow, rowName_mkRow]
        dsimp only
        have hsub : n + 1 - 2 = n - 1 := by omega
        have heta : epsilon n * eta n (n - 1) = 2 * eta n n := by
          have := eps_mul_eta n (n - 1)
          have h1 : n - 1 + 1 = n := by omega
          rw [h1] at this
          exact this
        rw [hsub]
        norm_num
        linarith
      · have hjgt : 2 < j := by omega
        have hb : ValidRow n (.b, j - 1) := by dsimp [ValidRow]; omega
        simp only [trans_bd_false_gt hn hr (Or.inl rfl) hjgt hb, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        unfold rowWeight
        rw [hr, rowName_mkRow]
        dsimp only
        have hcast : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hcast]
        linarith
    · by_cases hj : j = 2
      · subst j
        simp only [trans_bcd_false_two hn hr (Or.inr (Or.inl rfl)), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        unfold rowWeight
        rw [hr, rowName_mkRow, rowName_mkRow]
        dsimp only
        have hsub : n + 1 - 2 = n - 1 := by omega
        have heta : epsilon n * eta n (n - 1) = 2 * eta n n := by
          have := eps_mul_eta n (n - 1)
          have h1 : n - 1 + 1 = n := by omega
          rw [h1] at this
          exact this
        rw [hsub]
        norm_num
        linarith
      · have hjgt : 2 < j := by omega
        have hc : ValidRow n (.c, j - 1) := by dsimp [ValidRow]; omega
        simp only [trans_c_false_gt hn hr hjgt hc, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        unfold rowWeight
        rw [hr, rowName_mkRow]
        dsimp only
        have hcast : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hcast]
        linarith
    · by_cases hj : j = 2
      · subst j
        simp only [trans_bcd_false_two hn hr (Or.inr (Or.inr rfl)), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        unfold rowWeight
        rw [hr, rowName_mkRow, rowName_mkRow]
        dsimp only
        have hsub : n + 1 - 2 = n - 1 := by omega
        have heta : epsilon n * eta n (n - 1) = 2 * eta n n := by
          have := eps_mul_eta n (n - 1)
          have h1 : n - 1 + 1 = n := by omega
          rw [h1] at this
          exact this
        rw [hsub]
        norm_num
        linarith
      · have hjgt : 2 < j := by omega
        have hb : ValidRow n (.b, j - 1) := by dsimp [ValidRow]; omega
        simp only [trans_bd_false_gt hn hr (Or.inr rfl) hjgt hb, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        unfold rowWeight
        rw [hr, rowName_mkRow]
        dsimp only
        rw [if_neg hj]
        have hcast : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hcast]
        linarith
    · simp only [trans_e_false hn hr, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      unfold rowWeight
      rw [hr, rowName_mkRow]
      dsimp only
      have heta := two_n_mul_delta hn
      have hn3 : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      nlinarith
  · have hj_cases : (k = .e ∧ j = 1) ∨ (2 ≤ j ∧ j ≤ n) := by
      cases k <;> dsimp [ValidRow] at hp <;> simp <;> omega
    rcases hj_cases with ⟨rfl, rfl⟩ | ⟨hj2, hjn⟩
    · simp only [trans_e_true_one hn hr, add_mul, ite_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      unfold rowWeight
      rw [hr, rowName_mkRow, rowName_mkRow]
      dsimp only
      have hsub : n + 1 - 2 = n - 1 := by omega
      have heta : epsilon n * eta n (n - 1) = 2 * eta n n := by
        have := eps_mul_eta n (n - 1)
        have h1 : n - 1 + 1 = n := by omega
        rw [h1] at this
        exact this
      rw [hsub]
      linarith
    · by_cases hjlt : j < n
      · have ha : ValidRow n (.a, j + 1) := by dsimp [ValidRow]; omega
        have hd_row : ValidRow n (.d, j) := by dsimp [ValidRow]; omega
        have he_row : ValidRow n (.e, j) := by dsimp [ValidRow]; omega
        simp only [trans_true_lt hn hr hj2 hjlt ha hd_row he_row, add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have hwr := one_sub_eta_le_rowWeight hn r
        rw [hr] at hwr
        dsimp only at hwr
        have hwa : rowWeight n (mkRow n hn (.a, j + 1) ha) = 1 - eta n (n - j) := by
          unfold rowWeight
          rw [rowName_mkRow]
          dsimp only
          have : n + 1 - (j + 1) = n - j := by omega
          rw [this]
        have hwd : rowWeight n (mkRow n hn (.d, j) hd_row) ≤ 1 := rowWeight_le_one hn _
        have hwe : rowWeight n (mkRow n hn (.e, j) he_row) ≤ 1 := rowWeight_le_one hn _
        have hpos : 0 ≤ (1 - epsilon n) / 2 := by linarith
        have hm1 : (1 - epsilon n) / 2 * rowWeight n (mkRow n hn (.d, j) hd_row) ≤
            (1 - epsilon n) / 2 := by nlinarith
        have hm2 : (1 - epsilon n) / 2 * rowWeight n (mkRow n hn (.e, j) he_row) ≤
            (1 - epsilon n) / 2 := by nlinarith
        have heta : epsilon n * eta n (n - j) = 2 * eta n (n + 1 - j) := by
          have := eps_mul_eta n (n - j)
          have h1 : n - j + 1 = n + 1 - j := by omega
          rw [h1] at this
          exact this
        have hanti : eta n n ≤ eta n (n + 1 - j) := eta_anti hn (by omega)
        rw [hwa]
        linarith
      · have hjeq : j = n := by omega
        subst j
        simp only [trans_true_eq hn hr, add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have hwr := one_sub_eta_le_rowWeight hn r
        rw [hr] at hwr
        dsimp only at hwr
        have hsub : n + 1 - n = 1 := by omega
        rw [hsub] at hwr
        have hwd : rowWeight n (mkRow n hn (.d, n) (valid_d_n hn)) ≤ 1 := rowWeight_le_one hn _
        have hwe : rowWeight n (mkRow n hn (.e, n) (valid_e_n hn)) ≤ 1 := rowWeight_le_one hn _
        have hpos : 0 ≤ (1 - epsilon n) / 2 := by linarith
        have hm1 : (1 - epsilon n) / 2 * rowWeight n (mkRow n hn (.d, n) (valid_d_n hn)) ≤
            (1 - epsilon n) / 2 := by nlinarith
        have hm2 : (1 - epsilon n) / 2 * rowWeight n (mkRow n hn (.e, n) (valid_e_n hn)) ≤
            (1 - epsilon n) / 2 := by nlinarith
        have h1 : eta n 1 = epsilon n / 2 := by unfold eta; ring
        have hanti : eta n n ≤ eta n 1 := eta_anti hn (by omega)
        linarith

lemma column_rowWeight_bound (n : ℕ) (hn : 3 ≤ n) (j : Fin (cols n)) :
    delta n ≤ ∑ q : Fin (rows n), (program n).A q j * rowWeight n q := by
  rcases exists_actionColumn n hn j with ⟨r, b, rfl⟩
  have hA : ∀ q, (program n).A q (actionColumn n hn r b) * rowWeight n q =
      (if q = r then rowWeight n q else 0) - transition n hn r b q * rowWeight n q := by
    intro q
    unfold transition
    split_ifs <;> ring
  simp only [hA, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact transition_rowWeight_bound n hn r b

lemma program_bounded (n : ℕ) (hn : 3 ≤ n) : bounded (program n) := by
  refine ⟨(∑ q : Fin (rows n), rowWeight n q) / delta n, ?_⟩
  intro x ⟨hAx, hx⟩ j₀
  have hd : 0 < delta n := delta_pos n hn
  rw [abs_of_nonneg (hx j₀), le_div_iff₀ hd, mul_comm]
  have hcol := fun j => column_rowWeight_bound n hn j
  have hle1 : delta n * x j₀ ≤ (∑ q, (program n).A q j₀ * rowWeight n q) * x j₀ :=
    mul_le_mul_of_nonneg_right (hcol j₀) (hx j₀)
  have hle2 : (∑ q, (program n).A q j₀ * rowWeight n q) * x j₀ ≤
      ∑ j : Fin (cols n), (∑ q, (program n).A q j * rowWeight n q) * x j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (le_trans (le_of_lt hd) (hcol j)) (hx j))
      (Finset.mem_univ j₀)
  have hsum : (∑ j : Fin (cols n), (∑ q, (program n).A q j * rowWeight n q) * x j) =
      ∑ q : Fin (rows n), rowWeight n q := by
    calc (∑ j : Fin (cols n), (∑ q, (program n).A q j * rowWeight n q) * x j)
      _ = ∑ j : Fin (cols n), ∑ q : Fin (rows n), rowWeight n q * ((program n).A q j * x j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => by ring
      _ = ∑ q : Fin (rows n), ∑ j : Fin (cols n), rowWeight n q * ((program n).A q j * x j) :=
        Finset.sum_comm
      _ = ∑ q : Fin (rows n), rowWeight n q * ((program n).A *ᵥ x) q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.mul_sum]
        rfl
      _ = ∑ q : Fin (rows n), rowWeight n q := by
        rw [hAx]
        refine Finset.sum_congr rfl fun q _ => ?_
        change rowWeight n q * 1 = rowWeight n q
        ring
  linarith

end FriedmannCunningham

open FriedmannCunningham

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    FriedmannSimplex.bounded (program n) ∧
    ∀ σ : Policy n,
      FriedmannSimplex.basicFeasible (program n) (policyBasis n hn σ) ∧
        ∀ i, 0 < FriedmannSimplex.basicValues (program n) (policyBasis n hn σ) i :=
  ⟨program_bounded n hn, fun σ => ⟨policyBasis_basicFeasible n hn σ, basicValues_pos n hn σ⟩⟩
