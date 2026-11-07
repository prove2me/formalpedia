-- Prove2me | solution 1 for FriedmannCunningham.cube_realization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T05:02:46.885629+00:00
-- url     : https://prove2.me/submissions/838398df-83de-4f95-95f2-42af0a358d4b

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

lemma rowRank_rowName {n : ℕ} (_hn : 3 ≤ n) (r : Fin (rows n)) :
    rowRank n (rowName n r) = r.val := by
  have hr := r.isLt
  unfold rows at hr
  unfold rowName
  split_ifs <;> dsimp [rowRank] <;> omega

lemma rowName_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (rowName n) := by
  intro q r hqr
  apply Fin.ext
  rw [← rowRank_rowName hn q, ← rowRank_rowName hn r, hqr]

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

lemma actionColumn_bijective (n : ℕ) (hn : 3 ≤ n) :
    Function.Bijective (fun p : Fin (rows n) × Bool => actionColumn n hn p.1 p.2) := by
  have hinj : Function.Injective (fun p : Fin (rows n) × Bool => actionColumn n hn p.1 p.2) := by
    rintro ⟨r₁, b₁⟩ ⟨r₂, b₂⟩ h
    rcases actionColumn_inj hn h with ⟨rfl, rfl⟩
    rfl
  have hcard : Fintype.card (Fin (rows n) × Bool) = Fintype.card (Fin (cols n)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]
    unfold rows cols
    omega
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

lemma exists_actionColumn (n : ℕ) (hn : 3 ≤ n) (j : Fin (cols n)) :
    ∃ (r : Fin (rows n)) (b : Bool), actionColumn n hn r b = j := by
  rcases (actionColumn_bijective n hn).2 j with ⟨⟨r, b⟩, hr⟩
  exact ⟨r, b, hr⟩

noncomputable def colEquiv (n : ℕ) (hn : 3 ≤ n) : (Fin (rows n) × Bool) ≃ Fin (cols n) :=
  Equiv.ofBijective (fun p => actionColumn n hn p.1 p.2) (actionColumn_bijective n hn)

lemma sum_cols_eq_sum_rows_bool (n : ℕ) (hn : 3 ≤ n) (g : Fin (cols n) → ℚ) :
    (∑ j : Fin (cols n), g j) =
      ∑ q : Fin (rows n), (g (actionColumn n hn q false) + g (actionColumn n hn q true)) := by
  rw [← Equiv.sum_comp (colEquiv n hn) g, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_bool]
  simp [colEquiv]
  ring

lemma sum_cols_eq_sum_policy (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (g : Fin (cols n) → ℚ) :
    (∑ j : Fin (cols n), g j) =
      (∑ q : Fin (rows n), g (actionColumn n hn q (σ q))) +
        (∑ q : Fin (rows n), g (actionColumn n hn q (!σ q))) := by
  rw [sum_cols_eq_sum_rows_bool n hn g, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  cases σ q <;> simp [add_comm]

/-! ### Part 2: Master Decomposition of `A *ᵥ x` and Basic Solutions -/

lemma basicPoint_actionColumn (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) (b : Bool) :
    basicPoint (program n) (policyBasis n hn σ) (actionColumn n hn r b) =
      if b = σ r then basicValues (program n) (policyBasis n hn σ) r else 0 := by
  unfold basicPoint
  have hcongr : ∀ i : Fin (rows n),
      (if policyBasis n hn σ i = actionColumn n hn r b then
        basicValues (program n) (policyBasis n hn σ) i else 0) =
      if i = r then (if b = σ r then basicValues (program n) (policyBasis n hn σ) r else 0)
      else 0 := by
    intro i
    unfold policyBasis
    by_cases hir : i = r
    · subst i
      by_cases hb : b = σ r
      · subst b; simp
      · have hne : actionColumn n hn r (σ r) ≠ actionColumn n hn r b :=
          fun h => hb (actionColumn_inj hn h).2.symm
        simp [hne, hb]
    · have hne : actionColumn n hn i (σ i) ≠ actionColumn n hn r b :=
        fun h => hir (actionColumn_inj hn h).1
      simp [hne, hir]
  simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma basicPoint_apply_self (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    basicPoint (program n) (policyBasis n hn σ) (actionColumn n hn r (σ r)) =
      basicValues (program n) (policyBasis n hn σ) r := by
  rw [basicPoint_actionColumn, if_pos rfl]

lemma basicPoint_apply_opp (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    basicPoint (program n) (policyBasis n hn σ) (actionColumn n hn r (!σ r)) = 0 := by
  rw [basicPoint_actionColumn, if_neg]
  cases σ r <;> simp

lemma basicPoint_nonneg (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (j : Fin (cols n)) :
    0 ≤ basicPoint (program n) (policyBasis n hn σ) j := by
  rcases exists_actionColumn n hn j with ⟨r, b, rfl⟩
  rw [basicPoint_actionColumn]
  split_ifs
  · exact le_of_lt (((lp_valid n hn).2 σ).2 r)
  · linarith

lemma mulVec_A_eq_policyBasis (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (x : Fin (cols n) → ℚ) :
    (program n).A *ᵥ x =
      basisMatrix (program n) (policyBasis n hn σ) *ᵥ (fun q => x (policyBasis n hn σ q)) +
        fun r => ∑ q : Fin (rows n),
          (program n).A r (actionColumn n hn q (!σ q)) * x (actionColumn n hn q (!σ q)) := by
  ext r
  dsimp [mulVec, dotProduct, basisMatrix, policyBasis]
  exact sum_cols_eq_sum_policy n hn σ (fun j => (program n).A r j * x j)

lemma basicPoint_mulVec_A (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    (program n).A *ᵥ basicPoint (program n) (policyBasis n hn σ) = (program n).b := by
  rw [mulVec_A_eq_policyBasis n hn σ]
  simp only [policyBasis, basicPoint_apply_self, basicPoint_apply_opp, mul_zero,
    Finset.sum_const_zero]
  have hadd : (basisMatrix (program n) (policyBasis n hn σ) *ᵥ
      basicValues (program n) (policyBasis n hn σ) + fun _ => 0) =
      basisMatrix (program n) (policyBasis n hn σ) *ᵥ
        basicValues (program n) (policyBasis n hn σ) := by
    ext r; simp
  rw [hadd]
  set M := basisMatrix (program n) (policyBasis n hn σ)
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr ((lp_valid n hn).2 σ).1.2.1
  change M *ᵥ (M⁻¹ *ᵥ (program n).b) = (program n).b
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]

lemma basicPoint_feasible (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    feasible (program n) (basicPoint (program n) (policyBasis n hn σ)) :=
  ⟨basicPoint_mulVec_A n hn σ, basicPoint_nonneg n hn σ⟩

lemma coord_eq_of_mulVec_eq_b (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    {x : Fin (cols n) → ℚ} (hAx : (program n).A *ᵥ x = (program n).b) (i : Fin (rows n)) :
    x (policyBasis n hn σ i) +
      ∑ q : Fin (rows n),
        direction (program n) (policyBasis n hn σ) (actionColumn n hn q (!σ q)) i *
          x (actionColumn n hn q (!σ q)) =
      basicValues (program n) (policyBasis n hn σ) i := by
  set B := policyBasis n hn σ
  set M := basisMatrix (program n) B
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr ((lp_valid n hn).2 σ).1.2.1
  have hdecomp := congrArg (M⁻¹ *ᵥ ·) (mulVec_A_eq_policyBasis n hn σ x)
  rw [hAx, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hdet,
    Matrix.one_mulVec] at hdecomp
  have hi := (congrFun hdecomp i).symm
  dsimp only [Pi.add_apply] at hi
  have hsum : (M⁻¹ *ᵥ fun r => ∑ q : Fin (rows n),
      (program n).A r (actionColumn n hn q (!σ q)) * x (actionColumn n hn q (!σ q))) i =
      ∑ q : Fin (rows n),
        direction (program n) B (actionColumn n hn q (!σ q)) i *
          x (actionColumn n hn q (!σ q)) := by
    dsimp [direction, mulVec, dotProduct]
    calc (∑ r : Fin (rows n), M⁻¹ i r * ∑ q : Fin (rows n),
            (program n).A r (actionColumn n hn q (!σ q)) * x (actionColumn n hn q (!σ q)))
      _ = ∑ r : Fin (rows n), ∑ q : Fin (rows n),
            (M⁻¹ i r * (program n).A r (actionColumn n hn q (!σ q))) *
              x (actionColumn n hn q (!σ q)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring
      _ = ∑ q : Fin (rows n), ∑ r : Fin (rows n),
            (M⁻¹ i r * (program n).A r (actionColumn n hn q (!σ q))) *
              x (actionColumn n hn q (!σ q)) :=
        Finset.sum_comm
      _ = ∑ q : Fin (rows n),
            (∑ r : Fin (rows n), M⁻¹ i r * (program n).A r (actionColumn n hn q (!σ q))) *
              x (actionColumn n hn q (!σ q)) := by
        refine Finset.sum_congr rfl fun q _ => by rw [Finset.sum_mul]
  rw [hsum] at hi
  exact hi

lemma eq_basicPoint_of_opp_eq_zero (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    {x : Fin (cols n) → ℚ} (hAx : (program n).A *ᵥ x = (program n).b)
    (hz : ∀ q : Fin (rows n), x (actionColumn n hn q (!σ q)) = 0) :
    x = basicPoint (program n) (policyBasis n hn σ) := by
  ext j
  rcases exists_actionColumn n hn j with ⟨r, b, rfl⟩
  by_cases hb : b = σ r
  · subst b
    have hcoord := coord_eq_of_mulVec_eq_b n hn σ hAx r
    simp only [hz, mul_zero, Finset.sum_const_zero, add_zero] at hcoord
    rw [basicPoint_apply_self]
    exact hcoord
  · have hb' : b = !σ r := by
      cases b <;> cases h : σ r <;> revert hb <;> simp [h]
    subst b
    rw [hz r, basicPoint_apply_opp]

lemma policy_eq_of_basicPoint_eq (n : ℕ) (hn : 3 ≤ n) {σ τ : Policy n}
    (h : basicPoint (program n) (policyBasis n hn σ) =
      basicPoint (program n) (policyBasis n hn τ)) :
    σ = τ := by
  ext r
  have hr := congrFun h (actionColumn n hn r (σ r))
  rw [basicPoint_apply_self, basicPoint_actionColumn] at hr
  have hpos : 0 < basicValues (program n) (policyBasis n hn σ) r := ((lp_valid n hn).2 σ).2 r
  split_ifs at hr with heq
  · exact heq
  · linarith

/-! ### Part 3: Proof of `realizesCube` -/

lemma basicPoint_isVertex (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    isVertex (program n) (basicPoint (program n) (policyBasis n hn σ)) := by
  refine ⟨basicPoint_feasible n hn σ, ?_⟩
  intro y z hy hz hmid
  have hy0 : ∀ q : Fin (rows n), y (actionColumn n hn q (!σ q)) = 0 := by
    intro q
    have hq := hmid (actionColumn n hn q (!σ q))
    rw [basicPoint_apply_opp] at hq
    have hy_nn := hy.2 (actionColumn n hn q (!σ q))
    have hz_nn := hz.2 (actionColumn n hn q (!σ q))
    linarith
  have hz0 : ∀ q : Fin (rows n), z (actionColumn n hn q (!σ q)) = 0 := by
    intro q
    have hq := hmid (actionColumn n hn q (!σ q))
    rw [basicPoint_apply_opp] at hq
    have hy_nn := hy.2 (actionColumn n hn q (!σ q))
    have hz_nn := hz.2 (actionColumn n hn q (!σ q))
    linarith
  exact ⟨eq_basicPoint_of_opp_eq_zero n hn σ hy.1 hy0,
         eq_basicPoint_of_opp_eq_zero n hn σ hz.1 hz0⟩

lemma row_flow_ge_one (n : ℕ) (hn : 3 ≤ n) {x : Fin (cols n) → ℚ}
    (hx : feasible (program n) x) (r : Fin (rows n)) :
    1 ≤ x (actionColumn n hn r false) + x (actionColumn n hn r true) := by
  have hr : ((program n).A *ᵥ x) r = 1 := congrFun hx.1 r
  dsimp [mulVec, dotProduct] at hr
  rw [sum_cols_eq_sum_rows_bool n hn (fun j => (program n).A r j * x j)] at hr
  have hle : ∀ q : Fin (rows n), ∀ b : Bool,
      (program n).A r (actionColumn n hn q b) * x (actionColumn n hn q b) ≤
        if q = r then x (actionColumn n hn q b) else 0 := by
    intro q b
    have hA : (program n).A r (actionColumn n hn q b) =
        (if r = q then 1 else 0) - transition n hn q b r := by
      unfold transition; ring
    rw [hA]
    have htr : 0 ≤ transition n hn q b r := (mdp_valid n hn).1 q b r
    have hxb : 0 ≤ x (actionColumn n hn q b) := hx.2 _
    by_cases hqr : q = r
    · subst q; rw [if_pos rfl, if_pos rfl]; nlinarith
    · have hrq : r ≠ q := Ne.symm hqr
      rw [if_neg hrq, if_neg hqr]; nlinarith
  have hsum_le : (∑ q : Fin (rows n),
      ((program n).A r (actionColumn n hn q false) * x (actionColumn n hn q false) +
       (program n).A r (actionColumn n hn q true) * x (actionColumn n hn q true))) ≤
      ∑ q : Fin (rows n),
        ((if q = r then x (actionColumn n hn q false) else 0) +
         (if q = r then x (actionColumn n hn q true) else 0)) := by
    refine Finset.sum_le_sum fun q _ => add_le_add (hle q false) (hle q true)
  rw [Finset.sum_add_distrib] at hr
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum_le
  linarith

lemma exists_policy_of_isVertex (n : ℕ) (hn : 3 ≤ n) {x : Fin (cols n) → ℚ}
    (hvert : isVertex (program n) x) :
    ∃ σ : Policy n, basicPoint (program n) (policyBasis n hn σ) = x := by
  let σ : Policy n := fun r => decide (0 < x (actionColumn n hn r true))
  have hx_pos : ∀ r : Fin (rows n), 0 < x (policyBasis n hn σ r) := by
    intro r
    unfold policyBasis
    by_cases htrue : 0 < x (actionColumn n hn r true)
    · have hσ : σ r = true := decide_eq_true htrue
      rw [hσ]; exact htrue
    · have hσ : σ r = false := decide_eq_false htrue
      rw [hσ]
      have hflow := row_flow_ge_one n hn hvert.1 r
      linarith
  by_contra hne
  have hex_opp : ∃ r₀ : Fin (rows n), 0 < x (actionColumn n hn r₀ (!σ r₀)) := by
    by_contra hall
    simp only [not_exists, not_lt] at hall
    have hz : ∀ q : Fin (rows n), x (actionColumn n hn q (!σ q)) = 0 := by
      intro q
      exact le_antisymm (hall q) (hvert.1.2 _)
    exact hne ⟨σ, (eq_basicPoint_of_opp_eq_zero n hn σ hvert.1.1 hz).symm⟩
  rcases hex_opp with ⟨r₀, hr₀_pos⟩
  set B := policyBasis n hn σ
  set M := basisMatrix (program n) B
  set j₀ := actionColumn n hn r₀ (!σ r₀)
  let d : Fin (cols n) → ℚ := fun j =>
    (if j = j₀ then 1 else 0) -
      ∑ i : Fin (rows n), if B i = j then direction (program n) B j₀ i else 0
  have hd_j₀ : d j₀ = 1 := by
    dsimp [d]
    rw [if_pos rfl]
    have h0 : (∑ i : Fin (rows n), if B i = j₀ then direction (program n) B j₀ i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro hBi
      rcases actionColumn_inj hn hBi with ⟨rfl, hb⟩
      cases σ i <;> simp at hb
    linarith
  have hd_zero_of_x_zero : ∀ j : Fin (cols n), ¬ (0 < x j) → d j = 0 := by
    intro j hxj
    dsimp [d]
    have hj₀ : j ≠ j₀ := fun h => hxj (h ▸ hr₀_pos)
    have hBi : ∀ i : Fin (rows n), B i ≠ j := fun i h => hxj (h ▸ hx_pos i)
    simp [hj₀, hBi]
  have hAd : (program n).A *ᵥ d = 0 := by
    ext r
    have hdecomp := congrFun (mulVec_A_eq_policyBasis n hn σ d) r
    dsimp only [Pi.add_apply] at hdecomp
    rw [hdecomp]
    have hB_apply : ∀ q : Fin (rows n), d (B q) = - direction (program n) B j₀ q := by
      intro q
      dsimp [d]
      have hne_j₀ : B q ≠ j₀ := by
        intro h
        rcases actionColumn_inj hn h with ⟨rfl, hb⟩
        cases σ q <;> simp at hb
      rw [if_neg hne_j₀]
      have hcongr : ∀ i : Fin (rows n),
          (if B i = B q then direction (program n) B j₀ i else 0) =
          if i = q then direction (program n) B j₀ q else 0 := by
        intro i
        by_cases hiq : i = q
        · subst i; simp
        · have hne_Bi : B i ≠ B q := fun h => hiq (actionColumn_inj hn h).1
          simp [hne_Bi, hiq]
      simp [hcongr]
    have hopp_apply : ∀ q : Fin (rows n),
        d (actionColumn n hn q (!σ q)) = if q = r₀ then 1 else 0 := by
      intro q
      dsimp [d]
      have hBi : ∀ i : Fin (rows n), B i ≠ actionColumn n hn q (!σ q) := by
        intro i h
        rcases actionColumn_inj hn h with ⟨rfl, hb⟩
        cases σ i <;> simp at hb
      simp only [hBi, ↓reduceIte, Finset.sum_const_zero, sub_zero]
      by_cases hqr₀ : q = r₀
      · subst q; simp [j₀]
      · have hne_q : actionColumn n hn q (!σ q) ≠ j₀ :=
          fun h => hqr₀ (actionColumn_inj hn h).1
        simp [hne_q, hqr₀]
    have hMdir : (M *ᵥ direction (program n) B j₀) r = (program n).A r j₀ := by
      have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr ((lp_valid n hn).2 σ).1.2.1
      have hmul : M *ᵥ direction (program n) B j₀ = fun q => (program n).A q j₀ := by
        change M *ᵥ (M⁻¹ *ᵥ fun q => (program n).A q j₀) = _
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]
      exact congrFun hmul r
    have h1 : (M *ᵥ fun q => d (B q)) r = - (program n).A r j₀ := by
      simp only [hB_apply]
      change (M *ᵥ (- direction (program n) B j₀)) r = _
      rw [Matrix.mulVec_neg, Pi.neg_apply, hMdir]
    have h2 : (∑ q : Fin (rows n),
        (program n).A r (actionColumn n hn q (!σ q)) * d (actionColumn n hn q (!σ q))) =
        (program n).A r j₀ := by
      simp only [hopp_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rfl
    change (M *ᵥ fun q => d (B q)) r +
      (∑ q : Fin (rows n),
        (program n).A r (actionColumn n hn q (!σ q)) * d (actionColumn n hn q (!σ q))) = 0
    rw [h1, h2]
    ring
  have hne_cols : (Finset.univ : Finset (Fin (cols n))).Nonempty :=
    ⟨⟨0, by unfold cols; omega⟩, Finset.mem_univ _⟩
  let step : Fin (cols n) → ℚ := fun j => if 0 < x j then x j / (|d j| + 1) else 1
  have hstep_pos : ∀ j : Fin (cols n), 0 < step j := by
    intro j
    dsimp [step]
    split_ifs with hxj
    · have : 0 < |d j| + 1 := by positivity
      exact div_pos hxj this
    · norm_num
  set ε := Finset.univ.inf' hne_cols step
  have hε_pos : 0 < ε := (Finset.lt_inf'_iff hne_cols).mpr (fun j _ => hstep_pos j)
  have hε_le : ∀ j : Fin (cols n), ε * |d j| ≤ x j := by
    intro j
    by_cases hxj : 0 < x j
    · have hle : ε ≤ step j := Finset.inf'_le step (Finset.mem_univ j)
      dsimp [step] at hle
      rw [if_pos hxj] at hle
      have hpos : 0 < |d j| + 1 := by positivity
      rw [le_div_iff₀ hpos] at hle
      nlinarith [abs_nonneg (d j)]
    · rw [hd_zero_of_x_zero j hxj, abs_zero, mul_zero]
      exact hvert.1.2 j
  let y : Fin (cols n) → ℚ := x + ε • d
  let z : Fin (cols n) → ℚ := x - ε • d
  have hy_feas : feasible (program n) y := by
    refine ⟨?_, ?_⟩
    · dsimp [y]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hvert.1.1, hAd, smul_zero, add_zero]
    · intro j
      dsimp [y]
      have h1 := hε_le j
      have h2 := neg_abs_le (d j)
      nlinarith
  have hz_feas : feasible (program n) z := by
    refine ⟨?_, ?_⟩
    · dsimp [z]
      rw [sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul,
        hvert.1.1, hAd, smul_zero, neg_zero, add_zero]
    · intro j
      dsimp [z]
      have h1 := hε_le j
      have h2 := le_abs_self (d j)
      nlinarith
  have hmid : ∀ j : Fin (cols n), x j = (y j + z j) / 2 := by
    intro j; dsimp [y, z]; ring
  have hyx := (hvert.2 y z hy_feas hz_feas hmid).1
  have hyj₀ := congrFun hyx j₀
  dsimp [y] at hyj₀
  rw [hd_j₀, mul_one] at hyj₀
  linarith

lemma existsUnique_policy_of_isVertex (n : ℕ) (hn : 3 ≤ n) {x : Fin (cols n) → ℚ}
    (hvert : isVertex (program n) x) :
    ∃! σ : Policy n, basicPoint (program n) (policyBasis n hn σ) = x := by
  rcases exists_policy_of_isVertex n hn hvert with ⟨σ, rfl⟩
  exact ⟨σ, rfl, fun τ hτ => policy_eq_of_basicPoint_eq n hn hτ⟩

lemma eq_affine_of_opp_zero_except (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r₀ : Fin (rows n))
    {u v : Fin (cols n) → ℚ}
    (hu : (program n).A *ᵥ u = (program n).b)
    (hv : (program n).A *ᵥ v = (program n).b)
    (hu0 : ∀ q : Fin (rows n), q ≠ r₀ → u (actionColumn n hn q (!σ q)) = 0)
    (hv0 : ∀ q : Fin (rows n), q ≠ r₀ → v (actionColumn n hn q (!σ q)) = 0)
    (h_eq_r₀ : u (actionColumn n hn r₀ (!σ r₀)) = v (actionColumn n hn r₀ (!σ r₀))) :
    u = v := by
  have hopp : ∀ q : Fin (rows n),
      u (actionColumn n hn q (!σ q)) = v (actionColumn n hn q (!σ q)) := by
    intro q
    by_cases hqr₀ : q = r₀
    · subst q; exact h_eq_r₀
    · rw [hu0 q hqr₀, hv0 q hqr₀]
  ext j
  rcases exists_actionColumn n hn j with ⟨q, b, rfl⟩
  by_cases hb : b = σ q
  · subst b
    have hcu := coord_eq_of_mulVec_eq_b n hn σ hu q
    have hcv := coord_eq_of_mulVec_eq_b n hn σ hv q
    simp only [hopp] at hcu
    unfold policyBasis at hcu hcv
    linarith
  · have hb' : b = !σ q := by
      cases b <;> cases h : σ q <;> revert hb <;> simp [h]
    subst b
    exact hopp q

lemma cubeAdjacent_iff_polytopeAdjacent (n : ℕ) (hn : 3 ≤ n) (σ τ : Policy n) :
    cubeAdjacent n σ τ ↔
      polytopeAdjacent (program n) (basicPoint (program n) (policyBasis n hn σ))
        (basicPoint (program n) (policyBasis n hn τ)) := by
  set x_σ := basicPoint (program n) (policyBasis n hn σ)
  set x_τ := basicPoint (program n) (policyBasis n hn τ)
  constructor
  · rintro ⟨r₀, hne_r₀, hall_eq⟩
    have hτ_r₀ : τ r₀ = !σ r₀ := by
      cases h1 : σ r₀ <;> cases h2 : τ r₀ <;> revert hne_r₀ <;> simp [h1, h2]
    have hne_pt : x_σ ≠ x_τ := fun h => hne_r₀ (congrFun (policy_eq_of_basicPoint_eq n hn h) r₀)
    refine ⟨hne_pt, basicPoint_isVertex n hn σ, basicPoint_isVertex n hn τ, ?_⟩
    intro z hz hsupp
    set j₀ := actionColumn n hn r₀ (!σ r₀)
    set v_τ := basicValues (program n) (policyBasis n hn τ)
    have hv_τ_pos : 0 < v_τ r₀ := ((lp_valid n hn).2 τ).2 r₀
    have hx_τ_j₀ : x_τ j₀ = v_τ r₀ := by
      dsimp [x_τ, j₀]
      rw [← hτ_r₀, basicPoint_apply_self]
    have hx_σ_j₀ : x_σ j₀ = 0 := basicPoint_apply_opp n hn σ r₀
    let t : ℚ := z j₀ / v_τ r₀
    have ht_nonneg : 0 ≤ t := div_nonneg (hz.2 j₀) (le_of_lt hv_τ_pos)
    let w : Fin (cols n) → ℚ := fun j => (1 - t) * x_σ j + t * x_τ j
    have hw_Ax : (program n).A *ᵥ w = (program n).b := by
      change (program n).A *ᵥ ((1 - t) • x_σ + t • x_τ) = (program n).b
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        basicPoint_mulVec_A n hn σ, basicPoint_mulVec_A n hn τ]
      ext q
      change (1 - t) * 1 + t * 1 = 1
      ring
    have hz_opp : ∀ q : Fin (rows n), q ≠ r₀ → z (actionColumn n hn q (!σ q)) = 0 := by
      intro q hqr₀
      have hσq : (!σ q) = (!τ q) := congrArg not (hall_eq q hqr₀)
      apply hsupp
      · exact basicPoint_apply_opp n hn σ q
      · dsimp [x_τ]
        rw [hσq, basicPoint_apply_opp n hn τ q]
    have hw_opp : ∀ q : Fin (rows n), q ≠ r₀ → w (actionColumn n hn q (!σ q)) = 0 := by
      intro q hqr₀
      have hσq : (!σ q) = (!τ q) := congrArg not (hall_eq q hqr₀)
      dsimp [w, x_σ, x_τ]
      rw [basicPoint_apply_opp n hn σ q, hσq, basicPoint_apply_opp n hn τ q]
      ring
    have hzw_r₀ : z j₀ = w j₀ := by
      dsimp [w, t]
      rw [hx_σ_j₀, hx_τ_j₀, mul_zero, zero_add, div_mul_cancel₀ _ (ne_of_gt hv_τ_pos)]
    have hzw : z = w := eq_affine_of_opp_zero_except n hn σ r₀ hz.1 hw_Ax hz_opp hw_opp hzw_r₀
    have ht_le_one : t ≤ 1 := by
      set j₁ := actionColumn n hn r₀ (σ r₀)
      have hzj₁ : 0 ≤ z j₁ := hz.2 j₁
      rw [congrFun hzw j₁] at hzj₁
      dsimp [w, x_σ, x_τ, j₁] at hzj₁
      have hσ_opp : σ r₀ = !τ r₀ := by rw [hτ_r₀, Bool.not_not]
      rw [basicPoint_apply_self n hn σ r₀, hσ_opp, basicPoint_apply_opp n hn τ r₀, mul_zero,
        add_zero] at hzj₁
      have hv_σ_pos : 0 < basicValues (program n) (policyBasis n hn σ) r₀ :=
        ((lp_valid n hn).2 σ).2 r₀
      nlinarith
    exact ⟨t, ht_nonneg, ht_le_one, fun j => congrFun hzw j⟩
  · rintro ⟨hne_pt, _, _, hseg⟩
    have hne_pol : σ ≠ τ := fun h => hne_pt (by dsimp [x_σ, x_τ]; rw [h])
    have hex_diff : ∃ r₁ : Fin (rows n), σ r₁ ≠ τ r₁ := by
      by_contra hall
      simp only [not_exists, not_ne_iff] at hall
      exact hne_pol (funext hall)
    rcases hex_diff with ⟨r₁, hr₁⟩
    refine ⟨r₁, hr₁, ?_⟩
    intro r₂ hr₂_ne
    by_contra hr₂
    let π : Policy n := Function.update σ r₁ (τ r₁)
    set x_π := basicPoint (program n) (policyBasis n hn π)
    have hsupp : ∀ j : Fin (cols n), x_σ j = 0 → x_τ j = 0 → x_π j = 0 := by
      intro j hσ0 hτ0
      rcases exists_actionColumn n hn j with ⟨q, b, rfl⟩
      dsimp [x_σ, x_τ, x_π] at hσ0 hτ0 ⊢
      rw [basicPoint_actionColumn] at hσ0 hτ0 ⊢
      have hpos_σ := ((lp_valid n hn).2 σ).2 q
      have hpos_τ := ((lp_valid n hn).2 τ).2 q
      have hb_ne_σ : b ≠ σ q := fun h => by rw [if_pos h] at hσ0; linarith
      have hb_ne_τ : b ≠ τ q := fun h => by rw [if_pos h] at hτ0; linarith
      have hb_ne_π : b ≠ π q := by
        dsimp [π]
        by_cases hqr₁ : q = r₁
        · subst q; simpa using hb_ne_τ
        · rw [Function.update_of_ne hqr₁]; exact hb_ne_σ
      rw [if_neg hb_ne_π]
    rcases hseg x_π (basicPoint_feasible n hn π) hsupp with ⟨t, _, _, ht_eq⟩
    have hj₁ := ht_eq (actionColumn n hn r₁ (σ r₁))
    have hπ_r₁ : π r₁ = τ r₁ := Function.update_self r₁ (τ r₁) σ
    have hσ_opp_r₁ : σ r₁ = !τ r₁ := by
      cases h1 : σ r₁ <;> cases h2 : τ r₁ <;> revert hr₁ <;> simp [h1, h2]
    dsimp [x_π, x_σ, x_τ] at hj₁
    rw [basicPoint_actionColumn n hn π r₁ (σ r₁), hπ_r₁, if_neg hr₁,
        basicPoint_apply_self n hn σ r₁, hσ_opp_r₁,
        basicPoint_apply_opp n hn τ r₁] at hj₁
    have hv_σ_pos : 0 < basicValues (program n) (policyBasis n hn σ) r₁ :=
      ((lp_valid n hn).2 σ).2 r₁
    have ht1 : t = 1 := by nlinarith
    have hj₂ := ht_eq (actionColumn n hn r₂ (τ r₂))
    have hπ_r₂ : π r₂ = σ r₂ := Function.update_of_ne hr₂_ne (τ r₁) σ
    have hτ_opp_r₂ : τ r₂ = !σ r₂ := by
      cases h1 : σ r₂ <;> cases h2 : τ r₂ <;> revert hr₂ <;> simp [h1, h2]
    dsimp [x_π, x_σ, x_τ] at hj₂
    rw [basicPoint_actionColumn n hn π r₂ (τ r₂), hπ_r₂, if_neg (Ne.symm hr₂),
        basicPoint_apply_self n hn τ r₂, hτ_opp_r₂,
        basicPoint_apply_opp n hn σ r₂] at hj₂
    have hv_τ_pos : 0 < basicValues (program n) (policyBasis n hn τ) r₂ :=
      ((lp_valid n hn).2 τ).2 r₂
    have ht0 : t = 0 := by nlinarith
    linarith

lemma realizesCube_proof (n : ℕ) (hn : 3 ≤ n) : realizesCube n hn :=
  ⟨(lp_valid n hn).1,
   basicPoint_isVertex n hn,
   fun _ hvert => existsUnique_policy_of_isVertex n hn hvert,
   cubeAdjacent_iff_polytopeAdjacent n hn⟩

/-! ### Part 4: AUSO Characterization and Tie-Breaking Objective Perturbation -/

noncomputable def policyObj (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ) (σ : Policy n) : ℚ :=
  objective { program n with c := c } (basicPoint (program n) (policyBasis n hn σ))

lemma policyObj_eq_sum_basicValues (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ) (σ : Policy n) :
    policyObj n hn c σ =
      ∑ i : Fin (rows n),
        c (policyBasis n hn σ i) * basicValues (program n) (policyBasis n hn σ) i := by
  set B := policyBasis n hn σ
  dsimp [policyObj, objective, basicPoint]
  calc (∑ j : Fin (cols n), c j * ∑ i : Fin (rows n),
          if B i = j then basicValues (program n) B i else 0)
    _ = ∑ j : Fin (cols n), ∑ i : Fin (rows n),
          (if B i = j then c j * basicValues (program n) B i else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    _ = ∑ i : Fin (rows n), ∑ j : Fin (cols n),
          (if B i = j then c j * basicValues (program n) B i else 0) :=
      Finset.sum_comm
    _ = ∑ i : Fin (rows n), c (B i) * basicValues (program n) B i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq Finset.univ (B i)]
      simp

lemma objective_sub_eq_sum_reducedCost (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ)
    (σ τ : Policy n) :
    policyObj n hn c τ - policyObj n hn c σ =
      ∑ q : Fin (rows n),
        reducedCost { program n with c := c } (policyBasis n hn σ)
          (actionColumn n hn q (!σ q)) *
          basicPoint (program n) (policyBasis n hn τ) (actionColumn n hn q (!σ q)) := by
  set B := policyBasis n hn σ
  set x_τ := basicPoint (program n) (policyBasis n hn τ)
  have hAx_τ : (program n).A *ᵥ x_τ = (program n).b := basicPoint_mulVec_A n hn τ
  have hobj_τ : policyObj n hn c τ =
      (∑ i : Fin (rows n), c (B i) * x_τ (B i)) +
        ∑ q : Fin (rows n), c (actionColumn n hn q (!σ q)) * x_τ (actionColumn n hn q (!σ q)) :=
    sum_cols_eq_sum_policy n hn σ (fun j => c j * x_τ j)
  rw [hobj_τ, policyObj_eq_sum_basicValues n hn c σ]
  have hcoord : ∀ i : Fin (rows n),
      c (B i) * x_τ (B i) - c (B i) * basicValues (program n) B i =
        - ∑ q : Fin (rows n),
            (c (B i) * direction (program n) B (actionColumn n hn q (!σ q)) i) *
              x_τ (actionColumn n hn q (!σ q)) := by
    intro i
    have hi := coord_eq_of_mulVec_eq_b n hn σ hAx_τ i
    have hmul := congrArg (c (B i) * ·) hi
    rw [mul_add, Finset.mul_sum] at hmul
    have hsum : (∑ q : Fin (rows n),
        c (B i) * (direction (program n) B (actionColumn n hn q (!σ q)) i *
          x_τ (actionColumn n hn q (!σ q)))) =
        ∑ q : Fin (rows n),
          (c (B i) * direction (program n) B (actionColumn n hn q (!σ q)) i) *
            x_τ (actionColumn n hn q (!σ q)) :=
      Finset.sum_congr rfl fun q _ => by ring
    rw [hsum] at hmul
    linarith
  have hdiff : ((∑ i : Fin (rows n), c (B i) * x_τ (B i)) +
      ∑ q : Fin (rows n), c (actionColumn n hn q (!σ q)) * x_τ (actionColumn n hn q (!σ q))) -
      (∑ i : Fin (rows n), c (B i) * basicValues (program n) B i) =
      (∑ i : Fin (rows n), (c (B i) * x_τ (B i) - c (B i) * basicValues (program n) B i)) +
        ∑ q : Fin (rows n), c (actionColumn n hn q (!σ q)) * x_τ (actionColumn n hn q (!σ q)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hdiff]
  simp only [hcoord, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  have hcomb : - (∑ q : Fin (rows n), ∑ i : Fin (rows n),
        (c (B i) * direction (program n) B (actionColumn n hn q (!σ q)) i) *
          x_τ (actionColumn n hn q (!σ q))) +
      (∑ q : Fin (rows n), c (actionColumn n hn q (!σ q)) * x_τ (actionColumn n hn q (!σ q))) =
      ∑ q : Fin (rows n),
        (c (actionColumn n hn q (!σ q)) * x_τ (actionColumn n hn q (!σ q)) -
          ∑ i : Fin (rows n),
            (c (B i) * direction (program n) B (actionColumn n hn q (!σ q)) i) *
              x_τ (actionColumn n hn q (!σ q))) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hcomb]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.sum_mul]
  unfold reducedCost direction basisMatrix
  ring

lemma policyObj_update_sub (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ)
    (σ : Policy n) (r : Fin (rows n)) :
    let τ := Function.update σ r (!σ r)
    policyObj n hn c τ - policyObj n hn c σ =
      reducedCost { program n with c := c } (policyBasis n hn σ)
        (actionColumn n hn r (!σ r)) *
        basicValues (program n) (policyBasis n hn τ) r := by
  intro τ
  rw [objective_sub_eq_sum_reducedCost n hn c σ τ]
  have hterm : ∀ q : Fin (rows n),
      basicPoint (program n) (policyBasis n hn τ) (actionColumn n hn q (!σ q)) =
        if q = r then basicValues (program n) (policyBasis n hn τ) r else 0 := by
    intro q
    rw [basicPoint_actionColumn]
    by_cases hqr : q = r
    · subst q
      simp [τ]
    · have hτq : τ q = σ q := Function.update_of_ne hqr (!σ r) σ
      have hne : (!σ q) ≠ τ q := by rw [hτq]; cases σ q <;> simp
      simp [hne, hqr]
  simp [hterm]

lemma cubeAdjacent_symm {n : ℕ} {σ τ : Policy n} (h : cubeAdjacent n σ τ) :
    cubeAdjacent n τ σ := by
  rcases h with ⟨r, hne, hall⟩
  exact ⟨r, Ne.symm hne, fun q hq => (hall q hq).symm⟩

lemma cubeAdjacent_update (n : ℕ) (σ : Policy n) (r : Fin (rows n)) :
    cubeAdjacent n σ (Function.update σ r (!σ r)) := by
  refine ⟨r, ?_, ?_⟩
  · simp
  · intro q hq
    rw [Function.update_of_ne hq]

lemma transGen_cubeOrientation_lt {n : ℕ} (hn : 3 ≤ n) (c : Fin (cols n) → ℚ)
    {σ τ : Policy n} (h : Relation.TransGen (cubeOrientation n hn c) σ τ) :
    policyObj n hn c σ < policyObj n hn c τ := by
  induction h with
  | single hstep => exact hstep.2
  | tail _ hstep ih => exact lt_trans ih hstep.2

lemma isAUSO_of_no_tie (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ)
    (hno_tie : ∀ σ τ : Policy n, cubeAdjacent n σ τ → policyObj n hn c σ ≠ policyObj n hn c τ) :
    isAUSO n hn c := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ τ hadj
    rcases lt_or_gt_of_ne (hno_tie σ τ hadj) with hlt | hgt
    · exact Or.inl ⟨hadj, hlt⟩
    · exact Or.inr ⟨cubeAdjacent_symm hadj, hgt⟩
  · intro σ hcyc
    exact lt_irrefl _ (transGen_cubeOrientation_lt hn c hcyc)
  · intro face
    classical
    let S : Finset (Policy n) := Finset.univ.filter (fun σ => inCubeFace n face σ)
    let σ₀ : Policy n := fun r => (face r).getD false
    have hσ₀_face : inCubeFace n face σ₀ := by
      intro r b hfr
      dsimp [σ₀]
      rw [hfr]
      rfl
    have hS_ne : S.Nonempty := ⟨σ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ₀_face⟩⟩
    obtain ⟨σ_max, hσ_max_mem, hσ_max_ge⟩ := Finset.exists_max_image S (policyObj n hn c) hS_ne
    have hσ_max_face : inCubeFace n face σ_max := (Finset.mem_filter.mp hσ_max_mem).2
    have hσ_max_sink : ∀ τ : Policy n, inCubeFace n face τ → ¬ cubeOrientation n hn c σ_max τ := by
      intro τ hτ_face ⟨_, hlt⟩
      have hle := hσ_max_ge τ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ_face⟩)
      change policyObj n hn c σ_max < policyObj n hn c τ at hlt
      linarith
    refine ⟨σ_max, ⟨hσ_max_face, hσ_max_sink⟩, ?_⟩
    rintro σ ⟨hσ_face, hσ_sink⟩
    by_contra hne
    have hrc_neg : ∀ q : Fin (rows n), σ_max q ≠ σ q →
        reducedCost { program n with c := c } (policyBasis n hn σ)
          (actionColumn n hn q (!σ q)) < 0 := by
      intro q hq_ne
      let σ' := Function.update σ q (!σ q)
      have hσ'_face : inCubeFace n face σ' := by
        intro r b hfr
        dsimp [σ']
        by_cases hqr : r = q
        · subst r
          exfalso
          exact hq_ne (by rw [hσ_max_face q b hfr, hσ_face q b hfr])
        · rw [Function.update_of_ne hqr]
          exact hσ_face r b hfr
      have hadj : cubeAdjacent n σ σ' := cubeAdjacent_update n σ q
      have hnot_orient := hσ_sink σ' hσ'_face
      have hne_obj := hno_tie σ σ' hadj
      have hlt_obj : policyObj n hn c σ' < policyObj n hn c σ := by
        rcases lt_or_gt_of_ne hne_obj with hlt | hgt
        · exact False.elim (hnot_orient ⟨hadj, hlt⟩)
        · exact hgt
      have hsub := policyObj_update_sub n hn c σ q
      dsimp only at hsub
      have hv_pos : 0 < basicValues (program n) (policyBasis n hn σ') q :=
        ((lp_valid n hn).2 σ').2 q
      nlinarith
    have hdiff := objective_sub_eq_sum_reducedCost n hn c σ σ_max
    have hterm_le : ∀ q : Fin (rows n),
        reducedCost { program n with c := c } (policyBasis n hn σ)
          (actionColumn n hn q (!σ q)) *
          basicPoint (program n) (policyBasis n hn σ_max) (actionColumn n hn q (!σ q)) ≤ 0 := by
      intro q
      rw [basicPoint_actionColumn]
      split_ifs with hq
      · have hq_ne : σ_max q ≠ σ q := by rw [← hq]; cases σ q <;> simp
        have hrc := hrc_neg q hq_ne
        have hv_pos := ((lp_valid n hn).2 σ_max).2 q
        nlinarith
      · linarith
    have hex_q : ∃ q₀ : Fin (rows n), σ_max q₀ ≠ σ q₀ := by
      by_contra hall
      simp only [not_exists, not_ne_iff] at hall
      exact hne (funext hall).symm
    rcases hex_q with ⟨q₀, hq₀_ne⟩
    have hterm_lt : reducedCost { program n with c := c } (policyBasis n hn σ)
        (actionColumn n hn q₀ (!σ q₀)) *
        basicPoint (program n) (policyBasis n hn σ_max) (actionColumn n hn q₀ (!σ q₀)) < 0 := by
      rw [basicPoint_actionColumn, if_pos]
      · have hrc := hrc_neg q₀ hq₀_ne
        have hv_pos := ((lp_valid n hn).2 σ_max).2 q₀
        nlinarith
      · cases h1 : σ q₀ <;> cases h2 : σ_max q₀ <;> revert hq₀_ne <;> simp [h1, h2]
    have hsum_lt : (∑ q : Fin (rows n),
        reducedCost { program n with c := c } (policyBasis n hn σ)
          (actionColumn n hn q (!σ q)) *
          basicPoint (program n) (policyBasis n hn σ_max) (actionColumn n hn q (!σ q))) < 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q₀)]
      have hrest : (∑ q ∈ Finset.univ.erase q₀,
          reducedCost { program n with c := c } (policyBasis n hn σ)
            (actionColumn n hn q (!σ q)) *
            basicPoint (program n) (policyBasis n hn σ_max) (actionColumn n hn q (!σ q))) ≤ 0 :=
        Finset.sum_nonpos (fun q _ => hterm_le q)
      linarith
    have hge := hσ_max_ge σ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ_face⟩)
    linarith

lemma policyObj_update_cost (n : ℕ) (hn : 3 ≤ n) (c₁ : Fin (cols n) → ℚ)
    (j₀ : Fin (cols n)) (δ : ℚ) (u : Policy n) :
    policyObj n hn (Function.update c₁ j₀ (c₁ j₀ + δ)) u =
      policyObj n hn c₁ u + δ * basicPoint (program n) (policyBasis n hn u) j₀ := by
  dsimp [policyObj, objective]
  have hterm : ∀ j : Fin (cols n),
      Function.update c₁ j₀ (c₁ j₀ + δ) j * basicPoint (program n) (policyBasis n hn u) j =
        c₁ j * basicPoint (program n) (policyBasis n hn u) j +
          (if j = j₀ then δ * basicPoint (program n) (policyBasis n hn u) j₀ else 0) := by
    intro j
    by_cases hj : j = j₀
    · subst j; simp; ring
    · simp [hj]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma perturb_single_col (n : ℕ) (hn : 3 ≤ n) (c₁ : Fin (cols n) → ℚ) (j₀ : Fin (cols n)) :
    ∃ c₂ : Fin (cols n) → ℚ,
      (∀ u v : Policy n, policyObj n hn c₁ u < policyObj n hn c₁ v →
        policyObj n hn c₂ u < policyObj n hn c₂ v) ∧
      (∀ u v : Policy n,
        basicPoint (program n) (policyBasis n hn u) j₀ ≠
          basicPoint (program n) (policyBasis n hn v) j₀ →
        policyObj n hn c₂ u ≠ policyObj n hn c₂ v) := by
  set x := fun u : Policy n => basicPoint (program n) (policyBasis n hn u)
  have hne_pairs : (Finset.univ : Finset (Policy n × Policy n)).Nonempty :=
    ⟨(initialPolicy n, initialPolicy n), Finset.mem_univ _⟩
  let gap : Policy n × Policy n → ℚ := fun p =>
    if policyObj n hn c₁ p.1 < policyObj n hn c₁ p.2 then
      (policyObj n hn c₁ p.2 - policyObj n hn c₁ p.1) / (2 * (|x p.2 j₀ - x p.1 j₀| + 1))
    else 1
  have hgap_pos : ∀ p : Policy n × Policy n, 0 < gap p := by
    intro p
    dsimp [gap]
    split_ifs with hlt
    · have hnum : 0 < policyObj n hn c₁ p.2 - policyObj n hn c₁ p.1 := sub_pos.mpr hlt
      have hden : 0 < 2 * (|x p.2 j₀ - x p.1 j₀| + 1) := by positivity
      exact div_pos hnum hden
    · norm_num
  set δ := Finset.univ.inf' hne_pairs gap
  have hδ_pos : 0 < δ := (Finset.lt_inf'_iff hne_pairs).mpr (fun p _ => hgap_pos p)
  let c₂ := Function.update c₁ j₀ (c₁ j₀ + δ)
  have hpres : ∀ u v : Policy n, policyObj n hn c₁ u < policyObj n hn c₁ v →
      policyObj n hn c₂ u < policyObj n hn c₂ v := by
    intro u v hlt
    have hle : δ ≤ gap (u, v) := Finset.inf'_le gap (Finset.mem_univ (u, v))
    dsimp [gap] at hle
    rw [if_pos hlt] at hle
    have hden : 0 < 2 * (|x v j₀ - x u j₀| + 1) := by positivity
    rw [le_div_iff₀ hden] at hle
    have habs := neg_abs_le (x v j₀ - x u j₀)
    dsimp [c₂]
    rw [policyObj_update_cost, policyObj_update_cost]
    nlinarith [abs_nonneg (x v j₀ - x u j₀)]
  refine ⟨c₂, hpres, ?_⟩
  intro u v hne_j₀
  by_cases hne_c₁ : policyObj n hn c₁ u ≠ policyObj n hn c₁ v
  · rcases lt_or_gt_of_ne hne_c₁ with hlt | hgt
    · exact ne_of_lt (hpres u v hlt)
    · exact ne_of_gt (hpres v u hgt)
  · simp only [not_ne_iff] at hne_c₁
    dsimp [c₂]
    rw [policyObj_update_cost, policyObj_update_cost, hne_c₁]
    intro heq
    have hmul : δ * (x u j₀ - x v j₀) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with hδ0 | hdiff0
    · linarith
    · exact hne_j₀ (sub_eq_zero.mp hdiff0)

lemma exists_perturbed_cost_list (n : ℕ) (hn : 3 ≤ n) (c₀ : Fin (cols n) → ℚ)
    (L : List (Fin (cols n))) :
    ∃ c : Fin (cols n) → ℚ,
      (∀ u v : Policy n, policyObj n hn c₀ u < policyObj n hn c₀ v →
        policyObj n hn c u < policyObj n hn c v) ∧
      (∀ j ∈ L, ∀ u v : Policy n,
        basicPoint (program n) (policyBasis n hn u) j ≠
          basicPoint (program n) (policyBasis n hn v) j →
        policyObj n hn c u ≠ policyObj n hn c v) := by
  induction L with
  | nil =>
    exact ⟨c₀, fun _ _ h => h, by intro j hj; cases hj⟩
  | cons j₀ L ih =>
    rcases ih with ⟨c₁, hpres₁, hsep₁⟩
    rcases perturb_single_col n hn c₁ j₀ with ⟨c₂, hpres₂, hsep_j₀⟩
    refine ⟨c₂, fun u v h => hpres₂ u v (hpres₁ u v h), ?_⟩
    intro j hj u v hne_j
    rcases List.mem_cons.mp hj with rfl | hjL
    · exact hsep_j₀ u v hne_j
    · rcases lt_or_gt_of_ne (hsep₁ j hjL u v hne_j) with hlt | hgt
      · exact ne_of_lt (hpres₂ u v hlt)
      · exact ne_of_gt (hpres₂ v u hgt)

lemma exists_auso_cost (n : ℕ) (hn : 3 ≤ n) :
    ∃ c : Fin (cols n) → ℚ, isAUSO n hn c ∧
      ∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ := by
  rcases exists_perturbed_cost_list n hn (program n).c
      (Finset.univ : Finset (Fin (cols n))).toList with ⟨c, hpres, hsep⟩
  refine ⟨c, ?_, ?_⟩
  · apply isAUSO_of_no_tie n hn c
    intro σ τ ⟨r, hne_r, _⟩
    set j := actionColumn n hn r (σ r)
    have hmem : j ∈ (Finset.univ : Finset (Fin (cols n))).toList :=
      Finset.mem_toList.mpr (Finset.mem_univ j)
    apply hsep j hmem σ τ
    rw [basicPoint_apply_self, basicPoint_actionColumn, if_neg hne_r]
    exact ne_of_gt (((lp_valid n hn).2 σ).2 r)
  · rintro σ τ ⟨hadj, hlt⟩
    exact ⟨hadj, hpres σ τ hlt⟩

end FriedmannCunningham

open FriedmannCunningham

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    realizesCube n hn ∧
    ∃ c : Fin (cols n) → ℚ, isAUSO n hn c ∧
      ∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ :=
  ⟨realizesCube_proof n hn, exists_auso_cost n hn⟩
