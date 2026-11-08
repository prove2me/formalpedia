-- Prove2me | solution 1 for FriedmannCunningham.simplex_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:29:45.992072+00:00
-- url     : https://prove2.me/submissions/aaf4bca5-cc39-401c-9791-f9ecb71b1769

import Definitions.Def_friedmann_cunningham
import Theorems.Thm_FriedmannCunningham_mdp_lower_bound
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

/-! ### Part 2: Strict Objective Increase and Pivot Correspondence -/

lemma policyBasis_update (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    policyBasis n hn (Function.update σ r (!σ r)) =
      Function.update (policyBasis n hn σ) r (actionColumn n hn r (!σ r)) := by
  ext q
  unfold policyBasis
  by_cases hqr : q = r
  · subst hqr; simp
  · simp [hqr]

lemma basicObjective_eq_sum_basicValues (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    basicObjective (program n) (policyBasis n hn σ) =
      ∑ i : Fin (rows n),
        (program n).c (policyBasis n hn σ i) *
          basicValues (program n) (policyBasis n hn σ) i := by
  set B := policyBasis n hn σ
  dsimp [basicObjective, objective, basicPoint]
  calc (∑ j : Fin (cols n), (program n).c j * ∑ i : Fin (rows n),
          if B i = j then basicValues (program n) B i else 0)
    _ = ∑ j : Fin (cols n), ∑ i : Fin (rows n),
          (if B i = j then (program n).c j * basicValues (program n) B i else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    _ = ∑ i : Fin (rows n), ∑ j : Fin (cols n),
          (if B i = j then (program n).c j * basicValues (program n) B i else 0) :=
      Finset.sum_comm
    _ = ∑ i : Fin (rows n), (program n).c (B i) * basicValues (program n) B i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq Finset.univ (B i)]
      simp

lemma basicValues_eq_update_add_direction (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    (r i : Fin (rows n)) :
    let B := policyBasis n hn σ
    let j := actionColumn n hn r (!σ r)
    let B' := policyBasis n hn (Function.update σ r (!σ r))
    basicValues (program n) B i =
      (if i = r then 0 else basicValues (program n) B' i) +
        basicValues (program n) B' r * direction (program n) B j i := by
  intro B j B'
  set M := basisMatrix (program n) B
  set M' := basisMatrix (program n) B'
  set v := basicValues (program n) B'
  set w : Fin (rows n) → ℚ := fun k => if k = r then 0 else v k
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr ((lp_valid n hn).2 σ).1.2.1
  have hdet' : IsUnit M'.det :=
    isUnit_iff_ne_zero.mpr ((lp_valid n hn).2 (Function.update σ r (!σ r))).1.2.1
  have hM'v : M' *ᵥ v = (program n).b := by
    change M' *ᵥ (M'⁻¹ *ᵥ (program n).b) = (program n).b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M' hdet', Matrix.one_mulVec]
  have hdecomp : M' *ᵥ v = M *ᵥ w + v r • (fun q => (program n).A q j) := by
    ext q
    dsimp [mulVec, dotProduct, M, M', basisMatrix, w]
    have hterm : ∀ k : Fin (rows n),
        (program n).A q (B' k) * v k =
          (program n).A q (B k) * (if k = r then 0 else v k) +
            (if k = r then (program n).A q j * v r else 0) := by
      intro k
      by_cases hkr : k = r
      · subst k
        simp [B', policyBasis_update, j]
      · simp [hkr, B', policyBasis_update, B]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  have hbv : basicValues (program n) B = w + v r • direction (program n) B j := by
    calc basicValues (program n) B
      _ = M⁻¹ *ᵥ (M' *ᵥ v) := by rw [hM'v]; rfl
      _ = M⁻¹ *ᵥ (M *ᵥ w + v r • (fun q => (program n).A q j)) := by rw [hdecomp]
      _ = M⁻¹ *ᵥ (M *ᵥ w) + M⁻¹ *ᵥ (v r • (fun q => (program n).A q j)) :=
        Matrix.mulVec_add _ _ _
      _ = w + v r • direction (program n) B j := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hdet, Matrix.one_mulVec,
          Matrix.mulVec_smul]
        rfl
  exact congrFun hbv i

lemma basicObjective_sub_eq (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    let B := policyBasis n hn σ
    let j := actionColumn n hn r (!σ r)
    let B' := policyBasis n hn (Function.update σ r (!σ r))
    basicObjective (program n) B' - basicObjective (program n) B =
      basicValues (program n) B' r * reducedCost (program n) B j := by
  intro B j B'
  set v := basicValues (program n) B'
  rw [basicObjective_eq_sum_basicValues n hn (Function.update σ r (!σ r)),
      basicObjective_eq_sum_basicValues n hn σ]
  have hB' : ∀ i : Fin (rows n),
      (program n).c (B' i) * v i =
        (if i = r then 0 else (program n).c (B i) * v i) +
          (if i = r then (program n).c j * v r else 0) := by
    intro i
    by_cases hir : i = r
    · subst i
      simp [B', policyBasis_update, j]
    · simp [hir, B', policyBasis_update, B]
  have hB : ∀ i : Fin (rows n),
      (program n).c (B i) * basicValues (program n) B i =
        (if i = r then 0 else (program n).c (B i) * v i) +
          v r * ((program n).c (B i) * direction (program n) B j i) := by
    intro i
    have hi := basicValues_eq_update_add_direction n hn σ r i
    dsimp only at hi
    rw [hi]
    split_ifs <;> ring
  change (∑ i, (program n).c (B' i) * v i) -
    (∑ i, (program n).c (B i) * basicValues (program n) B i) = _
  simp only [hB', hB, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    ← Finset.mul_sum]
  unfold reducedCost
  ring

lemma basicObjective_lt_of_mdpImproving (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    {r : Fin (rows n)} (himp : mdpImproving n hn σ r) :
    basicObjective (program n) (policyBasis n hn σ) <
      basicObjective (program n) (policyBasis n hn (Function.update σ r (!σ r))) := by
  have hdiff := basicObjective_sub_eq n hn σ r
  dsimp only at hdiff
  have hv_pos : 0 < basicValues (program n)
      (policyBasis n hn (Function.update σ r (!σ r))) r :=
    ((lp_valid n hn).2 (Function.update σ r (!σ r))).2 r
  have hrc_pos : 0 < reducedCost (program n) (policyBasis n hn σ)
      (actionColumn n hn r (!σ r)) :=
    (((policy_pivot n hn σ).2 r).1.mp himp).2
  have hmul : 0 < basicValues (program n) (policyBasis n hn (Function.update σ r (!σ r))) r *
      reducedCost (program n) (policyBasis n hn σ) (actionColumn n hn r (!σ r)) :=
    mul_pos hv_pos hrc_pos
  linarith

lemma exists_mdpImproving_of_improving (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    {k : Fin (cols n)} (himp : improving (program n) (policyBasis n hn σ) k) :
    ∃ q : Fin (rows n), k = actionColumn n hn q (!σ q) ∧ mdpImproving n hn σ q := by
  rcases exists_actionColumn n hn k with ⟨q, b, rfl⟩
  have hne : policyBasis n hn σ q ≠ actionColumn n hn q b := himp.1 q
  have hb : b = !σ q := by
    cases hb1 : b <;> cases hσ1 : σ q <;> simp_all [policyBasis]
  subst hb
  exact ⟨q, rfl, ((policy_pivot n hn σ).2 q).1.mpr himp⟩

lemma simplex_lower_bound_proof (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → FriedmannSimplex.State (rows n) (cols n)),
      s 0 = initialState n hn ∧
      FriedmannSimplex.cunninghamRun (program n) (order n) s T ∧
      2 ^ n ≤ T ∧
      ∀ t, t < T →
        FriedmannSimplex.basicObjective (program n) (s t).basis <
          FriedmannSimplex.basicObjective (program n) (s (t + 1)).basis := by
  rcases mdp_lower_bound n hn with ⟨T, s_mdp, ⟨hinit, hstep, hopt⟩, hT⟩
  let s : ℕ → State (rows n) (cols n) := fun t =>
    { basis := policyBasis n hn (s_mdp t).policy
      last := (s_mdp t).last }
  refine ⟨T, s, ?_, ?_, hT, ?_⟩
  · dsimp [s]
    rw [hinit]
    rfl
  · refine ⟨((lp_valid n hn).2 (s_mdp 0).policy).1, ?_, ?_⟩
    · intro t ht
      rcases hstep t ht with ⟨r, himp, hmin, hpol, hlast⟩
      refine ⟨actionColumn n hn r (!(s_mdp t).policy r), ?_, ?_, ?_⟩
      · refine ⟨(((policy_pivot n hn (s_mdp t).policy).2 r).1.mp himp), ?_⟩
        intro k hk
        rcases exists_mdpImproving_of_improving n hn (s_mdp t).policy hk with ⟨q, rfl, hq⟩
        exact hmin q hq
      · dsimp [s]
        rw [hpol]
        exact ((policy_pivot n hn (s_mdp t).policy).2 r).2 himp
      · dsimp [s, order]
        exact hlast
    · refine ⟨((lp_valid n hn).2 (s_mdp T).policy).1, ?_⟩
      intro k hk
      rcases exists_mdpImproving_of_improving n hn (s_mdp T).policy hk with ⟨q, _, hq⟩
      exact hopt q hq
  · intro t ht
    rcases hstep t ht with ⟨r, himp, _, hpol, _⟩
    dsimp [s]
    rw [hpol]
    exact basicObjective_lt_of_mdpImproving n hn (s_mdp t).policy himp

end FriedmannCunningham

open FriedmannCunningham

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → FriedmannSimplex.State (rows n) (cols n)),
      s 0 = initialState n hn ∧
      FriedmannSimplex.cunninghamRun (program n) (order n) s T ∧
      2 ^ n ≤ T ∧
      ∀ t, t < T →
        FriedmannSimplex.basicObjective (program n) (s t).basis <
          FriedmannSimplex.basicObjective (program n) (s (t + 1)).basis :=
  simplex_lower_bound_proof n hn
