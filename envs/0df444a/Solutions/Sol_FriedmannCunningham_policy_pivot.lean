-- Prove2me | solution 1 for FriedmannCunningham.policy_pivot
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:21:47.250241+00:00
-- url     : https://prove2.me/submissions/583d9031-2413-4550-b39f-53781f92238b

import Definitions.Def_friedmann_cunningham
import Theorems.Thm_FriedmannCunningham_mdp_valid
import Theorems.Thm_FriedmannCunningham_lp_valid
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

lemma policyBasis_ne_opp_actionColumn (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    (r i : Fin (rows n)) :
    policyBasis n hn σ i ≠ actionColumn n hn r (!σ r) := by
  intro h
  rcases actionColumn_inj hn h with ⟨rfl, hb⟩
  cases σ i <;> simp at hb

/-! ### Part 2: Objective Identity -/

lemma policyValue_eq_sum (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (q : Fin (rows n)) :
    policyValue n hn σ q =
      ∑ i : Fin (rows n),
        (basisMatrix (program n) (policyBasis n hn σ))⁻¹ i q *
          actionReward n hn i (σ i) := by
  unfold policyValue
  rw [← Matrix.transpose_nonsing_inv]
  rfl

lemma basicValues_eq_sum (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (i : Fin (rows n)) :
    basicValues (program n) (policyBasis n hn σ) i =
      ∑ q : Fin (rows n), (basisMatrix (program n) (policyBasis n hn σ))⁻¹ i q := by
  dsimp [basicValues, mulVec, dotProduct]
  have hb : (program n).b = fun _ => 1 := rfl
  simp [hb]

lemma basicObjective_eq_sum_policyValue (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    basicObjective (program n) (policyBasis n hn σ) =
      ∑ r : Fin (rows n), policyValue n hn σ r := by
  set B := policyBasis n hn σ
  have hobj : basicObjective (program n) B =
      ∑ i : Fin (rows n),
        actionReward n hn i (σ i) * basicValues (program n) (policyBasis n hn σ) i := by
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
      _ = ∑ i : Fin (rows n), actionReward n hn i (σ i) * basicValues (program n) B i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_ite_eq Finset.univ (B i)]
        simp [B, policyBasis, actionReward]
  rw [hobj]
  simp only [basicValues_eq_sum, policyValue_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun i _ => by ring

/-! ### Part 3: Reduced Cost and Improving Equivalence -/

lemma reducedCost_opp_actionColumn (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    reducedCost (program n) (policyBasis n hn σ) (actionColumn n hn r (!σ r)) =
      actionReward n hn r (!σ r) - policyValue n hn σ r +
        ∑ q : Fin (rows n), transition n hn r (!σ r) q * policyValue n hn σ q := by
  set B := policyBasis n hn σ
  set M := basisMatrix (program n) B
  set j := actionColumn n hn r (!σ r)
  have hdir : (∑ i : Fin (rows n), (program n).c (B i) * direction (program n) B j i) =
      ∑ q : Fin (rows n), policyValue n hn σ q * (program n).A q j := by
    calc (∑ i : Fin (rows n), (program n).c (B i) * direction (program n) B j i)
      _ = ∑ i : Fin (rows n), ∑ q : Fin (rows n),
            (M⁻¹ i q * actionReward n hn i (σ i)) * (program n).A q j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp [direction, mulVec, dotProduct, B, policyBasis, actionReward]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring
      _ = ∑ q : Fin (rows n), ∑ i : Fin (rows n),
            (M⁻¹ i q * actionReward n hn i (σ i)) * (program n).A q j :=
        Finset.sum_comm
      _ = ∑ q : Fin (rows n), policyValue n hn σ q * (program n).A q j := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_mul, ← policyValue_eq_sum]
  have hA : ∀ q : Fin (rows n), policyValue n hn σ q * (program n).A q j =
      (if q = r then policyValue n hn σ q else 0) -
        transition n hn r (!σ r) q * policyValue n hn σ q := by
    intro q
    dsimp [j]
    unfold transition
    split_ifs <;> ring
  unfold reducedCost
  rw [hdir]
  simp only [hA, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  change actionReward n hn r (!σ r) -
    (policyValue n hn σ r - ∑ x, transition n hn r (!σ r) x * policyValue n hn σ x) = _
  ring

lemma mdpImproving_iff_improving (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    mdpImproving n hn σ r ↔
      improving (program n) (policyBasis n hn σ) (actionColumn n hn r (!σ r)) := by
  unfold mdpImproving improving
  rw [reducedCost_opp_actionColumn]
  constructor
  · intro h
    exact ⟨policyBasis_ne_opp_actionColumn n hn σ r, by linarith⟩
  · rintro ⟨_, h⟩
    linarith

/-! ### Part 4: Leaving Variable and Pivot Correspondence -/

lemma policyBasis_update (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    policyBasis n hn (Function.update σ r (!σ r)) =
      Function.update (policyBasis n hn σ) r (actionColumn n hn r (!σ r)) := by
  ext q
  unfold policyBasis
  by_cases hqr : q = r
  · subst hqr; simp
  · simp [hqr]

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

lemma leaving_opp_actionColumn (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n)) :
    leaving (program n) (policyBasis n hn σ) (actionColumn n hn r (!σ r)) r := by
  set B := policyBasis n hn σ
  set j := actionColumn n hn r (!σ r)
  set σ' := Function.update σ r (!σ r)
  set B' := policyBasis n hn σ'
  have hu_pos : ∀ i, 0 < basicValues (program n) B i := ((lp_valid n hn).2 σ).2
  have hv_pos : ∀ i, 0 < basicValues (program n) B' i := ((lp_valid n hn).2 σ').2
  have hr_eq := basicValues_eq_update_add_direction n hn σ r r
  dsimp only at hr_eq
  rw [if_pos rfl, zero_add] at hr_eq
  have hdr_pos : 0 < direction (program n) B j r := by
    have hur := hu_pos r
    have hvr := hv_pos r
    nlinarith
  refine ⟨hdr_pos, ?_⟩
  intro i hdi_pos
  have hi_eq := basicValues_eq_update_add_direction n hn σ r i
  dsimp only at hi_eq
  have hdiv_r : basicValues (program n) B r / direction (program n) B j r =
      basicValues (program n) B' r := by
    rw [hr_eq, mul_div_cancel_right₀ _ (ne_of_gt hdr_pos)]
  rw [hdiv_r, le_div_iff₀ hdi_pos]
  have hnonneg : 0 ≤ (if i = r then 0 else basicValues (program n) B' i) := by
    split_ifs
    · linarith
    · exact le_of_lt (hv_pos i)
  linarith

lemma pivot_of_mdpImproving (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) (r : Fin (rows n))
    (himp : mdpImproving n hn σ r) :
    pivot (program n) (policyBasis n hn σ) (actionColumn n hn r (!σ r))
      (policyBasis n hn (Function.update σ r (!σ r))) := by
  refine ⟨((lp_valid n hn).2 σ).1,
    (mdpImproving_iff_improving n hn σ r).mp himp,
    r,
    leaving_opp_actionColumn n hn σ r,
    policyBasis_update n hn σ r,
    ((lp_valid n hn).2 (Function.update σ r (!σ r))).1⟩

end FriedmannCunningham

open FriedmannCunningham
open scoped BigOperators

theorem solution (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    FriedmannSimplex.basicObjective (program n) (policyBasis n hn σ) =
      (∑ r : Fin (rows n), policyValue n hn σ r) ∧
    ∀ r,
      (mdpImproving n hn σ r ↔
        FriedmannSimplex.improving (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))) ∧
      (mdpImproving n hn σ r →
        FriedmannSimplex.pivot (program n) (policyBasis n hn σ)
          (actionColumn n hn r (!σ r))
          (policyBasis n hn (Function.update σ r (!σ r)))) :=
  ⟨basicObjective_eq_sum_policyValue n hn σ,
   fun r => ⟨mdpImproving_iff_improving n hn σ r, pivot_of_mdpImproving n hn σ r⟩⟩
