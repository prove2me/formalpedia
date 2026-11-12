-- Prove2me | solution 1 for BudgetedAffine.Disjoint.online_cover_exists
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:38:21.198564+00:00
-- url     : https://prove2.me/submissions/ee2aaaf2-d406-40e3-a9a3-26c9d66850cc

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover

open scoped Classical
open Matrix

namespace BudgetedAffine.Disjoint

/-! ### Elementary real and logarithmic bounds -/

private lemma exp_one_lt_three : Real.exp 1 < 3 := by
  have h1 : (7 / 8 : ℝ) ≤ Real.exp (-1 / 8 : ℝ) := by
    have h := Real.add_one_le_exp (-1 / 8 : ℝ)
    linarith
  have hpow : (7 / 8 : ℝ) ^ 8 ≤ (Real.exp (-1 / 8 : ℝ)) ^ 8 :=
    pow_le_pow_left₀ (by norm_num) h1 8
  rw [← Real.exp_nat_mul] at hpow
  have hexp_neg : (8 : ℕ) * (-1 / 8 : ℝ) = -1 := by norm_num
  rw [hexp_neg] at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.exp_pos 1).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
  have hnum : (1 : ℝ) < (7 / 8 : ℝ) ^ 8 * 3 := by norm_num
  have hlt : (7 / 8 : ℝ) ^ 8 * Real.exp 1 < (7 / 8 : ℝ) ^ 8 * 3 := lt_of_le_of_lt hmul hnum
  exact lt_of_mul_lt_mul_left hlt (by positivity)

private lemma one_lt_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hn
  rw [Real.lt_log_iff_exp_lt hn_pos]
  exact lt_of_lt_of_le exp_one_lt_three (by exact_mod_cast hn)

private lemma log_eighteen_lt_three : Real.log 18 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : (17 / 16 : ℝ) ≤ Real.exp (1 / 16 : ℝ) := by
    have h := Real.add_one_le_exp (1 / 16 : ℝ)
    linarith
  have hpow : (17 / 16 : ℝ) ^ 48 ≤ (Real.exp (1 / 16 : ℝ)) ^ 48 :=
    pow_le_pow_left₀ (by norm_num) h1 48
  rw [← Real.exp_nat_mul] at hpow
  have hexp3 : (48 : ℕ) * (1 / 16 : ℝ) = 3 := by norm_num
  rw [hexp3] at hpow
  have hnum : (18 : ℝ) < (17 / 16 : ℝ) ^ 48 := by norm_num
  exact lt_of_lt_of_le hnum hpow

private lemma log_le_sub_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 := by
  rw [Real.log_le_iff_le_exp hx]
  have h := Real.add_one_le_exp (x - 1)
  linarith

private lemma half_le_log_one_add {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r / 2 ≤ Real.log (1 + r) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 : 1 - r / 2 ≤ Real.exp (-(r / 2)) := by
    have h := Real.add_one_le_exp (-(r / 2))
    linarith
  have hprod : 1 ≤ (1 - r / 2) * (1 + r) := by nlinarith
  have hle : 1 ≤ Real.exp (-(r / 2)) * (1 + r) :=
    hprod.trans (mul_le_mul_of_nonneg_right h1 (by linarith))
  have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_pos (r / 2)).le
  have hexp_cancel : Real.exp (r / 2) * (Real.exp (-(r / 2)) * (1 + r)) = 1 + r := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  linarith

private noncomputable def stepCap (n : ℕ) : ℕ :=
  Nat.ceil (16 * (n : ℝ) * Real.log n)

private lemma stepCap_lower {n : ℕ} :
    16 * (n : ℝ) * Real.log n ≤ (stepCap n : ℝ) :=
  Nat.le_ceil _

private lemma one_add_stepCap_div_lt {n : ℕ} (hn : 3 ≤ n) :
    1 + (stepCap n : ℝ) / n < 18 * Real.log n := by
  have hL : 1 < Real.log n := one_lt_log_of_three_le hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hnL_gt1 : 1 < (n : ℝ) * Real.log n := by nlinarith
  have hceil : (stepCap n : ℝ) < 16 * (n : ℝ) * Real.log n + 1 := by
    unfold stepCap
    exact Nat.ceil_lt_add_one (by positivity)
  have hnum : (n : ℝ) + (stepCap n : ℝ) < 18 * (n : ℝ) * Real.log n := by nlinarith
  have hdiv : ((n : ℝ) + (stepCap n : ℝ)) / n < (18 * (n : ℝ) * Real.log n) / n :=
    div_lt_div_of_pos_right hnum hn_pos
  have hlhs : 1 + (stepCap n : ℝ) / n = ((n : ℝ) + (stepCap n : ℝ)) / n := by
    field_simp [hn_pos.ne']
  have hrhs : (18 * (n : ℝ) * Real.log n) / n = 18 * Real.log n := by
    field_simp [hn_pos.ne']
  linarith

private lemma two_mul_n_mul_log_lt_stepCap {n : ℕ} (hn : 3 ≤ n) :
    2 * (n : ℝ) * Real.log ((n : ℝ) + stepCap n) < (stepCap n : ℝ) := by
  have hL : 1 < Real.log n := one_lt_log_of_three_le hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hL_pos : 0 < Real.log n := by linarith
  have hceil : (stepCap n : ℝ) < 16 * (n : ℝ) * Real.log n + 1 := by
    unfold stepCap
    exact Nat.ceil_lt_add_one (by positivity)
  have hsum_pos : 0 < (n : ℝ) + stepCap n := by positivity
  have hsum_lt : (n : ℝ) + stepCap n < 18 * (n : ℝ) * Real.log n := by nlinarith
  have hlog_lt : Real.log ((n : ℝ) + stepCap n) < Real.log (18 * (n : ℝ) * Real.log n) :=
    Real.log_lt_log hsum_pos hsum_lt
  have h18n_ne : (18 * (n : ℝ)) ≠ 0 := by positivity
  have hlog_split : Real.log (18 * (n : ℝ) * Real.log n) =
      Real.log 18 + Real.log n + Real.log (Real.log n) := by
    rw [Real.log_mul h18n_ne hL_pos.ne', Real.log_mul (by norm_num) hn_pos.ne']
  have hlog_ub : Real.log ((n : ℝ) + stepCap n) < 4 * Real.log n := by
    have h1 := log_eighteen_lt_three
    have h2 := log_le_sub_one hL_pos
    linarith
  have hmul : 2 * (n : ℝ) * Real.log ((n : ℝ) + stepCap n) < 8 * (n : ℝ) * Real.log n := by
    nlinarith
  have hlb := stepCap_lower (n := n)
  nlinarith

private lemma sum_pow_two_le (k : ℕ) :
    ∑ m ∈ Finset.range (k + 1), (2 : ℝ) ^ m ≤ 2 * (2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-! ### Row classification and single-row minimum cost -/

private noncomputable def Jpos {n : ℕ} (d : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < d j)

private noncomputable def posCols {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) : Finset (Fin n) :=
  (Jpos d).filter (fun j => 0 < M i j)

private def hasZeroCover {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) : Prop :=
  ∃ j : Fin n, d j = 0 ∧ 0 < M i j

private noncomputable def rowAlpha {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) (hpos : (posCols M d i).Nonempty) : ℝ :=
  (posCols M d i).inf' hpos (fun j => d j / M i j)

private lemma exists_col_eq_rowAlpha {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) (hpos : (posCols M d i).Nonempty) :
    ∃ j ∈ posCols M d i, d j / M i j = rowAlpha M d i hpos := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hpos (fun j => d j / M i j)
  exact ⟨j, hj, hjeq.symm⟩

private lemma rowAlpha_pos {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) (hpos : (posCols M d i).Nonempty) :
    0 < rowAlpha M d i hpos := by
  obtain ⟨j, hj, hjeq⟩ := exists_col_eq_rowAlpha M d i hpos
  have hj' := Finset.mem_filter.mp hj
  have hdj : 0 < d j := (Finset.mem_filter.mp hj'.1).2
  have hMij : 0 < M i j := hj'.2
  rw [← hjeq]
  positivity

private lemma mulVec_eq_sum_Jpos {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d)
    {i : Fin m} (hnoZero : ¬ hasZeroCover M d i) (z : Fin n → ℝ) :
    (M *ᵥ z) i = ∑ j ∈ Jpos d, M i j * z j := by
  simp only [mulVec, dotProduct]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hjnot => ?_
  have hdj_le : d j ≤ 0 := not_lt.mp (fun hlt => hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩))
  have hdj0 : d j = 0 := le_antisymm hdj_le (hd j)
  have hMle : M i j ≤ 0 := not_lt.mp (fun hMpos => hnoZero ⟨j, hdj0, hMpos⟩)
  have hM0 : M i j = 0 := le_antisymm hMle (hM i j)
  simp [hM0]

private lemma rowAlpha_le_dotProduct {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d)
    {i : Fin m} (hnoZero : ¬ hasZeroCover M d i) (hpos : (posCols M d i).Nonempty)
    {y : Fin n → ℝ} (hy_nn : 0 ≤ y) (hy_cov : 1 ≤ (M *ᵥ y) i) :
    rowAlpha M d i hpos ≤ d ⬝ᵥ y := by
  have hsum_eq := mulVec_eq_sum_Jpos M d hM hd hnoZero y
  rw [hsum_eq] at hy_cov
  have hα_pos : 0 < rowAlpha M d i hpos := rowAlpha_pos M d i hpos
  have hterm_le : ∀ j ∈ Jpos d, rowAlpha M d i hpos * (M i j * y j) ≤ d j * y j := by
    intro j hj
    by_cases hMpos : 0 < M i j
    · have hj_pos : j ∈ posCols M d i := Finset.mem_filter.mpr ⟨hj, hMpos⟩
      have hinf : rowAlpha M d i hpos ≤ d j / M i j := Finset.inf'_le _ hj_pos
      have hmul : rowAlpha M d i hpos * M i j ≤ d j := (le_div_iff₀ hMpos).mp hinf
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hmul (hy_nn j)
    · have hM0 : M i j = 0 := le_antisymm (not_lt.mp hMpos) (hM i j)
      rw [hM0, zero_mul, mul_zero]
      exact mul_nonneg (hd j) (hy_nn j)
  calc
    rowAlpha M d i hpos
      ≤ rowAlpha M d i hpos * ∑ j ∈ Jpos d, M i j * y j := by nlinarith
    _ = ∑ j ∈ Jpos d, rowAlpha M d i hpos * (M i j * y j) := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Jpos d, d j * y j := Finset.sum_le_sum hterm_le
    _ ≤ ∑ j : Fin n, d j * y j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => mul_nonneg (hd j) (hy_nn j))
    _ = d ⬝ᵥ y := rfl

/-! ### Online doubling primal-dual algorithm -/

private structure PhaseState (n : ℕ) where
  B₀ : ℝ
  k : ℕ
  t : ℕ
  x : Fin n → ℝ

private structure State (n : ℕ) where
  y_zero : Fin n → ℝ
  y_pos : Fin n → ℝ
  phase : Option (PhaseState n)

private def State.y {n : ℕ} (st : State n) : Fin n → ℝ :=
  st.y_zero + st.y_pos

private def initState (n : ℕ) : State n :=
  { y_zero := 0, y_pos := 0, phase := none }

private noncomputable def initX {n : ℕ} (d : Fin n → ℝ) (B : ℝ) : Fin n → ℝ :=
  fun j => if j ∈ Jpos d then B / n else 0

private noncomputable def initPhase {n : ℕ} (d : Fin n → ℝ) (B₀ : ℝ) :
    PhaseState n × (Fin n → ℝ) :=
  ({ B₀ := B₀, k := 0, t := 0, x := initX d B₀ },
   fun j => if j ∈ Jpos d then (B₀ / n) / d j else 0)

private noncomputable def abortStep {n : ℕ} (d : Fin n → ℝ)
    (ps : PhaseState n) (y_pos : Fin n → ℝ) : PhaseState n × (Fin n → ℝ) :=
  let k' := ps.k + 1
  let B' := (2 : ℝ) ^ k' * ps.B₀
  let x' := initX d B'
  ({ B₀ := ps.B₀, k := k', t := 0, x := x' },
   fun j => y_pos j + if j ∈ Jpos d then x' j / d j else 0)

private noncomputable def multStep {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) (ps : PhaseState n) (y_pos : Fin n → ℝ) :
    PhaseState n × (Fin n → ℝ) :=
  let B := (2 : ℝ) ^ ps.k * ps.B₀
  let x' : Fin n → ℝ := fun j =>
    if j ∈ Jpos d then ps.x j * (1 + (B / n) * (M i j / d j)) else 0
  ({ B₀ := ps.B₀, k := ps.k, t := ps.t + 1, x := x' },
   fun j => y_pos j + if j ∈ Jpos d then (x' j - ps.x j) / d j else 0)

private noncomputable def rowFracCov {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Jpos d, M i j * (x j / d j)

private noncomputable def coverLoop {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (i : Fin m) (α : ℝ) :
    ℕ → PhaseState n → (Fin n → ℝ) → PhaseState n × (Fin n → ℝ)
  | 0, ps, y_pos => (ps, y_pos)
  | fuel + 1, ps, y_pos =>
    if 1 ≤ rowFracCov M d i ps.x then (ps, y_pos)
    else if (2 : ℝ) ^ ps.k * ps.B₀ < α ∨ stepCap n ≤ ps.t then
      let res := abortStep d ps y_pos
      coverLoop M d i α fuel res.1 res.2
    else
      let res := multStep M d i ps y_pos
      coverLoop M d i α fuel res.1 res.2

private noncomputable def zeroStep {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (st : State n) (i : Fin m) : State n :=
  let yz' : Fin n → ℝ := fun j =>
    if d j = 0 ∧ 0 < M i j then max (st.y_zero j) (1 / M i j) else st.y_zero j
  { y_zero := yz', y_pos := st.y_pos, phase := st.phase }

private noncomputable def stepRow {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (st : State n) (i : Fin m) : State n :=
  if hasZeroCover M d i then
    zeroStep M d st i
  else (
    if hpos : (posCols M d i).Nonempty then
      let α := rowAlpha M d i hpos
      let init := match st.phase with
        | some ps => (ps, st.y_pos)
        | none => initPhase d α
      let K_bound := Nat.ceil ((n : ℝ) * α / init.1.B₀) + 1
      let fuel := (K_bound + 1) * (stepCap n + 1)
      let res := coverLoop M d i α fuel init.1 init.2
      { y_zero := st.y_zero, y_pos := res.2, phase := some res.1 }
    else
      st)

private noncomputable def stepBatch {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (st : State n) (S : Finset (Fin m)) : State n :=
  (S.sort (· ≤ ·)).foldl (stepRow M d) st

private noncomputable def runBatches {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (s : List (Finset (Fin m))) : State n :=
  s.foldl (stepBatch M d) (initState n)

/-! ### Monotonicity and structural invariants -/

private structure PhaseStructInv {n : ℕ} (d : Fin n → ℝ)
    (ps : PhaseState n) (y_pos : Fin n → ℝ) : Prop where
  B₀_pos : 0 < ps.B₀
  t_le : ps.t ≤ stepCap n
  x_lb : ∀ j ∈ Jpos d, ((2 : ℝ) ^ ps.k * ps.B₀) / n ≤ ps.x j
  x_sum : ∑ j ∈ Jpos d, ps.x j ≤ ((2 : ℝ) ^ ps.k * ps.B₀) * (1 + (ps.t : ℝ) / n)
  y_cost : d ⬝ᵥ y_pos ≤
    (∑ m ∈ Finset.range ps.k, (2 : ℝ) ^ m * ps.B₀) * (1 + (stepCap n : ℝ) / n) +
      ∑ j ∈ Jpos d, ps.x j
  y_lb : ∀ j ∈ Jpos d, ps.x j / d j ≤ y_pos j
  y_nn : 0 ≤ y_pos
  y_supp : ∀ j, j ∉ Jpos d → y_pos j = 0

private structure StateStructInv {n : ℕ} (d : Fin n → ℝ) (st : State n) : Prop where
  yz_nn : 0 ≤ st.y_zero
  yz_supp : ∀ j, d j ≠ 0 → st.y_zero j = 0
  phase_inv : match st.phase with
    | none => st.y_pos = 0
    | some ps => PhaseStructInv d ps st.y_pos

private lemma dotProduct_Jpos_eq {n : ℕ} (d : Fin n → ℝ) {z : Fin n → ℝ}
    (hz : ∀ j, j ∉ Jpos d → z j = 0) :
    d ⬝ᵥ z = ∑ j ∈ Jpos d, d j * z j := by
  simp only [dotProduct]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hjnot => ?_
  rw [hz j hjnot, mul_zero]

private lemma sum_initX_le {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∑ j ∈ Jpos d, initX d B j ≤ B := by
  have h1 : ∑ j ∈ Jpos d, initX d B j = ((Jpos d).card : ℝ) * (B / n) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [initX, hj]
  rw [h1]
  have hcard : ((Jpos d).card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_univ (Jpos d)).trans_eq (Fintype.card_fin n)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc
    ((Jpos d).card : ℝ) * (B / n) ≤ (n : ℝ) * (B / n) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hB hn_pos.le)
    _ = B := mul_div_cancel₀ B hn_pos.ne'

private lemma initPhase_structInv {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ)
    {B₀ : ℝ} (hB₀ : 0 < B₀) :
    PhaseStructInv d (initPhase d B₀).1 (initPhase d B₀).2 := by
  let res := initPhase d B₀
  have hsupp : ∀ j, j ∉ Jpos d → res.2 j = 0 := by
    intro j hj
    dsimp only [res]
    simp [initPhase, hj]
  refine
    { B₀_pos := hB₀
      t_le := Nat.zero_le _
      x_lb := fun j hj => by simp [initPhase, initX, hj]
      x_sum := by
        simpa [initPhase] using sum_initX_le hn d hB₀.le
      y_cost := by
        rw [dotProduct_Jpos_eq d hsupp]
        simp only [initPhase, Finset.range_zero, Finset.sum_empty, zero_mul, zero_add]
        refine le_of_eq (Finset.sum_congr rfl fun j hj => ?_)
        have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
        dsimp only [res]
        simp [initPhase, initX, hj, mul_div_cancel₀ _ hdj.ne']
      y_lb := fun j hj => by simp [initPhase, initX, hj]
      y_nn := fun j => by
        by_cases hj : j ∈ Jpos d
        · have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
          simp only [initPhase, hj, ↓reduceIte]
          positivity
        · simp [initPhase, hj]
      y_supp := hsupp }

private lemma abortStep_mono {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ)
    {ps : PhaseState n} (hB₀ : 0 < ps.B₀) (y_pos : Fin n → ℝ) :
    y_pos ≤ (abortStep d ps y_pos).2 := by
  intro j
  by_cases hj : j ∈ Jpos d
  · have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
    have hadd : 0 ≤ initX d ((2 : ℝ) ^ (ps.k + 1) * ps.B₀) j / d j := by
      simp only [initX, hj, ↓reduceIte]
      positivity
    simpa [abortStep, hj] using hadd
  · simp [abortStep, hj]

private lemma abortStep_structInv {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ)
    {ps : PhaseState n} {y_pos : Fin n → ℝ} (hinv : PhaseStructInv d ps y_pos) :
    PhaseStructInv d (abortStep d ps y_pos).1 (abortStep d ps y_pos).2 := by
  let res := abortStep d ps y_pos
  have hB₀ := hinv.B₀_pos
  have hB'_pos : 0 < (2 : ℝ) ^ (ps.k + 1) * ps.B₀ := by positivity
  have hsupp : ∀ j, j ∉ Jpos d → res.2 j = 0 := by
    intro j hj
    dsimp only [res]
    simp [abortStep, hj, hinv.y_supp j hj]
  have hmono := abortStep_mono hn d hB₀ y_pos
  refine
    { B₀_pos := hB₀
      t_le := Nat.zero_le _
      x_lb := fun j hj => by simp [abortStep, initX, hj]
      x_sum := by
        simpa [abortStep] using sum_initX_le hn d hB'_pos.le
      y_cost := by
        rw [dotProduct_Jpos_eq d hsupp]
        have hcost_old := hinv.y_cost
        rw [dotProduct_Jpos_eq d hinv.y_supp] at hcost_old
        have hadd_eq : ∑ j ∈ Jpos d, d j * res.2 j =
            ∑ j ∈ Jpos d, d j * y_pos j + ∑ j ∈ Jpos d, res.1.x j := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
          dsimp only [res]
          simp only [abortStep, hj, ↓reduceIte, mul_add]
          rw [mul_div_cancel₀ _ hdj.ne']
        have hx_cap : ∑ j ∈ Jpos d, ps.x j ≤
            ((2 : ℝ) ^ ps.k * ps.B₀) * (1 + (stepCap n : ℝ) / n) := by
          refine hinv.x_sum.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
          have ht : (ps.t : ℝ) ≤ stepCap n := Nat.cast_le.mpr hinv.t_le
          have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
          linarith [div_le_div_of_nonneg_right ht hn_pos.le]
        rw [hadd_eq]
        have hrng : (∑ m ∈ Finset.range (ps.k + 1), (2 : ℝ) ^ m * ps.B₀) *
            (1 + (stepCap n : ℝ) / n) =
            (∑ m ∈ Finset.range ps.k, (2 : ℝ) ^ m * ps.B₀) * (1 + (stepCap n : ℝ) / n) +
              ((2 : ℝ) ^ ps.k * ps.B₀) * (1 + (stepCap n : ℝ) / n) := by
          rw [Finset.sum_range_succ, add_mul]
        change ∑ j ∈ Jpos d, d j * y_pos j + ∑ j ∈ Jpos d, res.1.x j ≤
          (∑ m ∈ Finset.range (ps.k + 1), (2 : ℝ) ^ m * ps.B₀) *
            (1 + (stepCap n : ℝ) / n) + ∑ j ∈ Jpos d, res.1.x j
        linarith
      y_lb := fun j hj => by
        have hy0 : 0 ≤ y_pos j := hinv.y_nn j
        simp only [abortStep, hj, ↓reduceIte]
        linarith
      y_nn := fun j => (hinv.y_nn j).trans (hmono j)
      y_supp := hsupp }

private lemma multStep_mono {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (i : Fin m)
    {ps : PhaseState n} (hB₀ : 0 < ps.B₀)
    (hx_nn : ∀ j ∈ Jpos d, 0 ≤ ps.x j) (y_pos : Fin n → ℝ) :
    y_pos ≤ (multStep M d i ps y_pos).2 := by
  intro j
  by_cases hj : j ∈ Jpos d
  · have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
    have hMij : 0 ≤ M i j := hM i j
    have hxj : 0 ≤ ps.x j := hx_nn j hj
    have hB : 0 < (2 : ℝ) ^ ps.k * ps.B₀ := by positivity
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hdiff : 0 ≤ ps.x j * (1 + ((2 : ℝ) ^ ps.k * ps.B₀ / n) * (M i j / d j)) - ps.x j := by
      have hr : 0 ≤ ((2 : ℝ) ^ ps.k * ps.B₀ / n) * (M i j / d j) := by positivity
      nlinarith
    have hdiv : 0 ≤ (ps.x j * (1 + ((2 : ℝ) ^ ps.k * ps.B₀ / n) * (M i j / d j)) - ps.x j) / d j :=
      div_nonneg hdiff hdj.le
    simpa [multStep, hj] using hdiv
  · simp [multStep, hj]

private lemma multStep_structInv {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (i : Fin m)
    {ps : PhaseState n} {y_pos : Fin n → ℝ} (hinv : PhaseStructInv d ps y_pos)
    (hcov_lt : rowFracCov M d i ps.x < 1) (ht_lt : ps.t < stepCap n) :
    PhaseStructInv d (multStep M d i ps y_pos).1 (multStep M d i ps y_pos).2 := by
  let res := multStep M d i ps y_pos
  have hB₀ := hinv.B₀_pos
  let B := (2 : ℝ) ^ ps.k * ps.B₀
  have hB_pos : 0 < B := by positivity
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx_nn : ∀ j ∈ Jpos d, 0 ≤ ps.x j := fun j hj =>
    (div_nonneg hB_pos.le hn_pos.le).trans (hinv.x_lb j hj)
  have hmono := multStep_mono hn M d hM i hB₀ hx_nn y_pos
  have hsupp : ∀ j, j ∉ Jpos d → res.2 j = 0 := by
    intro j hj
    dsimp only [res]
    simp [multStep, hj, hinv.y_supp j hj]
  have hx'_ge : ∀ j ∈ Jpos d, ps.x j ≤ res.1.x j := by
    intro j hj
    have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
    have hMij : 0 ≤ M i j := hM i j
    have hr : 0 ≤ (B / n) * (M i j / d j) := by positivity
    have hxj : 0 ≤ ps.x j := hx_nn j hj
    dsimp only [res]
    simp only [multStep, hj, ↓reduceIte]
    change ps.x j ≤ ps.x j * (1 + (B / n) * (M i j / d j))
    nlinarith
  have hsum_diff : ∑ j ∈ Jpos d, res.1.x j - ∑ j ∈ Jpos d, ps.x j =
      (B / n) * rowFracCov M d i ps.x := by
    rw [← Finset.sum_sub_distrib, rowFracCov, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    dsimp only [res]
    simp only [multStep, hj, ↓reduceIte]
    change ps.x j * (1 + (B / n) * (M i j / d j)) - ps.x j = (B / n) * (M i j * (ps.x j / d j))
    ring
  refine
    { B₀_pos := hB₀
      t_le := Nat.succ_le_of_lt ht_lt
      x_lb := fun j hj => (hinv.x_lb j hj).trans (hx'_ge j hj)
      x_sum := by
        have hinc : ∑ j ∈ Jpos d, res.1.x j - ∑ j ∈ Jpos d, ps.x j ≤ B / n := by
          rw [hsum_diff]
          exact mul_le_of_le_one_right (div_nonneg hB_pos.le hn_pos.le) hcov_lt.le
        have hold := hinv.x_sum
        change ∑ j ∈ Jpos d, res.1.x j ≤ B * (1 + ((ps.t + 1 : ℕ) : ℝ) / n)
        have hstep : B * (1 + (ps.t : ℝ) / n) + B / n = B * (1 + ((ps.t + 1 : ℕ) : ℝ) / n) := by
          push_cast
          ring
        linarith
      y_cost := by
        rw [dotProduct_Jpos_eq d hsupp]
        have hcost_old := hinv.y_cost
        rw [dotProduct_Jpos_eq d hinv.y_supp] at hcost_old
        have hcost_diff : ∑ j ∈ Jpos d, d j * res.2 j =
            ∑ j ∈ Jpos d, d j * y_pos j + (∑ j ∈ Jpos d, res.1.x j - ∑ j ∈ Jpos d, ps.x j) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
          dsimp only [res]
          simp only [multStep, hj, ↓reduceIte, mul_add]
          congr 1
          exact mul_div_cancel₀ _ hdj.ne'
        change ∑ j ∈ Jpos d, d j * res.2 j ≤
          (∑ m ∈ Finset.range ps.k, (2 : ℝ) ^ m * ps.B₀) * (1 + (stepCap n : ℝ) / n) +
            ∑ j ∈ Jpos d, res.1.x j
        linarith
      y_lb := fun j hj => by
        have hylb := hinv.y_lb j hj
        let xj' : ℝ := ps.x j * (1 + (B / n) * (M i j / d j))
        have hsplit : xj' / d j = ps.x j / d j + (xj' - ps.x j) / d j := by ring
        simp only [multStep, hj, ↓reduceIte]
        change xj' / d j ≤ y_pos j + (xj' - ps.x j) / d j
        linarith
      y_nn := fun j => (hinv.y_nn j).trans (hmono j)
      y_supp := hsupp }

private lemma coverLoop_spec {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (i : Fin m)
    (hpos : (posCols M d i).Nonempty) :
    ∀ (fuel : ℕ) (ps : PhaseState n) (y_pos : Fin n → ℝ) (K_bound : ℕ),
      PhaseStructInv d ps y_pos →
      (n : ℝ) * rowAlpha M d i hpos / ps.B₀ < (K_bound : ℝ) →
      (K_bound - ps.k) * (stepCap n + 1) + (stepCap n - ps.t) < fuel →
      let res := coverLoop M d i (rowAlpha M d i hpos) fuel ps y_pos
      y_pos ≤ res.2 ∧ PhaseStructInv d res.1 res.2 ∧ 1 ≤ rowFracCov M d i res.1.x := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro ps y_pos K_bound hinv hK hmeas
    let α := rowAlpha M d i hpos
    dsimp only [coverLoop]
    by_cases hcov : 1 ≤ rowFracCov M d i ps.x
    · rw [if_pos hcov]
      exact ⟨le_rfl, hinv, hcov⟩
    · rw [if_neg hcov]
      have hcov_lt : rowFracCov M d i ps.x < 1 := not_le.mp hcov
      have hk_lt : ps.k < K_bound := by
        have hB_lt_nα : (2 : ℝ) ^ ps.k * ps.B₀ < (n : ℝ) * α := by
          by_contra hge
          have hB_ge : (n : ℝ) * α ≤ (2 : ℝ) ^ ps.k * ps.B₀ := not_lt.mp hge
          obtain ⟨j₀, hj₀, hj₀_eq⟩ := exists_col_eq_rowAlpha M d i hpos
          have hj₀_filt := Finset.mem_filter.mp hj₀
          have hj₀_J : j₀ ∈ Jpos d := hj₀_filt.1
          have hMpos : 0 < M i j₀ := hj₀_filt.2
          have hdj₀ : 0 < d j₀ := (Finset.mem_filter.mp hj₀_J).2
          have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
          have hxlb := hinv.x_lb j₀ hj₀_J
          have hterm_ge1 : 1 ≤ M i j₀ * (ps.x j₀ / d j₀) := by
            have h1 : α ≤ (2 : ℝ) ^ ps.k * ps.B₀ / n := by
              rw [le_div_iff₀ hn_pos]
              linarith
            have h2 : d j₀ / M i j₀ ≤ ps.x j₀ := by
              rw [hj₀_eq]
              exact h1.trans hxlb
            have h3 : d j₀ ≤ M i j₀ * ps.x j₀ := by
              have := (div_le_iff₀ hMpos).mp h2
              linarith
            have h4 : 1 ≤ (M i j₀ * ps.x j₀) / d j₀ := (le_div_iff₀ hdj₀).mpr (by linarith)
            simpa [mul_div_assoc] using h4
          have hsum_ge : M i j₀ * (ps.x j₀ / d j₀) ≤ rowFracCov M d i ps.x := by
            have hB_pos : 0 < (2 : ℝ) ^ ps.k * ps.B₀ := by have := hinv.B₀_pos; positivity
            have hf : ∀ j ∈ Jpos d, 0 ≤ M i j * (ps.x j / d j) := by
              intro j hj
              have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
              have hxj : 0 ≤ ps.x j :=
                (div_nonneg hB_pos.le hn_pos.le).trans (hinv.x_lb j hj)
              exact mul_nonneg (hM i j) (div_nonneg hxj hdj.le)
            exact Finset.single_le_sum hf hj₀_J
          linarith
        have hpow_lt : (2 : ℝ) ^ ps.k < (n : ℝ) * α / ps.B₀ :=
          (lt_div_iff₀ hinv.B₀_pos).mpr hB_lt_nα
        have hk_le_pow : (ps.k : ℝ) ≤ (2 : ℝ) ^ ps.k := by
          exact_mod_cast (Nat.lt_two_pow_self (n := ps.k)).le
        have hk_real_lt : (ps.k : ℝ) < (K_bound : ℝ) :=
          (hk_le_pow.trans_lt hpow_lt).trans hK
        exact_mod_cast hk_real_lt
      by_cases habort : (2 : ℝ) ^ ps.k * ps.B₀ < α ∨ stepCap n ≤ ps.t
      · rw [if_pos habort]
        have hinv' := abortStep_structInv hn d hinv
        have hmono1 := abortStep_mono hn d hinv.B₀_pos y_pos
        have hK' : (n : ℝ) * α / (abortStep d ps y_pos).1.B₀ < (K_bound : ℝ) := hK
        have hmeas' : (K_bound - (abortStep d ps y_pos).1.k) * (stepCap n + 1) +
            (stepCap n - (abortStep d ps y_pos).1.t) < fuel := by
          change (K_bound - (ps.k + 1)) * (stepCap n + 1) + (stepCap n - 0) < fuel
          have hsub : K_bound - ps.k = (K_bound - (ps.k + 1)) + 1 := by omega
          rw [hsub, add_one_mul] at hmeas
          omega
        obtain ⟨hm2, hinv2, hcov2⟩ := ih _ _ K_bound hinv' hK' hmeas'
        exact ⟨hmono1.trans hm2, hinv2, hcov2⟩
      · rw [if_neg habort]
        have ht_lt : ps.t < stepCap n := not_le.mp (fun h => habort (Or.inr h))
        have hinv' := multStep_structInv hn M d hM i hinv hcov_lt ht_lt
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        have hB_pos : 0 < (2 : ℝ) ^ ps.k * ps.B₀ := by have := hinv.B₀_pos; positivity
        have hx_nn : ∀ j ∈ Jpos d, 0 ≤ ps.x j := fun j hj =>
          (div_nonneg hB_pos.le hn_pos.le).trans (hinv.x_lb j hj)
        have hmono1 := multStep_mono hn M d hM i hinv.B₀_pos hx_nn y_pos
        have hK' : (n : ℝ) * α / (multStep M d i ps y_pos).1.B₀ < (K_bound : ℝ) := hK
        have hmeas' : (K_bound - (multStep M d i ps y_pos).1.k) * (stepCap n + 1) +
            (stepCap n - (multStep M d i ps y_pos).1.t) < fuel := by
          change (K_bound - ps.k) * (stepCap n + 1) + (stepCap n - (ps.t + 1)) < fuel
          omega
        obtain ⟨hm2, hinv2, hcov2⟩ := ih _ _ K_bound hinv' hK' hmeas'
        exact ⟨hmono1.trans hm2, hinv2, hcov2⟩

private lemma stepRow_spec {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) {st : State n}
    (hst : StateStructInv d st) (i : Fin m) :
    let st' := stepRow M d st i
    st.y ≤ st'.y ∧ StateStructInv d st' ∧
      ((hasZeroCover M d i ∨ (posCols M d i).Nonempty) → 1 ≤ (M *ᵥ st'.y) i) := by
  dsimp only [stepRow]
  by_cases hz : hasZeroCover M d i
  · rw [if_pos hz]
    let yz' : Fin n → ℝ := fun j =>
      if d j = 0 ∧ 0 < M i j then max (st.y_zero j) (1 / M i j) else st.y_zero j
    let st_z : State n := { st with y_zero := yz' }
    change st.y ≤ st_z.y ∧ StateStructInv d st_z ∧
      ((hasZeroCover M d i ∨ (posCols M d i).Nonempty) → 1 ≤ (M *ᵥ st_z.y) i)
    have hyz_le : st.y_zero ≤ yz' := by
      intro j
      dsimp only [yz']
      split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    have hy_le : st.y ≤ st_z.y := add_le_add hyz_le le_rfl
    refine ⟨hy_le, ?_, ?_⟩
    · refine ⟨fun j => (hst.yz_nn j).trans (hyz_le j), ?_, hst.phase_inv⟩
      intro j hdj
      have hnot : ¬ (d j = 0 ∧ 0 < M i j) := fun h => hdj h.1
      dsimp only [st_z, yz']
      simp [hnot, hst.yz_supp j hdj]
    · intro _
      obtain ⟨j₀, hdj₀, hMj₀⟩ := hz
      have hy_pos_nn : ∀ j, 0 ≤ st.y_pos j := by
        intro j
        cases hph : st.phase with
        | none =>
          have hp0 : st.y_pos = 0 := by simpa [hph] using hst.phase_inv
          simp [hp0]
        | some ps =>
          have hpinv : PhaseStructInv d ps st.y_pos := by simpa [hph] using hst.phase_inv
          exact hpinv.y_nn j
      have hy_nn' : ∀ j, 0 ≤ st_z.y j := fun j =>
        add_nonneg ((hst.yz_nn j).trans (hyz_le j)) (hy_pos_nn j)
      have hj₀_lb : 1 / M i j₀ ≤ st_z.y j₀ := by
        have hpos_j₀ := hy_pos_nn j₀
        dsimp only [st_z, State.y, yz']
        simp only [Pi.add_apply, hdj₀, hMj₀, and_self, ↓reduceIte]
        linarith [le_max_right (st.y_zero j₀) (1 / M i j₀)]
      simp only [mulVec, dotProduct]
      calc
        (1 : ℝ) = M i j₀ * (1 / M i j₀) := (mul_one_div_cancel hMj₀.ne').symm
        _ ≤ M i j₀ * st_z.y j₀ := mul_le_mul_of_nonneg_left hj₀_lb (hM i j₀)
        _ ≤ ∑ j : Fin n, M i j * st_z.y j :=
          Finset.single_le_sum (fun j _ => mul_nonneg (hM i j) (hy_nn' j)) (Finset.mem_univ j₀)
  · rw [if_neg hz]
    by_cases hpos : (posCols M d i).Nonempty
    · rw [dif_pos hpos]
      let α := rowAlpha M d i hpos
      have hα_pos : 0 < α := rowAlpha_pos M d i hpos
      let init : PhaseState n × (Fin n → ℝ) := match st.phase with
        | some ps => (ps, st.y_pos)
        | none => initPhase d α
      have hinit : st.y_pos ≤ init.2 ∧ PhaseStructInv d init.1 init.2 := by
        dsimp only [init]
        cases hph : st.phase with
        | none =>
          have hp0 : st.y_pos = 0 := by simpa [hph] using hst.phase_inv
          have hinv0 := initPhase_structInv hn d hα_pos
          exact ⟨by rw [hp0]; exact hinv0.y_nn, hinv0⟩
        | some ps =>
          have hpinv : PhaseStructInv d ps st.y_pos := by simpa [hph] using hst.phase_inv
          exact ⟨le_rfl, hpinv⟩
      let K_bound := Nat.ceil ((n : ℝ) * α / init.1.B₀) + 1
      let fuel := (K_bound + 1) * (stepCap n + 1)
      have hK_lt : (n : ℝ) * α / init.1.B₀ < (K_bound : ℝ) := by
        have hle : (n : ℝ) * α / init.1.B₀ ≤ Nat.ceil ((n : ℝ) * α / init.1.B₀) :=
          Nat.le_ceil _
        dsimp [K_bound]
        push_cast
        linarith
      have hmeas_lt : (K_bound - init.1.k) * (stepCap n + 1) + (stepCap n - init.1.t) < fuel := by
        dsimp [fuel]
        have h1 : K_bound - init.1.k ≤ K_bound := Nat.sub_le _ _
        have h2 : stepCap n - init.1.t ≤ stepCap n := Nat.sub_le _ _
        nlinarith
      obtain ⟨hloop_mono, hloop_inv, hloop_cov⟩ :=
        coverLoop_spec hn M d hM i hpos fuel init.1 init.2 K_bound hinit.2 hK_lt hmeas_lt
      let res := coverLoop M d i α fuel init.1 init.2
      refine ⟨add_le_add le_rfl (hinit.1.trans hloop_mono), ⟨hst.yz_nn, hst.yz_supp, hloop_inv⟩, ?_⟩
      intro _
      simp only [mulVec, dotProduct]
      calc
        (1 : ℝ) ≤ rowFracCov M d i res.1.x := hloop_cov
        _ ≤ ∑ j ∈ Jpos d, M i j * (st.y_zero j + res.2 j) := by
          unfold rowFracCov
          refine Finset.sum_le_sum fun j hj => ?_
          have hlb : res.1.x j / d j ≤ res.2 j := hloop_inv.y_lb j hj
          have hyz0 : 0 ≤ st.y_zero j := hst.yz_nn j
          exact mul_le_mul_of_nonneg_left (by linarith) (hM i j)
        _ ≤ ∑ j : Fin n, M i j * (st.y_zero j + res.2 j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ =>
            mul_nonneg (hM i j) (add_nonneg (hst.yz_nn j) (hloop_inv.y_nn j))
    · rw [dif_neg hpos]
      exact ⟨le_rfl, hst, fun h => False.elim (h.elim hz hpos)⟩

private lemma foldl_stepRow_mono_and_inv {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    ∀ (l : List (Fin m)) (st : State n), StateStructInv d st →
      st.y ≤ (l.foldl (stepRow M d) st).y ∧ StateStructInv d (l.foldl (stepRow M d) st) := by
  intro l
  induction l with
  | nil => intro st hst; exact ⟨le_rfl, hst⟩
  | cons i l ih =>
    intro st hst
    obtain ⟨hm1, hst1, _⟩ := stepRow_spec hn M d hM hst i
    obtain ⟨hm2, hst2⟩ := ih (stepRow M d st i) hst1
    exact ⟨hm1.trans hm2, hst2⟩

private lemma foldl_stepRow_covers_mem {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    ∀ (l : List (Fin m)) (st : State n), StateStructInv d st →
      ∀ i ∈ l, (hasZeroCover M d i ∨ (posCols M d i).Nonempty) →
        1 ≤ (M *ᵥ (l.foldl (stepRow M d) st).y) i := by
  intro l
  induction l with
  | nil => intro _ _ i hi; simp at hi
  | cons a l ih =>
    intro st hst i hi hcov_able
    obtain ⟨_, hst1, hcov_a⟩ := stepRow_spec hn M d hM hst a
    rcases List.mem_cons.mp hi with rfl | hil
    · obtain ⟨hm_tail, _⟩ := foldl_stepRow_mono_and_inv hn M d hM l (stepRow M d st i) hst1
      have h1 : 1 ≤ (M *ᵥ (stepRow M d st i).y) i := hcov_a hcov_able
      refine h1.trans ?_
      simp only [mulVec, dotProduct]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hm_tail j) (hM i j)
    · exact ih (stepRow M d st a) hst1 i hil hcov_able

private lemma initState_structInv {n : ℕ} (d : Fin n → ℝ) :
    StateStructInv d (initState n) :=
  { yz_nn := le_rfl
    yz_supp := fun _ _ => rfl
    phase_inv := rfl }

private lemma runBatches_inv_and_mono {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    ∀ s : List (Finset (Fin m)),
      StateStructInv d (runBatches M d s) ∧
        ∀ S : Finset (Fin m), (runBatches M d s).y ≤ (runBatches M d (s ++ [S])).y := by
  intro s
  have hinv : ∀ s' : List (Finset (Fin m)), StateStructInv d (runBatches M d s') := by
    intro s'
    induction s' using List.reverseRecOn with
    | nil => exact initState_structInv d
    | append_singleton p S ih =>
      unfold runBatches at ih ⊢
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact (foldl_stepRow_mono_and_inv hn M d hM (S.sort (· ≤ ·)) _ ih).2
  refine ⟨hinv s, fun S => ?_⟩
  unfold runBatches
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact (foldl_stepRow_mono_and_inv hn M d hM (S.sort (· ≤ ·)) _ (hinv s)).1

/-! ### Offline potential invariant and `72 log n` competitiveness -/

private noncomputable def potential {n : ℕ} (d y_star : Fin n → ℝ)
    (ps : PhaseState n) : ℝ :=
  let B := (2 : ℝ) ^ ps.k * ps.B₀
  ∑ j ∈ Jpos d, (d j * y_star j / B) * Real.log (ps.x j / (B / n))

private structure PhaseOfflineInv {n : ℕ} (d y_star : Fin n → ℝ)
    (ps : PhaseState n) : Prop where
  B_lt : (2 : ℝ) ^ ps.k * ps.B₀ < 2 * (d ⬝ᵥ y_star)
  pot_lb : (ps.t : ℝ) / (2 * n) ≤ potential d y_star ps

private def StateOfflineInv {n : ℕ} (d y_star : Fin n → ℝ) (st : State n) : Prop :=
  match st.phase with
  | none => True
  | some ps => PhaseOfflineInv d y_star ps

private lemma initPhase_offlineInv {n : ℕ} (hn : 0 < n) (d y_star : Fin n → ℝ)
    {α : ℝ} (hα_pos : 0 < α) (hα_le : α ≤ d ⬝ᵥ y_star) :
    PhaseOfflineInv d y_star (initPhase d α).1 := by
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  refine ⟨?_, ?_⟩
  · simp only [initPhase, pow_zero, one_mul]
    linarith
  · unfold potential
    simp only [initPhase, Nat.cast_zero, zero_div, pow_zero, one_mul]
    have hzero : ∑ j ∈ Jpos d,
        (d j * y_star j / α) * Real.log (initX d α j / (α / n)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hdiv1 : (α / n) / (α / n) = 1 := div_self (div_ne_zero hα_pos.ne' hn_ne)
      simp [initX, hj, hdiv1]
    linarith

private lemma abortStep_offlineInv {n : ℕ} (hn : 3 ≤ n) (d y_star : Fin n → ℝ)
    (hd : 0 ≤ d) (hy_nn : 0 ≤ y_star)
    {ps : PhaseState n} {y_pos : Fin n → ℝ}
    (hstruct : PhaseStructInv d ps y_pos) (hoff : PhaseOfflineInv d y_star ps)
    {α : ℝ} (hα_le : α ≤ d ⬝ᵥ y_star)
    (habort : (2 : ℝ) ^ ps.k * ps.B₀ < α ∨ stepCap n ≤ ps.t) :
    PhaseOfflineInv d y_star (abortStep d ps y_pos).1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  let B := (2 : ℝ) ^ ps.k * ps.B₀
  have hB_pos : 0 < B := by have := hstruct.B₀_pos; positivity
  have hB_lt_opt : B < d ⬝ᵥ y_star := by
    rcases habort with hlt_α | hcap
    · exact hlt_α.trans_le hα_le
    · by_contra hge
      have hopt_le_B : d ⬝ᵥ y_star ≤ B := not_lt.mp hge
      have hpot_ub : potential d y_star ps ≤ Real.log ((n : ℝ) + stepCap n) := by
        unfold potential
        change ∑ j ∈ Jpos d, (d j * y_star j / B) * Real.log (ps.x j / (B / n)) ≤
          Real.log ((n : ℝ) + stepCap n)
        have hlog_le : ∀ j ∈ Jpos d, Real.log (ps.x j / (B / n)) ≤
            Real.log ((n : ℝ) + stepCap n) := by
          intro j hj
          have hxj_pos : 0 < ps.x j / (B / n) := by
            have := hstruct.x_lb j hj
            have h1 : 1 ≤ ps.x j / (B / n) := (le_div_iff₀ (div_pos hB_pos hn_pos)).mpr (by linarith)
            linarith
          refine Real.log_le_log hxj_pos ?_
          have hxj_ub : ps.x j ≤ ∑ j' ∈ Jpos d, ps.x j' := by
            refine Finset.single_le_sum (fun j' hj' => ?_) hj
            exact (div_nonneg hB_pos.le hn_pos.le).trans (hstruct.x_lb j' hj')
          have ht_le : (ps.t : ℝ) ≤ stepCap n := Nat.cast_le.mpr hstruct.t_le
          have hxsum_ub : ∑ j' ∈ Jpos d, ps.x j' ≤ B * (1 + (stepCap n : ℝ) / n) := by
            refine hstruct.x_sum.trans (mul_le_mul_of_nonneg_left ?_ hB_pos.le)
            linarith [div_le_div_of_nonneg_right ht_le hn_pos.le]
          have h1 : ps.x j ≤ (B / n) * ((n : ℝ) + stepCap n) := by
            have heq : B * (1 + (stepCap n : ℝ) / n) = (B / n) * ((n : ℝ) + stepCap n) := by
              field_simp [hn_pos.ne']
            linarith
          exact (div_le_iff₀ (div_pos hB_pos hn_pos)).mpr (by linarith)
        have hlog_nn : 0 ≤ Real.log ((n : ℝ) + stepCap n) := by
          refine Real.log_nonneg ?_
          have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
          have hsc : (0 : ℝ) ≤ stepCap n := Nat.cast_nonneg _
          linarith
        have hsum_w : ∑ j ∈ Jpos d, (d j * y_star j / B) ≤ 1 := by
          rw [← Finset.sum_div]
          have hsub : ∑ j ∈ Jpos d, d j * y_star j ≤ d ⬝ᵥ y_star :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => mul_nonneg (hd j) (hy_nn j))
          exact (div_le_one hB_pos).mpr (hsub.trans hopt_le_B)
        calc
          ∑ j ∈ Jpos d, (d j * y_star j / B) * Real.log (ps.x j / (B / n))
            ≤ ∑ j ∈ Jpos d, (d j * y_star j / B) * Real.log ((n : ℝ) + stepCap n) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hw : 0 ≤ d j * y_star j / B := div_nonneg (mul_nonneg (hd j) (hy_nn j)) hB_pos.le
              exact mul_le_mul_of_nonneg_left (hlog_le j hj) hw
          _ = (∑ j ∈ Jpos d, (d j * y_star j / B)) * Real.log ((n : ℝ) + stepCap n) :=
              (Finset.sum_mul _ _ _).symm
          _ ≤ 1 * Real.log ((n : ℝ) + stepCap n) :=
              mul_le_mul_of_nonneg_right hsum_w hlog_nn
          _ = Real.log ((n : ℝ) + stepCap n) := one_mul _
      have ht_cap : (stepCap n : ℝ) / (2 * n) ≤ (ps.t : ℝ) / (2 * n) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hcap) (by positivity)
      have hchain : (stepCap n : ℝ) / (2 * n) ≤ Real.log ((n : ℝ) + stepCap n) :=
        (ht_cap.trans hoff.pot_lb).trans hpot_ub
      have hle_mul : (stepCap n : ℝ) ≤ 2 * (n : ℝ) * Real.log ((n : ℝ) + stepCap n) := by
        have h2n : (0 : ℝ) < 2 * n := by positivity
        have := (div_le_iff₀ h2n).mp hchain
        linarith
      linarith [two_mul_n_mul_log_lt_stepCap hn]
  refine ⟨?_, ?_⟩
  · change (2 : ℝ) ^ (ps.k + 1) * ps.B₀ < 2 * (d ⬝ᵥ y_star)
    have hpow : (2 : ℝ) ^ (ps.k + 1) * ps.B₀ = 2 * B := by
      dsimp [B]
      ring
    linarith
  · unfold potential
    simp only [abortStep, Nat.cast_zero, zero_div]
    have hzero : ∑ j ∈ Jpos d,
        (d j * y_star j / ((2 : ℝ) ^ (ps.k + 1) * ps.B₀)) *
          Real.log (initX d ((2 : ℝ) ^ (ps.k + 1) * ps.B₀) j /
            (((2 : ℝ) ^ (ps.k + 1) * ps.B₀) / n)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hB'_ne : ((2 : ℝ) ^ (ps.k + 1) * ps.B₀) / n ≠ 0 :=
        div_ne_zero (by have := hstruct.B₀_pos; positivity) hn_pos.ne'
      simp [initX, hj, div_self hB'_ne]
    linarith

private lemma multStep_offlineInv {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d y_star : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d) (hy_nn : 0 ≤ y_star)
    {i : Fin m} (hnoZero : ¬ hasZeroCover M d i) (hy_cov : 1 ≤ (M *ᵥ y_star) i)
    {ps : PhaseState n} {y_pos : Fin n → ℝ}
    (hstruct : PhaseStructInv d ps y_pos) (hoff : PhaseOfflineInv d y_star ps)
    (hcov_lt : rowFracCov M d i ps.x < 1) :
    PhaseOfflineInv d y_star (multStep M d i ps y_pos).1 := by
  let B := (2 : ℝ) ^ ps.k * ps.B₀
  have hB_pos : 0 < B := by have := hstruct.B₀_pos; positivity
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨hoff.B_lt, ?_⟩
  unfold potential
  change ((ps.t + 1 : ℕ) : ℝ) / (2 * n) ≤
    ∑ j ∈ Jpos d, (d j * y_star j / B) *
      Real.log ((multStep M d i ps y_pos).1.x j / (B / n))
  have hpot_diff : ∑ j ∈ Jpos d, (d j * y_star j / B) *
      Real.log ((multStep M d i ps y_pos).1.x j / (B / n)) - potential d y_star ps ≥
      1 / (2 * (n : ℝ)) := by
    unfold potential
    change ∑ j ∈ Jpos d, (d j * y_star j / B) *
        Real.log ((multStep M d i ps y_pos).1.x j / (B / n)) -
      ∑ j ∈ Jpos d, (d j * y_star j / B) * Real.log (ps.x j / (B / n)) ≥ 1 / (2 * (n : ℝ))
    rw [← Finset.sum_sub_distrib]
    have hsum_cov : 1 ≤ ∑ j ∈ Jpos d, M i j * y_star j := by
      rwa [← mulVec_eq_sum_Jpos M d hM hd hnoZero y_star]
    have hterm : ∀ j ∈ Jpos d,
        (1 / (2 * (n : ℝ))) * (M i j * y_star j) ≤
          (d j * y_star j / B) * Real.log ((multStep M d i ps y_pos).1.x j / (B / n)) -
            (d j * y_star j / B) * Real.log (ps.x j / (B / n)) := by
      intro j hj
      have hdj : 0 < d j := (Finset.mem_filter.mp hj).2
      have hMij : 0 ≤ M i j := hM i j
      let r := (B / n) * (M i j / d j)
      have hr0 : 0 ≤ r := by positivity
      have hr1 : r ≤ 1 := by
        have hxlb := hstruct.x_lb j hj
        have hr_le : r ≤ M i j * (ps.x j / d j) := by
          have hmul := mul_le_mul_of_nonneg_right hxlb (div_nonneg hMij hdj.le)
          dsimp [r]
          linarith [show ps.x j * (M i j / d j) = M i j * (ps.x j / d j) by ring]
        have hsub_sum : M i j * (ps.x j / d j) ≤ rowFracCov M d i ps.x := by
          have hf : ∀ j' ∈ Jpos d, 0 ≤ M i j' * (ps.x j' / d j') := by
            intro j' hj'
            have hdj' : 0 < d j' := (Finset.mem_filter.mp hj').2
            have hxj' : 0 ≤ ps.x j' :=
              (div_nonneg hB_pos.le hn_pos.le).trans (hstruct.x_lb j' hj')
            exact mul_nonneg (hM i j') (div_nonneg hxj' hdj'.le)
          exact Finset.single_le_sum hf hj
        linarith
      have hq_pos : 0 < ps.x j / (B / n) := by
        have h1 : 1 ≤ ps.x j / (B / n) :=
          (le_div_iff₀ (div_pos hB_pos hn_pos)).mpr (by linarith [hstruct.x_lb j hj])
        linarith
      have h1r_pos : 0 < 1 + r := by linarith
      have hx'_div : (multStep M d i ps y_pos).1.x j / (B / n) =
          (ps.x j / (B / n)) * (1 + r) := by
        simp only [multStep, hj, ↓reduceIte]
        change (ps.x j * (1 + r)) / (B / n) = (ps.x j / (B / n)) * (1 + r)
        ring
      rw [hx'_div, Real.log_mul hq_pos.ne' h1r_pos.ne']
      have hsub_eq : (d j * y_star j / B) * (Real.log (ps.x j / (B / n)) + Real.log (1 + r)) -
          (d j * y_star j / B) * Real.log (ps.x j / (B / n)) =
          (d j * y_star j / B) * Real.log (1 + r) := by ring
      rw [hsub_eq]
      have hlog_lb := half_le_log_one_add hr0 hr1
      have hw_nn : 0 ≤ d j * y_star j / B :=
        div_nonneg (mul_nonneg hdj.le (hy_nn j)) hB_pos.le
      have hmul_lb := mul_le_mul_of_nonneg_left hlog_lb hw_nn
      have halg : (d j * y_star j / B) * (r / 2) =
          (1 / (2 * (n : ℝ))) * (M i j * y_star j) := by
        dsimp [r]
        field_simp [hB_pos.ne', hdj.ne', hn_pos.ne']
      linarith
    calc
      1 / (2 * (n : ℝ)) ≤ (1 / (2 * (n : ℝ))) * ∑ j ∈ Jpos d, M i j * y_star j := by
        have hpos_2n : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := by positivity
        simpa using mul_le_mul_of_nonneg_left hsum_cov hpos_2n
      _ = ∑ j ∈ Jpos d, (1 / (2 * (n : ℝ))) * (M i j * y_star j) := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum hterm
  have hold := hoff.pot_lb
  have hstep : (ps.t : ℝ) / (2 * n) + 1 / (2 * (n : ℝ)) = ((ps.t + 1 : ℕ) : ℝ) / (2 * n) := by
    push_cast
    ring
  linarith

private lemma coverLoop_offlineInv {m n : ℕ} (hn : 3 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d y_star : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d) (hy_nn : 0 ≤ y_star)
    {i : Fin m} (hnoZero : ¬ hasZeroCover M d i) (hpos : (posCols M d i).Nonempty)
    (hy_cov : 1 ≤ (M *ᵥ y_star) i) :
    ∀ (fuel : ℕ) (ps : PhaseState n) (y_pos : Fin n → ℝ),
      PhaseStructInv d ps y_pos →
      PhaseOfflineInv d y_star ps →
      PhaseOfflineInv d y_star
        (coverLoop M d i (rowAlpha M d i hpos) fuel ps y_pos).1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  have hα_le : rowAlpha M d i hpos ≤ d ⬝ᵥ y_star :=
    rowAlpha_le_dotProduct M d hM hd hnoZero hpos hy_nn hy_cov
  intro fuel
  induction fuel with
  | zero => intro ps _ _ hoff; exact hoff
  | succ fuel ih =>
    intro ps y_pos hstruct hoff
    dsimp only [coverLoop]
    by_cases hcov : 1 ≤ rowFracCov M d i ps.x
    · rw [if_pos hcov]
      exact hoff
    · rw [if_neg hcov]
      have hcov_lt : rowFracCov M d i ps.x < 1 := not_le.mp hcov
      by_cases habort : (2 : ℝ) ^ ps.k * ps.B₀ < rowAlpha M d i hpos ∨ stepCap n ≤ ps.t
      · rw [if_pos habort]
        exact ih _ _ (abortStep_structInv hn0 d hstruct)
          (abortStep_offlineInv hn d y_star hd hy_nn hstruct hoff hα_le habort)
      · rw [if_neg habort]
        have ht_lt : ps.t < stepCap n := not_le.mp (fun h => habort (Or.inr h))
        exact ih _ _ (multStep_structInv hn0 M d hM i hstruct hcov_lt ht_lt)
          (multStep_offlineInv hn0 M d y_star hM hd hy_nn hnoZero hy_cov hstruct hoff hcov_lt)

private lemma stepRow_offlineInv {m n : ℕ} (hn : 3 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d y_star : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d) (hy_nn : 0 ≤ y_star)
    {st : State n} (hst : StateStructInv d st) (hoff : StateOfflineInv d y_star st)
    {i : Fin m} (hy_cov : 1 ≤ (M *ᵥ y_star) i) :
    StateOfflineInv d y_star (stepRow M d st i) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  unfold stepRow
  by_cases hz : hasZeroCover M d i
  · rw [if_pos hz]
    exact hoff
  · rw [if_neg hz]
    by_cases hpos : (posCols M d i).Nonempty
    · rw [dif_pos hpos]
      dsimp only [StateOfflineInv]
      let α := rowAlpha M d i hpos
      have hα_pos : 0 < α := rowAlpha_pos M d i hpos
      have hα_le : α ≤ d ⬝ᵥ y_star :=
        rowAlpha_le_dotProduct M d hM hd hz hpos hy_nn hy_cov
      let init : PhaseState n × (Fin n → ℝ) := match st.phase with
        | some ps => (ps, st.y_pos)
        | none => initPhase d α
      have hinit_struct : PhaseStructInv d init.1 init.2 := by
        dsimp only [init]
        cases hph : st.phase with
        | none => exact initPhase_structInv hn0 d hα_pos
        | some ps => simpa [hph] using hst.phase_inv
      have hinit_off : PhaseOfflineInv d y_star init.1 := by
        dsimp only [init]
        cases hph : st.phase with
        | none => exact initPhase_offlineInv hn0 d y_star hα_pos hα_le
        | some ps => simpa [hph, StateOfflineInv] using hoff
      exact coverLoop_offlineInv hn M d y_star hM hd hy_nn hz hpos hy_cov _ init.1 init.2
        hinit_struct hinit_off
    · rw [dif_neg hpos]
      exact hoff

private lemma mem_reqUnion_of_mem {m : ℕ} {s : List (Finset (Fin m))}
    {S : Finset (Fin m)} (hS : S ∈ s) {i : Fin m} (hi : i ∈ S) :
    i ∈ reqUnion s := by
  induction s with
  | nil => simp at hS
  | cons T tl ih =>
    simp only [reqUnion, List.foldr_cons, Finset.mem_union]
    rcases List.mem_cons.mp hS with rfl | htl
    · exact Or.inl hi
    · exact Or.inr (ih htl)

private lemma runBatches_offlineInv {m n : ℕ} (hn : 3 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d y_star : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d) (hy_nn : 0 ≤ y_star)
    (s : List (Finset (Fin m)))
    (hy_cov : BudgetedAffine.Budget.indic (reqUnion s) ≤ M *ᵥ y_star) :
    StateOfflineInv d y_star (runBatches M d s) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  have hrow_cov : ∀ S ∈ s, ∀ i ∈ S, 1 ≤ (M *ᵥ y_star) i := by
    intro S hS i hi
    have hmem : i ∈ reqUnion s := mem_reqUnion_of_mem hS hi
    have hle := hy_cov i
    simpa [BudgetedAffine.Budget.indic, hmem] using hle
  suffices hgen : ∀ s' : List (Finset (Fin m)),
      (∀ S ∈ s', ∀ i ∈ S, 1 ≤ (M *ᵥ y_star) i) →
      StateOfflineInv d y_star (runBatches M d s') from hgen s hrow_cov
  intro s' hs'
  induction s' using List.reverseRecOn with
  | nil => trivial
  | append_singleton p S ih =>
    have hp : ∀ T ∈ p, ∀ i ∈ T, 1 ≤ (M *ᵥ y_star) i :=
      fun T hT => hs' T (List.mem_append_left _ hT)
    have hS : ∀ i ∈ S, 1 ≤ (M *ᵥ y_star) i :=
      hs' S (List.mem_append_right _ (List.mem_singleton_self S))
    have hoff_p := ih hp
    have hst_p := (runBatches_inv_and_mono hn0 M d hM p).1
    unfold runBatches
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold stepBatch
    have hlist : ∀ (l : List (Fin m)) (st : State n),
        StateStructInv d st → StateOfflineInv d y_star st →
        (∀ i ∈ l, 1 ≤ (M *ᵥ y_star) i) →
        StateOfflineInv d y_star (l.foldl (stepRow M d) st) := by
      intro l
      induction l with
      | nil => intro _ _ hoff _; exact hoff
      | cons a l ihl =>
        intro st hst hoff hl
        have ha : 1 ≤ (M *ᵥ y_star) a := hl a List.mem_cons_self
        have hst1 := (stepRow_spec hn0 M d hM hst a).2.1
        have hoff1 := stepRow_offlineInv hn M d y_star hM hd hy_nn hst hoff ha
        exact ihl _ hst1 hoff1 (fun i hi => hl i (List.mem_cons_of_mem a hi))
    exact hlist (S.sort (· ≤ ·)) (runBatches M d p) hst_p hoff_p
      (fun i hi => hS i ((Finset.mem_sort (· ≤ ·)).mp hi))

private lemma runBatches_cost_le {m n : ℕ} (hn : 3 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ)
    (d y_star : Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d) (hy_nn : 0 ≤ y_star)
    (s : List (Finset (Fin m)))
    (hy_cov : BudgetedAffine.Budget.indic (reqUnion s) ≤ M *ᵥ y_star) :
    d ⬝ᵥ (runBatches M d s).y ≤ (72 * Real.log n) * (d ⬝ᵥ y_star) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  let st := runBatches M d s
  have hst : StateStructInv d st := (runBatches_inv_and_mono hn0 M d hM s).1
  have hoff : StateOfflineInv d y_star st := runBatches_offlineInv hn M d y_star hM hd hy_nn s hy_cov
  have hyz_cost : d ⬝ᵥ st.y_zero = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hdj : d j = 0
    · simp [hdj]
    · simp [hst.yz_supp j hdj]
  have hy_cost_eq : d ⬝ᵥ st.y = d ⬝ᵥ st.y_pos := by
    simp [State.y, dotProduct_add, hyz_cost]
  rw [hy_cost_eq]
  have hd_ystar_nn : 0 ≤ d ⬝ᵥ y_star :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hd j) (hy_nn j)
  cases hph : st.phase with
  | none =>
    have hp0 : st.y_pos = 0 := by simpa [hph] using hst.phase_inv
    rw [hp0, dotProduct_zero]
    positivity
  | some ps =>
    have hpinv : PhaseStructInv d ps st.y_pos := by simpa [hph] using hst.phase_inv
    have hpoff : PhaseOfflineInv d y_star ps := by simpa [StateOfflineInv, hph] using hoff
    have hB₀ := hpinv.B₀_pos
    have hx_cap : ∑ j ∈ Jpos d, ps.x j ≤
        ((2 : ℝ) ^ ps.k * ps.B₀) * (1 + (stepCap n : ℝ) / n) := by
      refine hpinv.x_sum.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have ht : (ps.t : ℝ) ≤ stepCap n := Nat.cast_le.mpr hpinv.t_le
      linarith [div_le_div_of_nonneg_right ht hn_pos.le]
    have htotal_phase : d ⬝ᵥ st.y_pos ≤
        (∑ m ∈ Finset.range (ps.k + 1), (2 : ℝ) ^ m * ps.B₀) * (1 + (stepCap n : ℝ) / n) := by
      have h1 := hpinv.y_cost
      have h2 : (∑ m ∈ Finset.range (ps.k + 1), (2 : ℝ) ^ m * ps.B₀) *
          (1 + (stepCap n : ℝ) / n) =
          (∑ m ∈ Finset.range ps.k, (2 : ℝ) ^ m * ps.B₀) * (1 + (stepCap n : ℝ) / n) +
            ((2 : ℝ) ^ ps.k * ps.B₀) * (1 + (stepCap n : ℝ) / n) := by
        rw [Finset.sum_range_succ, add_mul]
      linarith
    have hgeom : ∑ m ∈ Finset.range (ps.k + 1), (2 : ℝ) ^ m * ps.B₀ ≤
        4 * (d ⬝ᵥ y_star) := by
      rw [← Finset.sum_mul]
      have h1 := mul_le_mul_of_nonneg_right (sum_pow_two_le ps.k) hB₀.le
      have h2 := hpoff.B_lt
      linarith
    have hcap_lt : 1 + (stepCap n : ℝ) / n ≤ 18 * Real.log n :=
      (one_add_stepCap_div_lt hn).le
    have hsum_nn : 0 ≤ ∑ m ∈ Finset.range (ps.k + 1), (2 : ℝ) ^ m * ps.B₀ :=
      Finset.sum_nonneg fun m _ => by positivity
    calc
      d ⬝ᵥ st.y_pos
        ≤ (∑ m ∈ Finset.range (ps.k + 1), (2 : ℝ) ^ m * ps.B₀) *
            (1 + (stepCap n : ℝ) / n) := htotal_phase
      _ ≤ (4 * (d ⬝ᵥ y_star)) * (18 * Real.log n) :=
          mul_le_mul hgeom hcap_lt (by positivity) (by positivity)
      _ = (72 * Real.log n) * (d ⬝ᵥ y_star) := by ring

private noncomputable def buildOnlineCover {m n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hd : 0 ≤ d) :
    OnlineCover M d (72 * Real.log n) where
  sol s := (runBatches M d s).y
  sol_nil := by simp [runBatches, initState, State.y]
  nonneg s := by
    have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
    have hst := (runBatches_inv_and_mono hn0 M d hM s).1
    intro j
    have hy_pos_nn : 0 ≤ (runBatches M d s).y_pos j := by
      cases hph : (runBatches M d s).phase with
      | none =>
        have hp0 : (runBatches M d s).y_pos = 0 := by simpa [hph] using hst.phase_inv
        simp [hp0]
      | some ps =>
        have hpinv : PhaseStructInv d ps (runBatches M d s).y_pos := by
          simpa [hph] using hst.phase_inv
        exact hpinv.y_nn j
    exact add_nonneg (hst.yz_nn j) hy_pos_nn
  mono s S := by
    have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
    exact (runBatches_inv_and_mono hn0 M d hM s).2 S
  covers s hfeas S hS i hi := by
    have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
    have hex_y : ∃ y_star : Fin n → ℝ,
        0 ≤ y_star ∧ BudgetedAffine.Budget.indic (reqUnion s) ≤ M *ᵥ y_star := by
      by_contra hno
      apply hfeas
      unfold BudgetedAffine.Budget.coverCost
      refine iInf_eq_top.mpr fun y => iInf_eq_top.mpr fun hy => ?_
      exact False.elim (hno ⟨y, hy.1, hy.2⟩)
    obtain ⟨y_star, hy_nn, hy_cov⟩ := hex_y
    have hmem_req : i ∈ reqUnion s := mem_reqUnion_of_mem hS hi
    have hi_cov1 : 1 ≤ (M *ᵥ y_star) i := by
      simpa [BudgetedAffine.Budget.indic, hmem_req] using hy_cov i
    have hi_able : hasZeroCover M d i ∨ (posCols M d i).Nonempty := by
      by_cases hz : hasZeroCover M d i
      · exact Or.inl hz
      · refine Or.inr ?_
        rw [mulVec_eq_sum_Jpos M d hM hd hz y_star] at hi_cov1
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hsum0 : ∑ j ∈ Jpos d, M i j * y_star j = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hnot : j ∉ posCols M d i := by simp [hemp]
          have hMle : M i j ≤ 0 :=
            not_lt.mp (fun hMpos => hnot (Finset.mem_filter.mpr ⟨hj, hMpos⟩))
          have hM0 : M i j = 0 := le_antisymm hMle (hM i j)
          simp [hM0]
        linarith
    obtain ⟨p, s₂, rfl⟩ := List.mem_iff_append.mp hS
    have hmono_tail : ∀ tail : List (Finset (Fin m)),
        (runBatches M d (p ++ [S])).y ≤ (runBatches M d ((p ++ [S]) ++ tail)).y := by
      intro tail
      induction tail using List.reverseRecOn with
      | nil => simp
      | append_singleton t1 T iht =>
        rw [← List.append_assoc]
        exact iht.trans ((runBatches_inv_and_mono hn0 M d hM (p ++ [S] ++ t1)).2 T)
    have hcov_pS : 1 ≤ (M *ᵥ (runBatches M d (p ++ [S])).y) i := by
      unfold runBatches
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hst_p := (runBatches_inv_and_mono hn0 M d hM p).1
      exact foldl_stepRow_covers_mem hn0 M d hM (S.sort (· ≤ ·)) _ hst_p i
        ((Finset.mem_sort (· ≤ ·)).mpr hi) hi_able
    have hle_y : (runBatches M d (p ++ [S])).y ≤ (runBatches M d (p ++ S :: s₂)).y := by
      simpa using hmono_tail s₂
    refine hcov_pS.trans ?_
    simp only [mulVec, dotProduct]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle_y j) (hM i j)
  compet s _ hfeas := by
    have hL : 1 < Real.log n := one_lt_log_of_three_le hn
    let ρ : ℝ := 72 * Real.log n
    have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith
    let C : EReal := BudgetedAffine.Budget.coverCost M d (BudgetedAffine.Budget.indic (reqUnion s))
    have hC_nn : (0 : EReal) ≤ C := by
      refine le_iInf fun y => le_iInf fun hy => ?_
      exact EReal.coe_nonneg.mpr (Finset.sum_nonneg fun j _ => mul_nonneg (hd j) (hy.1 j))
    have hC_bot : C ≠ ⊥ := by
      intro hbot
      rw [hbot] at hC_nn
      exact not_le_of_gt (EReal.bot_lt_coe 0) hC_nn
    have hC_eq : ((C.toReal : ℝ) : EReal) = C := EReal.coe_toReal hfeas hC_bot
    have hdiv_le_C : (((d ⬝ᵥ (runBatches M d s).y) / ρ : ℝ) : EReal) ≤ C := by
      refine le_iInf fun y => le_iInf fun hy => ?_
      refine EReal.coe_le_coe_iff.mpr ?_
      rw [div_le_iff₀ hρ_pos, mul_comm]
      exact runBatches_cost_le hn M d y hM hd hy.1 s hy.2
    change ((d ⬝ᵥ (runBatches M d s).y : ℝ) : EReal) ≤ (ρ : EReal) * C
    rw [← hC_eq] at hdiv_le_C ⊢
    have hreal_div : (d ⬝ᵥ (runBatches M d s).y) / ρ ≤ C.toReal :=
      EReal.coe_le_coe_iff.mp hdiv_le_C
    have hreal_mul : d ⬝ᵥ (runBatches M d s).y ≤ ρ * C.toReal := by
      have := (div_le_iff₀ hρ_pos).mp hreal_div
      linarith
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.mpr hreal_mul

end BudgetedAffine.Disjoint

open BudgetedAffine.Disjoint in
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℕ) (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ),
      (∀ i j, 0 ≤ M i j) → 0 ≤ d → Nonempty (OnlineCover M d (K * Real.log n)) :=
  ⟨72, by norm_num, 3, fun n hn m M d hM hd => ⟨buildOnlineCover hn M d hM hd⟩⟩
