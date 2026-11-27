-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_13
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:28:47.448735+00:00
-- url     : https://prove2.me/submissions/e87db169-eb2b-4bd1-adc2-9e9735658f13

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GaussianMatrix_full_rank_ae

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPP413

open GEPPGrowth.Main

/-! ### Pivot folds as lexicographic argmax -/

/-- A fold that replaces the current choice by any admissible strictly better index returns
the maximum of the key over the start and the admissible list entries. -/
lemma foldl_spec {ι K : Type*} [LinearOrder K] (P : ι → Prop) [DecidablePred P] (key : ι → K)
    (L : List ι) (b₀ : ι) :
    ((L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀) = b₀ ∨
        P (L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀)) ∧
      key b₀ ≤ key (L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀) ∧
      ∀ j ∈ L, P j → key j ≤ key (L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀) := by
  induction L generalizing b₀ with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    by_cases hx : P x ∧ key b₀ < key x
    · rw [if_pos hx]
      obtain ⟨h1, h2, h3⟩ := ih x
      refine ⟨h1.elim (fun h => Or.inr (by rw [h]; exact hx.1)) Or.inr, hx.2.le.trans h2, fun _ => h2, h3⟩
    · rw [if_neg hx]
      obtain ⟨h1, h2, h3⟩ := ih b₀
      refine ⟨h1, h2, fun hP => ?_, h3⟩
      exact (not_lt.1 fun h => hx ⟨hP, h⟩).trans h2

/-- Lexicographic key of the GEPP pivot rule in column `k`: larger magnitude, then smaller index. -/
def keyR {n : ℕ} (M : Mat n) (k j : Fin n) : Lex (ℝ × (Fin n)ᵒᵈ) :=
  toLex (|M j k|, OrderDual.toDual j)

def keyV {d : ℕ} (y : Vec d) (j : Fin d) : Lex (ℝ × (Fin d)ᵒᵈ) :=
  toLex (|y j|, OrderDual.toDual j)

lemma keyR_inj {n : ℕ} (M : Mat n) (k : Fin n) {i j : Fin n} (h : keyR M k i = keyR M k j) :
    i = j := by
  simp only [keyR, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h; exact h.2

lemma keyV_inj {d : ℕ} (y : Vec d) {i j : Fin d} (h : keyV y i = keyV y j) : i = j := by
  simp only [keyV, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h; exact h.2

lemma rowPivot_eq_fold {n : ℕ} (M : Mat n) (k : Fin n) :
    rowPivot M k = (List.finRange n).foldl
      (fun b j => if k ≤ j ∧ keyR M k b < keyR M k j then j else b) k := by
  unfold rowPivot
  congr 1
  funext b j
  simp only [keyR, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual]

lemma pivot_eq_fold {d : ℕ} (y : Vec (d+1)) :
    pivot y = (List.finRange (d+1)).foldl
      (fun b j => if True ∧ keyV y b < keyV y j then j else b) 0 := by
  unfold pivot
  congr 1
  funext b j
  simp only [keyV, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual, true_and]

lemma rowPivot_spec {n : ℕ} (M : Mat n) (k : Fin n) :
    k ≤ rowPivot M k ∧ ∀ j, k ≤ j → keyR M k j ≤ keyR M k (rowPivot M k) := by
  rw [rowPivot_eq_fold]
  obtain ⟨h1, -, h3⟩ := foldl_spec (fun j => k ≤ j) (keyR M k) (List.finRange n) k
  exact ⟨h1.elim (fun h => by rw [h]) id, fun j hj => h3 j (List.mem_finRange j) hj⟩

lemma rowPivot_eq_iff {n : ℕ} (M : Mat n) (k i : Fin n) :
    rowPivot M k = i ↔ k ≤ i ∧ ∀ j, k ≤ j → keyR M k j ≤ keyR M k i := by
  obtain ⟨h1, h2⟩ := rowPivot_spec M k
  refine ⟨fun h => h ▸ ⟨h1, h2⟩, fun ⟨hi, hmax⟩ => keyR_inj M k ?_⟩
  exact le_antisymm (hmax _ h1) (h2 _ hi)

lemma pivot_spec {d : ℕ} (y : Vec (d+1)) : ∀ j, keyV y j ≤ keyV y (pivot y) := by
  rw [pivot_eq_fold]
  obtain ⟨-, -, h3⟩ := foldl_spec (fun _ => True) (keyV y) (List.finRange (d+1)) 0
  exact fun j => h3 j (List.mem_finRange j) trivial

lemma rowPivot_max {n : ℕ} (M : Mat n) (k j : Fin n) (hj : k ≤ j) :
    |M j k| ≤ |M (rowPivot M k) k| := by
  have := (rowPivot_spec M k).2 j hj
  simp only [keyR, Prod.Lex.toLex_le_toLex] at this
  rcases this with h | h
  · exact h.le
  · exact h.1.le

/-- The GEPP pivot in column `t` is the shifted `pivot` of the residual column. -/
lemma rowPivot_shift {n t d : ℕ} (hd : n - t = d + 1) (M : Mat n) :
    rowPivot M ⟨t, by omega⟩ =
      ⟨(pivot (fun j : Fin (d+1) => M ⟨j.val + t, by omega⟩ ⟨t, by omega⟩)).val + t, by omega⟩ := by
  set y : Vec (d+1) := fun j => M ⟨j.val + t, by omega⟩ ⟨t, by omega⟩
  rw [rowPivot_eq_iff]
  refine ⟨by simp [Fin.le_def], fun j hj => ?_⟩
  have hj' : t ≤ j.val := hj
  have := pivot_spec y ⟨j.val - t, by omega⟩
  simp only [keyV, keyR, Prod.Lex.toLex_le_toLex, OrderDual.toDual_lt_toDual,
    OrderDual.toDual_le_toDual, y] at this ⊢
  have e : (⟨j.val - t + t, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [e] at this
  rcases this with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, ?_⟩
    simp only [Fin.le_def] at h2 ⊢
    omega

/-- Measurability of the pivot row as a function of the matrix. -/
lemma measurable_rowPivot {n : ℕ} (k : Fin n) :
    Measurable (fun M : Fin n → Fin n → ℝ => rowPivot M k) := by
  refine measurable_to_countable' fun i => ?_
  have : (fun M : Fin n → Fin n → ℝ => rowPivot M k) ⁻¹' {i} =
      {_M | k ≤ i} ∩ ⋂ j : Fin n, {M | k ≤ j → keyR M k j ≤ keyR M k i} := by
    ext M
    refine (rowPivot_eq_iff (M : Mat n) k i).trans ?_
    exact ⟨fun h => ⟨h.1, Set.mem_iInter.2 h.2⟩, fun h => ⟨h.1, Set.mem_iInter.1 h.2⟩⟩
  rw [this]
  refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun j => ?_)
  by_cases hj : k ≤ j
  · simp only [hj, true_implies, keyR, Prod.Lex.toLex_le_toLex, OrderDual.toDual_lt_toDual,
      OrderDual.toDual_le_toDual]
    have h1 : Measurable (fun M : Fin n → Fin n → ℝ => |M j k|) := by fun_prop
    have h2 : Measurable (fun M : Fin n → Fin n → ℝ => |M i k|) := by fun_prop
    exact (measurableSet_lt h1 h2).union ((measurableSet_eq_fun h1 h2).inter (MeasurableSet.const _))
  · simp [hj]
    exact MeasurableSet.univ

/-! ### The accumulated row-operation matrix -/

/-- Left factor of one GEPP step at column `k` with pivot row `i`: swap rows `k, i`, then
subtract multiples of the pivot row. On columns `≥ k`, `stepAt` is left multiplication by it. -/
def stepMat {n : ℕ} (M : Mat n) (k i : Fin n) : Mat n :=
  fun a c => (if Equiv.swap k i a = c then 1 else 0) -
    (if k < a then M (Equiv.swap k i a) k / M (Equiv.swap k i k) k else 0) *
      (if Equiv.swap k i k = c then 1 else 0)

/-- Product of the first `s` step matrices: rows of `(run A s).matrix` in columns `≥ s` are
rows of `Tm A s * A`. -/
def Tm {n : ℕ} (A : Mat n) : ℕ → Mat n
  | 0 => 1
  | s+1 => if h : s < n then
      stepMat (run A s).matrix ⟨s,h⟩ (rowPivot (run A s).matrix ⟨s,h⟩) * Tm A s else Tm A s

lemma run_succ {n : ℕ} (A : Mat n) (s : ℕ) :
    run A (s+1) = if h : s < n then stepAt (run A s) ⟨s,h⟩ (rowPivot (run A s).matrix ⟨s,h⟩)
      else run A s := rfl

lemma Tm_succ {n : ℕ} (A : Mat n) (s : ℕ) :
    Tm A (s+1) = if h : s < n then
      stepMat (run A s).matrix ⟨s,h⟩ (rowPivot (run A s).matrix ⟨s,h⟩) * Tm A s else Tm A s := rfl

lemma stepMat_mul_apply {n : ℕ} (M X : Mat n) (k i a b : Fin n) :
    (stepMat M k i * X) a b = X (Equiv.swap k i a) b -
      (if k < a then M (Equiv.swap k i a) k / M (Equiv.swap k i k) k else 0) *
        X (Equiv.swap k i k) b := by
  simp [stepMat, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, mul_assoc,
    Finset.sum_ite_eq, Finset.mul_sum]

lemma stepAt_matrix {n : ℕ} (s : RunState n) (k i a b : Fin n) (hb : k ≤ b) :
    (stepAt s k i).matrix a b = (stepMat s.matrix k i * s.matrix) a b := by
  rw [stepMat_mul_apply]
  simp [stepAt, hb]

/-- Columns `≥ s` of the GEPP state are `Tm A s` applied to the input. -/
lemma run_col {n : ℕ} (A : Mat n) : ∀ s (b : Fin n), s ≤ b.val → ∀ a,
    (run A s).matrix a b = (Tm A s * A) a b := by
  intro s
  induction s with
  | zero => intro b _ a; simp [run, Tm]
  | succ s ih =>
    intro b hb a
    rw [run_succ, Tm_succ]
    split_ifs with h
    · rw [stepAt_matrix _ _ _ _ _ (by simp [Fin.le_def]; omega), Matrix.mul_assoc,
        stepMat_mul_apply, stepMat_mul_apply, ih b (by omega), ih b (by omega)]
    · exact absurd b.isLt (by omega)

/-- Below the first `s` rows, the first `s` columns of `Tm A s * A` vanish. -/
lemma TA_zero {n : ℕ} (A : Mat n) : ∀ s (j a : Fin n), j.val < s → s ≤ a.val →
    (Tm A s * A) a j = 0 := by
  intro s
  induction s with
  | zero => intro j a hj; omega
  | succ s ih =>
    intro j a hj ha
    rw [Tm_succ]
    split_ifs with h
    · set M := (run A s).matrix
      set q := rowPivot M ⟨s,h⟩
      have hq : s ≤ q.val := (rowPivot_spec M ⟨s,h⟩).1
      have hsw : ∀ x : Fin n, s ≤ x.val → s ≤ (Equiv.swap (⟨s,h⟩ : Fin n) q x).val := by
        intro x hx
        rw [Equiv.swap_apply_def]
        split_ifs <;> simp_all
      have hka : (⟨s,h⟩ : Fin n) < a := by simp [Fin.lt_def]; omega
      rw [Matrix.mul_assoc, stepMat_mul_apply, if_pos hka]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · rw [ih j _ hj (hsw a (by omega)), ih j _ hj (hsw _ le_rfl)]
        simp
      · have hjs : j = ⟨s,h⟩ := Fin.ext hj
        subst hjs
        rw [← run_col A s _ le_rfl, ← run_col A s _ le_rfl]
        simp only [Equiv.swap_apply_left]
        by_cases h0 : M q ⟨s,h⟩ = 0
        · have hmax := rowPivot_max M ⟨s,h⟩ (Equiv.swap (⟨s,h⟩ : Fin n) q a)
            (by simpa [Fin.le_def] using hsw a (by omega))
          rw [h0, abs_zero] at hmax
          have e1 : M (Equiv.swap (⟨s,h⟩ : Fin n) q a) ⟨s,h⟩ = 0 := abs_nonpos_iff.1 hmax
          simp only [M] at e1 h0
          rw [e1, h0]; simp
        · field_simp; ring
    · exact absurd a.isLt (by omega)

lemma stepAt_matrix_apply {n : ℕ} (s : RunState n) (k i a b : Fin n) :
    (stepAt s k i).matrix a b = s.matrix (Equiv.swap k i a) b -
      (if k < a then s.matrix (Equiv.swap k i a) k / s.matrix (Equiv.swap k i k) k else 0) *
        (if k ≤ b then s.matrix (Equiv.swap k i k) b else 0) := rfl

/-- The columns `≥ s` of `Tm A s` at the current labels form the identity. -/
lemma Tm_labels {n : ℕ} (A : Mat n) : ∀ s, s ≤ n → ∀ (c : Fin n), s ≤ c.val → ∀ a,
    Tm A s a ((run A s).labels c) = if a = c then 1 else 0 := by
  intro s
  induction s with
  | zero =>
    intro _ c _ a
    show (1 : Mat n) a c = _
    by_cases h : a = c
    · subst h; simp
    · simp [h]
  | succ s ih =>
    intro hs c hc a
    have h : s < n := by omega
    rw [Tm_succ, run_succ, dif_pos h, dif_pos h, stepMat_mul_apply]
    set q := rowPivot (run A s).matrix ⟨s,h⟩
    have hq : s ≤ q.val := by
      have := (rowPivot_spec (run A s).matrix ⟨s,h⟩).1; simpa [Fin.le_def] using this
    have hsw : s ≤ (Equiv.swap (⟨s,h⟩ : Fin n) q c).val := by
      rw [Equiv.swap_apply_def]; split_ifs <;> simp_all <;> omega
    have hcs : c ≠ ⟨s,h⟩ := fun e => by rw [e] at hc; simp at hc
    have hne : q ≠ (Equiv.swap (⟨s,h⟩ : Fin n) q) c := by
      rw [Ne, eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]; exact hcs
    show Tm A s _ ((run A s).labels (Equiv.swap (⟨s,h⟩ : Fin n) q c)) - _ * Tm A s _
      ((run A s).labels (Equiv.swap (⟨s,h⟩ : Fin n) q c)) = _
    rw [ih (by omega) _ hsw, ih (by omega) _ hsw]
    simp [(Equiv.swap (⟨s,h⟩ : Fin n) q).injective.eq_iff, hne]

lemma labels_perm {n : ℕ} (A : Mat n) : ∀ s, ∃ σ : Equiv.Perm (Fin n), (run A s).labels = σ := by
  intro s
  induction s with
  | zero => exact ⟨Equiv.refl _, rfl⟩
  | succ s ih =>
    obtain ⟨σ, hσ⟩ := ih
    rw [run_succ]
    split_ifs with h
    · exact ⟨(Equiv.swap ⟨s,h⟩ (rowPivot (run A s).matrix ⟨s,h⟩)).trans σ,
        by funext a; simp [stepAt, hσ]⟩
    · exact ⟨σ, hσ⟩

lemma rowPivot_congr {n : ℕ} {M M' : Mat n} (k : Fin n) (h : ∀ i, M i k = M' i k) :
    rowPivot M k = rowPivot M' k := by
  have hk : keyR M k = keyR M' k := funext fun j => by simp [keyR, h]
  rw [rowPivot_eq_fold, rowPivot_eq_fold, hk]

lemma stepMat_congr {n : ℕ} {M M' : Mat n} (k i : Fin n) (h : ∀ i, M i k = M' i k) :
    stepMat M k i = stepMat M' k i := by
  ext a c; simp only [stepMat, h]

/-- Everything up to time `t` depends only on the first `t` columns of the input. -/
lemma locality {n t : ℕ} (A A' : Mat n) (hA : ∀ i (j : Fin n), j.val < t → A i j = A' i j) :
    ∀ s, s ≤ t → Tm A s = Tm A' s ∧ (run A s).labels = (run A' s).labels ∧
      ∀ i (j : Fin n), j.val < t → (run A s).matrix i j = (run A' s).matrix i j := by
  intro s
  induction s with
  | zero => intro _; exact ⟨rfl, rfl, fun i j hj => hA i j hj⟩
  | succ s ih =>
    intro hs
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [Tm_succ, Tm_succ, run_succ, run_succ]
    split_ifs with h
    · have hcol : ∀ i, (run A s).matrix i ⟨s,h⟩ = (run A' s).matrix i ⟨s,h⟩ :=
        fun i => h3 i _ (by simp; omega)
      rw [rowPivot_congr _ hcol, stepMat_congr _ _ hcol, h1]
      refine ⟨rfl, by funext a; simp [stepAt, h2], fun i j hj => ?_⟩
      rw [stepAt_matrix_apply, stepAt_matrix_apply, h3 _ _ hj, hcol, hcol]
      split_ifs <;> simp [h3 _ _ hj]
    · exact ⟨h1, h2, h3⟩

lemma measurable_step {n : ℕ} (k : Fin n) :
    Measurable (fun M : Fin n → Fin n → ℝ =>
      ((stepAt (⟨M, id⟩ : RunState n) k (rowPivot M k)).matrix : Fin n → Fin n → ℝ)) := by
  have h2 : Measurable (fun q : (Fin n → Fin n → ℝ) × Fin n =>
      ((stepAt (⟨q.1, id⟩ : RunState n) k q.2).matrix : Fin n → Fin n → ℝ)) := by
    refine measurable_from_prod_countable_left (fun i => ?_)
    refine measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun b => ?_))
    change Measurable (fun M : Fin n → Fin n → ℝ => M (Equiv.swap k i a) b -
      (if k < a then M (Equiv.swap k i a) k / M (Equiv.swap k i k) k else 0) *
        (if k ≤ b then M (Equiv.swap k i k) b else 0))
    split_ifs <;> fun_prop
  exact h2.comp (f := fun M => (M, rowPivot M k)) (measurable_id.prodMk (measurable_rowPivot k))

lemma measurable_stepMat {n : ℕ} (k : Fin n) :
    Measurable (fun M : Fin n → Fin n → ℝ => (stepMat M k (rowPivot M k) : Fin n → Fin n → ℝ)) := by
  have h2 : Measurable (fun q : (Fin n → Fin n → ℝ) × Fin n =>
      (stepMat q.1 k q.2 : Fin n → Fin n → ℝ)) := by
    refine measurable_from_prod_countable_left (fun i => ?_)
    refine measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun b => ?_))
    change Measurable (fun M : Fin n → Fin n → ℝ => (if Equiv.swap k i a = b then (1:ℝ) else 0) -
      (if k < a then M (Equiv.swap k i a) k / M (Equiv.swap k i k) k else 0) *
        (if Equiv.swap k i k = b then 1 else 0))
    split_ifs <;> fun_prop
  exact h2.comp (f := fun M => (M, rowPivot M k)) (measurable_id.prodMk (measurable_rowPivot k))

lemma measurable_run {n : ℕ} : ∀ s, Measurable (fun A : Fin n → Fin n → ℝ =>
    ((run A s).matrix : Fin n → Fin n → ℝ)) ∧
    Measurable (fun A : Fin n → Fin n → ℝ => (Tm A s : Fin n → Fin n → ℝ)) := by
  intro s
  induction s with
  | zero => exact ⟨measurable_id, measurable_const⟩
  | succ s ih =>
    by_cases h : s < n
    · have e1' : ∀ A : Mat n, (run A (s+1)).matrix =
          (stepAt (⟨(run A s).matrix, id⟩ : RunState n) ⟨s,h⟩
            (rowPivot (run A s).matrix ⟨s,h⟩)).matrix := by
        intro A; rw [run_succ, dif_pos h]; rfl
      have e2' : ∀ A : Mat n, Tm A (s+1) =
          stepMat (run A s).matrix ⟨s,h⟩ (rowPivot (run A s).matrix ⟨s,h⟩) * Tm A s := by
        intro A; rw [Tm_succ, dif_pos h]
      have e1 : (fun A : Fin n → Fin n → ℝ => ((run A (s+1)).matrix : Fin n → Fin n → ℝ)) =
          (fun M : Fin n → Fin n → ℝ =>
            ((stepAt (⟨M, id⟩ : RunState n) ⟨s,h⟩ (rowPivot M ⟨s,h⟩)).matrix :
              Fin n → Fin n → ℝ)) ∘ (fun A => (run A s).matrix) := funext e1'
      have e2 : (fun A : Fin n → Fin n → ℝ => (Tm A (s+1) : Fin n → Fin n → ℝ)) =
          fun A => ((stepMat (run A s).matrix ⟨s,h⟩ (rowPivot (run A s).matrix ⟨s,h⟩) *
            Tm A s : Mat n) : Fin n → Fin n → ℝ) := funext e2'
      refine ⟨e1 ▸ (measurable_step _).comp ih.1, e2 ▸ ?_⟩
      have hS := (measurable_stepMat (n := n) ⟨s,h⟩).comp ih.1
      refine measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun b => ?_))
      simp only [Matrix.mul_apply]
      refine Finset.measurable_sum _ (fun c _ => ?_)
      exact ((measurable_pi_apply c).comp ((measurable_pi_apply a).comp hS)).mul
        ((measurable_pi_apply b).comp ((measurable_pi_apply c).comp ih.2))
    · have e1 : ∀ A : Mat n, run A (s+1) = run A s := by
        intro A; rw [run_succ, dif_neg h]
      have e2 : ∀ A : Mat n, Tm A (s+1) = Tm A s := by
        intro A; rw [Tm_succ, dif_neg h]
      have f1 : (fun A : Fin n → Fin n → ℝ => ((run A (s+1)).matrix : Fin n → Fin n → ℝ)) =
          fun A => (run A s).matrix := funext fun A => congrArg RunState.matrix (e1 A)
      have f2 : (fun A : Fin n → Fin n → ℝ => (Tm A (s+1) : Fin n → Fin n → ℝ)) =
          fun A => Tm A s := funext fun A => e2 A
      rw [f1, f2]; exact ih

/-! ### Deterministic determinant identity -/

/-- Determinant of a matrix that is block upper triangular for the split `t | n - t`. -/
lemma det_block {n t : ℕ} (ht : t ≤ n) (X : Mat n)
    (h0 : ∀ a c : Fin n, t ≤ a.val → c.val < t → X a c = 0) :
    X.det = (Matrix.of fun i j : Fin t => X ⟨i, by omega⟩ ⟨j, by omega⟩).det *
      (Matrix.of fun i j : Fin (n-t) => X ⟨i + t, by omega⟩ ⟨j + t, by omega⟩).det := by
  let e : Fin t ⊕ Fin (n-t) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have he1 : ∀ i : Fin t, e (Sum.inl i) = ⟨i, by omega⟩ := fun i => Fin.ext (by simp [e])
  have he2 : ∀ i : Fin (n-t), e (Sum.inr i) = ⟨i + t, by omega⟩ :=
    fun i => Fin.ext (by simp [e]; omega)
  rw [← Matrix.det_submatrix_equiv_self e X]
  have : X.submatrix e e = Matrix.fromBlocks
      (Matrix.of fun i j : Fin t => X ⟨i, by omega⟩ ⟨j, by omega⟩)
      (X.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)) 0
      (Matrix.of fun i j : Fin (n-t) => X ⟨i + t, by omega⟩ ⟨j + t, by omega⟩) := by
    ext (i|i) (j|j)
    · simp [he1]
    · simp
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [he2, he1]; exact h0 _ _ (by simp) (by simp)
    · simp [he2]
  rw [this, Matrix.det_fromBlocks_zero₂₁]

lemma det_ne_zero_of_rank {n : ℕ} (A : Mat n) (h : A.rank = n) : A.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have hsurj : Function.Surjective A.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using h
  have hinj := LinearMap.injective_iff_surjective.2 hsurj
  exact hv (hinj (by simpa using hAv))

/-- The paper's covariance `Σ = W Wᵀ`, `W` the last `n - t` rows of `Tm A t`. -/
def Sig {n : ℕ} (A : Mat n) (t : ℕ) : Mat (n-t) :=
  Matrix.of fun i j : Fin (n-t) =>
    ∑ x, Tm A t ⟨i + t, by omega⟩ x * Tm A t ⟨j + t, by omega⟩ x

/-- Gram/pivot-minor identity: `det(FJ)² det(Σ)² = det(FᵀF) det(Σ)`, and `det(FJ) ≠ 0` when
`A` is invertible. -/
lemma det_identity {n t : ℕ} (ht : t ≤ n) (A : Mat n) :
    (pivotMinor ht A).det ^ 2 * (Sig A t).det ^ 2 =
      ((firstColumns ht A).transpose * firstColumns ht A).det * (Sig A t).det ∧
    (A.det ≠ 0 → (pivotMinor ht A).det ≠ 0) := by
  obtain ⟨σ, hσ⟩ := labels_perm A t
  let N : Mat n := Matrix.of fun a c =>
    if a.val < t then (if (run A t).labels a = c then 1 else 0) else Tm A t a c
  let M : Mat n := Matrix.of fun x c => if c.val < t then A x c else Tm A t c x
  -- `det N = ± 1`
  have hinj : Function.Injective (run A t).labels := hσ ▸ σ.injective
  have hN : N.det ^ 2 = 1 := by
    have hL : (N.submatrix id σ).transpose.det = 1 := by
      rw [det_block ht]
      · have h1 : (Matrix.of fun i j : Fin t => (N.submatrix id σ).transpose
            ⟨i, by omega⟩ ⟨j, by omega⟩) = 1 := by
          ext i j
          simp only [N, Matrix.transpose_apply, Matrix.submatrix_apply, id, Matrix.of_apply,
            if_pos j.isLt, ← hσ, Matrix.one_apply, hinj.eq_iff, Fin.ext_iff]
          by_cases h : (i : ℕ) = j
          · simp [h]
          · rw [if_neg, if_neg h]
            intro e
            have := congrArg Fin.val (hinj (Fin.ext e))
            simp at this; omega
        have h2 : (Matrix.of fun i j : Fin (n-t) => (N.submatrix id σ).transpose
            ⟨i + t, by omega⟩ ⟨j + t, by omega⟩) = 1 := by
          ext i j
          simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id, Matrix.of_apply, N]
          rw [if_neg (by simp), ← hσ, Tm_labels A t ht _ (by simp)]
          by_cases h : (i : ℕ) = j <;> simp [Matrix.one_apply, Fin.ext_iff, h, eq_comm]
        rw [h1, h2]; simp
      · intro a c ha hc
        simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id, N, Matrix.of_apply,
          if_pos hc, ← hσ]
        rw [if_neg (fun h => by have := congrArg Fin.val (hinj h); omega)]
    rw [Matrix.det_transpose, Matrix.det_permute'] at hL
    have := congrArg (· ^ 2) hL
    simp only [mul_pow, one_pow] at this
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp_all
  -- the first `t` columns of `T A` vanish below row `t`
  have hTA : ∀ a c : Fin n, t ≤ a.val → c.val < t → ∑ x, Tm A t a x * A x c = 0 := by
    intro a c ha hc
    have := TA_zero A t c a hc ha
    simpa [Matrix.mul_apply] using this
  have hNM : (N * M).det = (pivotMinor ht A).det * (Sig A t).det := by
    rw [det_block ht]
    · congr 2
      · ext i j
        simp [N, M, Matrix.mul_apply, pivotMinor]
      · ext i j
        simp [N, M, Matrix.mul_apply, Sig]
    · intro a c ha hc
      simp only [Matrix.mul_apply, N, M, Matrix.of_apply, if_neg (show ¬ a.val < t by omega),
        if_pos hc]
      exact hTA a c ha hc
  have hMM : (M.transpose * M).det =
      ((firstColumns ht A).transpose * firstColumns ht A).det * (Sig A t).det := by
    rw [det_block ht]
    · congr 2
      · ext i j
        simp [M, Matrix.mul_apply, firstColumns]
      · ext i j
        simp [M, Matrix.mul_apply, Sig]
    · intro a c ha hc
      simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply,
        if_neg (show ¬ a.val < t by omega), if_pos hc]
      exact hTA a c ha hc
  refine ⟨?_, fun hA => ?_⟩
  · rw [← mul_pow, ← hNM, ← hMM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_pow, hN]
    ring
  · have hNA : (N * A).det = (pivotMinor ht A).det *
        (Matrix.of fun i j : Fin (n-t) => (N * A) ⟨i + t, by omega⟩ ⟨j + t, by omega⟩).det := by
      rw [det_block ht]
      · congr 2
        ext i j
        simp [N, Matrix.mul_apply, pivotMinor]
      · intro a c ha hc
        simp only [Matrix.mul_apply, N, Matrix.of_apply, if_neg (show ¬ a.val < t by omega)]
        exact hTA a c ha hc
    intro h0
    rw [h0, zero_mul, Matrix.det_mul] at hNA
    have hN0 : N.det ≠ 0 := fun h => by simp [h] at hN
    exact mul_ne_zero hN0 hA hNA

/-! ### The covariance recursion along the actual run -/

lemma compressionAt_apply {d : ℕ} (y : Vec (d+1)) (p : Fin (d+1)) (a : Fin d) (b : Fin (d+1)) :
    compressionAt y p a b = (if Equiv.swap 0 p a.succ = b then 1 else 0) -
      (if b = p then ratiosAt y p (Equiv.swap 0 p a.succ) else 0) := by
  simp only [compressionAt, deletion, eliminationAt, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, basisVector, mul_sub]
  simp [Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

lemma swap_shift {n t d : ℕ} (hd : n - t = d + 1) (p m : Fin (d+1)) :
    Equiv.swap (⟨t, by omega⟩ : Fin n) ⟨p.val + t, by omega⟩ ⟨m.val + t, by omega⟩ =
      ⟨(Equiv.swap 0 p m).val + t, by omega⟩ := by
  by_cases h1 : m = 0
  · subst h1
    have e : (⟨(0 : Fin (d+1)).val + t, by omega⟩ : Fin n) = ⟨t, by omega⟩ := Fin.ext (by simp)
    rw [e, Equiv.swap_apply_left]
    exact Fin.ext (by simp)
  · by_cases h2 : m = p
    · subst h2
      rw [Equiv.swap_apply_right]
      exact Fin.ext (by simp)
    · have h1' : m.val ≠ 0 := fun e => h1 (Fin.ext e)
      have h2' : m.val ≠ p.val := fun e => h2 (Fin.ext e)
      rw [Equiv.swap_apply_of_ne_of_ne (fun e => h1' (by rw [Fin.mk.injEq] at e; omega))
        (fun e => h2' (by rw [Fin.mk.injEq] at e; omega))]
      exact Fin.ext (by simp [Equiv.swap_apply_of_ne_of_ne h1 h2])

/-- One compression step on the rows of `Tm`: `C W_t = W_{t+1}`. -/
lemma CW_eq {n t d : ℕ} (hd : n - t = d + 1) (A : Mat n) (a : Fin d) (x : Fin n) :
    let y : Vec (d+1) := fun j => (run A t).matrix ⟨j.val + t, by omega⟩ ⟨t, by omega⟩
    (compressionAt y (pivot y) *
      Matrix.of fun (b : Fin (d+1)) (x : Fin n) => Tm A t ⟨b.val + t, by omega⟩ x) a x =
      Tm A (t+1) ⟨a.val + (t+1), by omega⟩ x := by
  intro y
  have ht : t < n := by omega
  rw [Tm_succ, dif_pos ht, stepMat_mul_apply, rowPivot_shift hd]
  set p := pivot y
  have hsa := swap_shift hd p a.succ
  have e1 : (⟨a.val + (t+1), by omega⟩ : Fin n) = ⟨a.succ.val + t, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [e1, hsa, Equiv.swap_apply_left, if_pos (by simp [Fin.lt_def])]
  simp only [Matrix.mul_apply, compressionAt_apply, Matrix.of_apply, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_ite_eq', ratiosAt, y]
  rfl

lemma actualCov_eq {n : ℕ} (A : Mat n) : ∀ t, t ≤ n → ∀ i j : ℕ, actualCov A t i j =
    if h : i < n - t ∧ j < n - t then
      ∑ x, Tm A t ⟨i + t, by omega⟩ x * Tm A t ⟨j + t, by omega⟩ x else 0 := by
  intro t
  induction t with
  | zero =>
    intro _ i j
    show embed (1 : Mat n) i j = _
    simp only [embed]
    by_cases hi : i < n <;> by_cases hj : j < n <;> simp [hi, hj, Tm, Matrix.one_apply]
  | succ t ih =>
    intro ht i j
    obtain ⟨d, hd⟩ : ∃ d, n - t = d + 1 := ⟨n - t - 1, by omega⟩
    have hd' : n - (t+1) = d := by omega
    have e : actualCov A (t+1) = embed (update (block (actualCov A t) (d+1))
        (fun j : Fin (d+1) => actualColumn A t j.val)) := by
      show stateUpdate (n - t) (actualCov A t) (actualColumn A t) = _
      rw [hd]; rfl
    have hy : (fun j : Fin (d+1) => actualColumn A t j.val) =
        fun j => (run A t).matrix ⟨j.val + t, by omega⟩ ⟨t, by omega⟩ := by
      funext j; simp [actualColumn, show j.val + t < n by omega, show t < n by omega]
    have hS : block (actualCov A t) (d+1) =
        (Matrix.of fun (b : Fin (d+1)) (x : Fin n) => Tm A t ⟨b.val + t, by omega⟩ x) *
        (Matrix.of fun (b : Fin (d+1)) (x : Fin n) => Tm A t ⟨b.val + t, by omega⟩ x).transpose := by
      ext b b'
      simp only [block, ih (by omega), Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
      rw [dif_pos (by omega)]
    rw [e, hy]
    by_cases hij : i < d ∧ j < d
    · rw [dif_pos (by omega)]
      simp only [embed, dif_pos hij.1, dif_pos hij.2, update, updateAt, hS]
      rw [← Matrix.mul_assoc, Matrix.mul_assoc _ _ (compressionAt _ _).transpose,
        ← Matrix.transpose_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.transpose_apply, CW_eq hd A ⟨i, hij.1⟩ x, CW_eq hd A ⟨j, hij.2⟩ x]
    · rw [dif_neg (by omega)]
      simp only [embed]
      by_cases hi : i < d
      · rw [dif_pos hi, dif_neg (fun hj => hij ⟨hi, hj⟩)]
      · rw [dif_neg hi]

/-- One elimination step keeps `S ⪰ I` (from the proof of Proposition 4.11). -/
lemma updateAt_sub_one {d : ℕ} (S : Mat (d+1)) (hS : (S - 1).PosSemidef) (y : Vec (d+1))
    (i : Fin (d+1)) : (updateAt S y i - 1).PosSemidef := by
  set C := compressionAt y i
  set w : Vec d := fun a => ratiosAt y i (Equiv.swap 0 i a.succ)
  have hrow : ∀ a c, C a c = (if Equiv.swap 0 i a.succ = c then 1 else 0) -
      (if c = i then w a else 0) := fun a c => compressionAt_apply y i a c
  have hC : C * C.transpose = 1 + Matrix.vecMulVec w w := by
    ext a a'
    have hne : ∀ a : Fin d, Equiv.swap 0 i a.succ ≠ i := by
      intro a h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
      exact Fin.succ_ne_zero a h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hrow]
    simp [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', hne, Matrix.one_apply, Matrix.vecMulVec_apply, Fin.succ_inj]
  have hsplit : updateAt S y i - 1 = C * (S - 1) * C.transpose + Matrix.vecMulVec w w := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hC]
    simp only [updateAt, C]
    abel
  rw [hsplit]
  have h1 := hS.mul_mul_conjTranspose_same C
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have h2 := Matrix.posSemidef_vecMulVec_self_star w
  rw [star_trivial] at h2
  exact h1.add h2

lemma block_embed {d : ℕ} (M : Mat d) : block (embed M) d = M := by
  ext i j; simp [block, embed]

def Good (d : ℕ) : Set CovState := {S | (block S d - 1).PosSemidef}

lemma actualCov_good {n : ℕ} (A : Mat n) : ∀ t, t ≤ n → actualCov A t ∈ Good (n - t) := by
  intro t
  induction t with
  | zero => intro _; simp [Good, actualCov, block_embed, Matrix.PosSemidef.zero]
  | succ t ih =>
    intro ht
    obtain ⟨d, hd⟩ : ∃ d, n - t = d + 1 := ⟨n - t - 1, by omega⟩
    have hd' : n - (t+1) = d := by omega
    have e : actualCov A (t+1) = embed (update (block (actualCov A t) (d+1))
        (fun j : Fin (d+1) => actualColumn A t j.val)) := by
      show stateUpdate (n - t) (actualCov A t) (actualColumn A t) = _
      rw [hd]; rfl
    have := ih (by omega)
    rw [hd] at this
    rw [hd', e]
    simp only [Good, Set.mem_ofPred_eq, block_embed]
    exact updateAt_sub_one _ this _ _

lemma block_actualCov {n t : ℕ} (ht : t ≤ n) (A : Mat n) : block (actualCov A t) (n-t) = Sig A t := by
  ext i j
  simp only [block, Sig, Matrix.of_apply, actualCov_eq A t ht]
  rw [dif_pos ⟨i.isLt, j.isLt⟩]

/-- Second half of Lemma 4.13. -/
lemma det_part {n t : ℕ} (ht : t ≤ n) : ∀ᵐ A ∂(GaussianMatrix.gaussianMatrix n n),
    (block (actualCov A t) (n-t)).det =
      ((firstColumns ht A).transpose * firstColumns ht A).det / (pivotMinor ht A).det ^ 2 := by
  filter_upwards [GaussianMatrix.full_rank_ae n n] with A hA
  have hA' : (Matrix.of A).rank = n := by rw [hA, min_self]
  have hdetA : (A : Mat n).det ≠ 0 := det_ne_zero_of_rank A hA'
  obtain ⟨h1, h2⟩ := det_identity ht A
  have hFJ := h2 hdetA
  have hgood := actualCov_good A t ht
  simp only [Good, Set.mem_ofPred_eq] at hgood
  rw [block_actualCov ht] at hgood ⊢
  have hpos : (Sig A t).det ≠ 0 := by
    have := (Matrix.PosDef.one.add_posSemidef hgood).det_pos
    rw [add_sub_cancel] at this
    exact this.ne'
  rw [eq_div_iff (pow_ne_zero 2 hFJ)]
  apply mul_right_cancel₀ hpos
  rw [← h1]; ring

/-! ### The residual law -/

/-- Zero-padding of the first `t` columns to a full matrix. -/
def padCols {n t : ℕ} (f : Matrix (Fin n) (Fin t) ℝ) : Mat n :=
  fun i j => if h : j.val < t then f i ⟨j, h⟩ else 0

/-- `W` as a function of the first `t` columns: the last `n - t` rows of `Tm`. -/
def Wf {n t : ℕ} (f : Matrix (Fin n) (Fin t) ℝ) : Matrix (Fin (n-t)) (Fin n) ℝ :=
  fun i c => Tm (padCols f) t ⟨i + t, by omega⟩ c

lemma measurable_Wf {n t : ℕ} :
    Measurable (fun f : Fin n → Fin t → ℝ => (Wf f : Fin (n-t) → Fin n → ℝ)) := by
  have hp : Measurable (fun f : Fin n → Fin t → ℝ => (padCols f : Fin n → Fin n → ℝ)) := by
    refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
    unfold padCols
    split_ifs <;> fun_prop
  have hT := ((measurable_run (n := n) t).2).comp hp
  refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun c => ?_))
  exact (measurable_pi_apply c).comp ((measurable_pi_apply _).comp hT)

lemma Wf_firstColumns {n t : ℕ} (ht : t ≤ n) (A : Mat n) :
    Wf (firstColumns ht A) = fun (i : Fin (n-t)) (c : Fin n) => Tm A t ⟨i + t, by omega⟩ c := by
  have hloc := (locality (padCols (firstColumns ht A)) A
    (fun i j hj => by simp [padCols, firstColumns, hj]) t le_rfl).1
  funext i c
  simp only [Wf, hloc]

lemma residual_eq {n t : ℕ} (ht : t ≤ n) (A : Mat n) :
    residual A t = Wf (firstColumns ht A) *
      (Matrix.of fun c (j : Fin (n-t)) => A c ⟨j + t, by omega⟩) := by
  ext i j
  rw [Wf_firstColumns ht, GEPPGrowth.Main.residual, Matrix.submatrix_apply,
    run_col A t _ (by simp), Matrix.mul_apply]
  rfl

lemma Sig_eq {n t : ℕ} (ht : t ≤ n) (A : Mat n) :
    Sig A t = Wf (firstColumns ht A) * (Wf (firstColumns ht A)).transpose := by
  ext i j
  rw [Wf_firstColumns ht]
  simp only [Sig, Matrix.of_apply]
  rfl

lemma actualCov_embed {n t : ℕ} (ht : t ≤ n) (A : Mat n) : actualCov A t = embed (Sig A t) := by
  funext i j
  rw [actualCov_eq A t ht]
  simp only [embed, Sig, Matrix.of_apply]
  by_cases hi : i < n - t <;> by_cases hj : j < n - t <;> simp [hi, hj]

open scoped MatrixOrder in
lemma normal_one (d : ℕ) : normal (1 : Mat d) = Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  unfold normal multivariateGaussian
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), CFC.sqrt_one]
  conv_rhs => rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1))]
  congr 1
  funext y i
  simp

/-- Transposing an array of i.i.d. `N(0,1)` entries preserves its law. -/
lemma transpose_mp (m n : ℕ) :
    MeasurePreserving (fun (x : Fin n → Fin m → ℝ) j i => x i j)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1) := by
  have hm : Measurable (fun (x : Fin n → Fin m → ℝ) j i => x i j) := by fun_prop
  refine ⟨hm, (Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (gaussianReal 0 1).toFiniteSpanningSetsIn)
    fun s hs => ?_).symm⟩
  choose u hu hus using hs
  have hs' : s = fun j => Set.pi Set.univ (u j) := funext fun j => (hus j).symm
  subst hs'
  have hu' : ∀ j i, MeasurableSet (u j i) := fun j i => hu j i (Set.mem_univ _)
  have hpre : (fun (x : Fin n → Fin m → ℝ) j i => x i j) ⁻¹'
      Set.pi Set.univ (fun j => Set.pi Set.univ (u j)) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => u j i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi (hu' j)), hpre,
    Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Finset.prod_comm

/-- Splitting `n` i.i.d. columns into the first `t` and the last `n - t`. -/
lemma split_pi {n t : ℕ} (ht : t ≤ n) (ν : Measure (Vec n)) [IsProbabilityMeasure ν] :
    Measure.pi (fun _ : Fin n => ν) =
      ((Measure.pi fun _ : Fin t => ν).prod (Measure.pi fun _ : Fin (n-t) => ν)).map
        (fun p (j : Fin n) => if h : j.val < t then p.1 ⟨j, h⟩ else p.2 ⟨j - t, by omega⟩) := by
  let e : Fin t ⊕ Fin (n-t) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) e).map_eq
  have h2 := (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin t ⊕ Fin (n-t) => ν)).map_eq
  rw [← h1, ← h2, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  congr 1
  funext p j
  have he : ∀ x : Fin t ⊕ Fin (n-t) → Vec n,
      (MeasurableEquiv.piCongrLeft (fun _ => Vec n) e) x j = x (e.symm j) := by
    intro x
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [Function.comp_apply, he]
  by_cases h : j.val < t
  · rw [dif_pos h]
    have : e.symm j = Sum.inl ⟨j, h⟩ := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp [e])
    rw [this]; rfl
  · rw [dif_neg h]
    have : e.symm j = Sum.inr ⟨j - t, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp [e]; omega)
    rw [this]; rfl

/-- Law of the `n × n` Gaussian matrix by its first `t` and last `n - t` columns. -/
lemma gm_split {n t : ℕ} (ht : t ≤ n) :
    GaussianMatrix.gaussianMatrix n n =
      ((Measure.pi fun _ : Fin t => normal (1 : Mat n)).prod
        (Measure.pi fun _ : Fin (n-t) => normal (1 : Mat n))).map
        (fun p (i j : Fin n) => if h : j.val < t then p.1 ⟨j, h⟩ i else p.2 ⟨j - t, by omega⟩ i) := by
  have hj : Measurable (fun (p : (Fin t → Vec n) × (Fin (n-t) → Vec n)) (j : Fin n) =>
      if h : j.val < t then p.1 ⟨j, h⟩ else p.2 ⟨j - t, by omega⟩) := by
    refine measurable_pi_lambda _ (fun j => ?_)
    split_ifs <;> fun_prop
  have htr : Measurable (fun (z : Fin n → Vec n) (i j : Fin n) => z j i) := by fun_prop
  have h1 : GaussianMatrix.gaussianMatrix n n =
      (Measure.pi fun _ : Fin n => normal (1 : Mat n)).map (fun z i j => z j i) := by
    rw [normal_one]
    exact (transpose_mp n n).map_eq.symm
  rw [h1, split_pi ht, Measure.map_map htr hj]
  congr 1
  funext p i j
  simp only [Function.comp_apply]
  split_ifs <;> rfl

/-- A linear image of a centered multivariate Gaussian is the Gaussian with covariance `A S Aᵀ`
(from the proof of Proposition 3.1). -/
lemma mvG_map {m n : ℕ} (S : Mat n) (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S).map
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) =
    multivariateGaussian 0 (A * S * Aᵀ) := by
  have hS' : (A * S * Aᵀ).PosSemidef := by
    simpa using hS.mul_mul_conjTranspose_same A
  apply IsGaussian.ext
  · simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · have hadj : ∀ w : EuclideanSpace ℝ (Fin m),
        ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).adjoint w).ofLp =
          Aᵀ *ᵥ w.ofLp := by
      intro w
      have h1 := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
      have h2 := congrArg (fun f => (f w).ofLp) h1
      simp only [Matrix.ofLp_toEuclideanLin_apply] at h2
      rw [← ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_toLinearMap]
      simpa using h2.symm
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', hadj, hadj]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u.ofLp A,
      Matrix.mulVec_transpose]

lemma normal_map_mulVec {m n : ℕ} (S : Mat n) (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (normal S).map (fun x => A *ᵥ x) = normal (A * S * Aᵀ) := by
  unfold normal
  rw [← mvG_map S hS A, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- Columns `W g_j` of i.i.d. standard Gaussian `g_j` are i.i.d. `N(0, W Wᵀ)`. -/
lemma colLaw {n m : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) {E : Set (Mat m)} (hE : MeasurableSet E) :
    (Measure.pi fun _ : Fin m => normal (1 : Mat n))
      {b | W * (Matrix.of fun (c : Fin n) (j : Fin m) => b j c) ∈ E} =
      columnsLaw (W * W.transpose) m E := by
  have h1 := normal_map_mulVec (1 : Mat n) Matrix.PosSemidef.one W
  rw [Matrix.mul_one] at h1
  have hT : Measurable (fun (z : Fin m → Vec m) => (fun i j => z j i : Matrix (Fin m) (Fin m) ℝ)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)))
  have hM : Measurable (fun (b : Fin m → Vec n) (j : Fin m) => W *ᵥ b j) := by
    refine measurable_pi_lambda _ (fun j => ?_)
    exact (Matrix.toLin' W).continuous_of_finiteDimensional.measurable.comp (measurable_pi_apply j)
  unfold columnsLaw
  rw [← h1, ← Measure.pi_map_pi (fun _ => by fun_prop)]
  erw [Measure.map_apply hT hE, Measure.map_apply hM (hT hE)]
  congr 1

lemma measurable_matMul {α : Type*} [MeasurableSpace α] {a b c : ℕ}
    {X : α → Matrix (Fin a) (Fin b) ℝ} {Y : α → Matrix (Fin b) (Fin c) ℝ}
    (hX : Measurable X) (hY : Measurable Y) : Measurable (fun x => X x * Y x) := by
  refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hX)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hY))

/-- First half of Lemma 4.13: the residual law, for every `t ≤ n`. -/
theorem residual_law {n t : ℕ} (ht : t ≤ n) : HasResidualLaw n t ht := by
  have hWf : Measurable (fun f : Matrix (Fin n) (Fin t) ℝ => Wf f) := measurable_Wf
  refine ⟨⟨fun f => embed (Wf f * (Wf f).transpose), ?_, fun A => ?_⟩, fun H E hH hE => ?_⟩
  · have hWt : Measurable (fun f : Matrix (Fin n) (Fin t) ℝ => (Wf f).transpose) :=
      measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hWf)))
    have hG := measurable_matMul hWf hWt
    refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
    unfold embed
    split_ifs
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hG)
    · exact measurable_const
    · exact measurable_const
  · rw [actualCov_embed ht, Sig_eq ht]
  · -- column split of the Gaussian matrix
    set ρF := Measure.pi fun _ : Fin t => normal (1 : Mat n)
    set ρG := Measure.pi fun _ : Fin (n-t) => normal (1 : Mat n)
    set J : (Fin t → Vec n) × (Fin (n-t) → Vec n) → Fin n → Fin n → ℝ :=
      fun p i j => if h : j.val < t then p.1 ⟨j, h⟩ i else p.2 ⟨j - t, by omega⟩ i with hJdef
    have hJ : Measurable J := by
      refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
      simp only [hJdef]
      split_ifs <;> fun_prop
    let trF : (Fin t → Vec n) → Matrix (Fin n) (Fin t) ℝ := fun a i j => a j i
    let trG : (Fin (n-t) → Vec n) → Matrix (Fin n) (Fin (n-t)) ℝ :=
      fun b => Matrix.of fun c j => b j c
    have htrF : Measurable trF := measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)))
    have htrG : Measurable trG := measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)))
    have hF_J : ∀ p, firstColumns ht (J p) = trF p.1 := by
      intro p; funext i j; simp [firstColumns, hJdef, trF]
    have hR_J : ∀ p, GEPPGrowth.Main.residual (J p) t = Wf (trF p.1) * trG p.2 := by
      intro p
      refine (residual_eq ht (J p)).trans ?_
      rw [hF_J]
      congr 1
      ext c j
      show (if h : (j.val + t) < t then p.1 ⟨j.val + t, h⟩ c
        else p.2 ⟨j.val + t - t, by omega⟩ c) = p.2 j c
      rw [dif_neg (by omega)]
      simp only [Nat.add_sub_cancel]
    -- the conditional probability of `E` given the first columns
    let ψ : Matrix (Fin n) (Fin t) ℝ → ENNReal := fun f => ρG {b | Wf f * trG b ∈ E}
    have hY : MeasurableSet {q : Matrix (Fin n) (Fin t) ℝ × (Fin (n-t) → Vec n) |
        Wf q.1 * trG q.2 ∈ E} :=
      (measurable_matMul (hWf.comp measurable_fst) (htrG.comp measurable_snd)) hE
    have hψ : Measurable ψ := measurable_measure_prodMk_left hY
    have hψ' : ∀ A : Mat n, columnsLaw (block (actualCov A t) (n-t)) (n-t) E = ψ (firstColumns ht A) := by
      intro A
      rw [block_actualCov ht, Sig_eq ht]
      exact (colLaw _ hE).symm
    have hFm : Measurable (fun A : Fin n → Fin n → ℝ => firstColumns ht A) :=
      measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply _).comp (measurable_pi_apply i)))
    have hg : Measurable (fun a : Fin t → Vec n => H.indicator ψ (trF a)) :=
      (hψ.indicator hH).comp htrF
    -- right-hand side
    have hR : ∫⁻ A in {A | firstColumns ht A ∈ H},
        columnsLaw (block (actualCov A t) (n-t)) (n-t) E ∂(GaussianMatrix.gaussianMatrix n n) =
        ∫⁻ a, H.indicator ψ (trF a) ∂ρF := by
      have e1 : ∫⁻ A in {A | firstColumns ht A ∈ H},
          columnsLaw (block (actualCov A t) (n-t)) (n-t) E ∂(GaussianMatrix.gaussianMatrix n n) =
          ∫⁻ A, H.indicator ψ (firstColumns ht A) ∂(GaussianMatrix.gaussianMatrix n n) := by
        have hS : MeasurableSet {A : Fin n → Fin n → ℝ | firstColumns ht A ∈ H} := hFm hH
        refine (lintegral_indicator hS _).symm.trans (lintegral_congr fun A => ?_)
        by_cases h : firstColumns ht A ∈ H
        · exact (Set.indicator_of_mem (show A ∈ {A | firstColumns ht A ∈ H} from h) _).trans
            ((hψ' A).trans (Set.indicator_of_mem h ψ).symm)
        · exact (Set.indicator_of_notMem (show A ∉ {A | firstColumns ht A ∈ H} from h) _).trans
            (Set.indicator_of_notMem h ψ).symm
      rw [e1, gm_split ht, ← hJdef,
        lintegral_map (f := fun A : Fin n → Fin n → ℝ => H.indicator ψ (firstColumns ht A))
        ((hψ.indicator hH).comp hFm) hJ]
      simp_rw [hF_J]
      rw [lintegral_prod (fun z : (Fin t → Vec n) × (Fin (n-t) → Vec n) => H.indicator ψ (trF z.1))
        (hg.comp measurable_fst).aemeasurable]
      simp
      rfl
    -- left-hand side
    rw [hR, gm_split ht]
    have hS : MeasurableSet {A : Fin n → Fin n → ℝ | firstColumns ht A ∈ H ∧
        GEPPGrowth.Main.residual A t ∈ E} := by
      have hRm : Measurable (fun A : Fin n → Fin n → ℝ => GEPPGrowth.Main.residual A t) := by
        have : (fun A : Fin n → Fin n → ℝ => GEPPGrowth.Main.residual A t) = fun A =>
            Wf (firstColumns ht A) * Matrix.of fun c (j : Fin (n-t)) => A c ⟨j + t, by omega⟩ :=
          funext fun A => residual_eq ht A
        rw [this]
        refine measurable_matMul (hWf.comp hFm) ?_
        refine measurable_pi_lambda _ (fun c => measurable_pi_lambda _ (fun j => ?_))
        change Measurable (fun A : Fin n → Fin n → ℝ => A c ⟨j + t, by omega⟩)
        fun_prop
      exact (hFm hH).inter (hRm hE)
    rw [Measure.map_apply hJ hS]
    have hpre : J ⁻¹' {A | firstColumns ht A ∈ H ∧ GEPPGrowth.Main.residual A t ∈ E} =
        {p | trF p.1 ∈ H ∧ Wf (trF p.1) * trG p.2 ∈ E} := by
      ext p; simp only [Set.mem_preimage, Set.mem_setOf_eq, hF_J, hR_J]
    rw [hpre, Measure.prod_apply (hpre ▸ hJ hS)]
    refine lintegral_congr fun a => ?_
    by_cases ha : trF a ∈ H
    · rw [Set.indicator_of_mem ha]
      congr 1
      ext b; simp [ha]
    · rw [Set.indicator_of_notMem ha]
      have : Prod.mk a ⁻¹' {p : (Fin t → Vec n) × (Fin (n-t) → Vec n) |
          trF p.1 ∈ H ∧ Wf (trF p.1) * trG p.2 ∈ E} = ∅ := by
        ext b; simp [ha]
      rw [this, measure_empty]

end GEPP413

open GEPPGrowth.Main in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    HasResidualLaw n (k-1) (by omega) ∧
    (∀ᵐ A ∂(GaussianMatrix.gaussianMatrix n n),
      (block (actualCov A (k-1)) (n-(k-1))).det =
        ((firstColumns (show k-1 ≤ n by omega) A).transpose *
          firstColumns (show k-1 ≤ n by omega) A).det /
        (pivotMinor (show k-1 ≤ n by omega) A).det ^ 2) :=
  ⟨GEPP413.residual_law _, GEPP413.det_part _⟩
