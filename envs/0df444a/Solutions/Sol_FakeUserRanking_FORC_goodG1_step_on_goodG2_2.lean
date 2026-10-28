-- Prove2me | solution 2 for FakeUserRanking.FORC.goodG1_step_on_goodG2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T08:00:42.496545+00:00
-- url     : https://prove2.me/submissions/b26d93ff-9dae-46c0-9362-d5b1c796c72d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent
import Theorems.Thm_FakeUserRanking_FORC_real_rHat_step_concentration

set_option autoImplicit false

open FakeUserRanking.FORC

namespace SolGoodG1StepOnGoodG2

variable {n L T : ℕ}

lemma S_eq (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) =
    ∑ i ∈ Finset.range (L - 1), (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + i + 1 = i + 2 by ring, pow_add]
  norm_num
  ring

lemma S_le (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 2 := by
  rw [S_eq, ← Finset.mul_sum]
  have := sum_geometric_two_le (L - 1)
  linarith

lemma levelW_nonneg (L : ℕ) (k : Fin L) : 0 ≤ levelW L k := by
  unfold levelW
  split_ifs
  · linarith [S_le L]
  · positivity

lemma realW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (o : Obs n) :
    0 ≤ realW inst π o := by
  rcases o with ⟨j, b⟩
  have h1 : 0 ≤ reach inst π j := by
    unfold reach
    apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r _
    · linarith [(inst.q_mem r).2]
    · linarith [(inst.μ_mem (π r)).2]
  have h2 := (inst.μ_mem (π j)).1
  have h3 := (inst.μ_mem (π j)).2
  have h4 := (inst.q_mem j).1
  cases b
  · simp only [realW]
    apply mul_nonneg (mul_nonneg h1 (by linarith))
    split_ifs <;> linarith
  · simp only [realW]; exact mul_nonneg h1 h2

lemma obsW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (o : Obs n) :
    0 ≤ obsW inst π a o := by
  cases a with
  | none => exact realW_nonneg inst π o
  | some a => simp only [obsW]; split_ifs <;> norm_num

lemma stepW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) (s : Fin T) :
    0 ≤ stepW inst P A τ s := by
  unfold stepW
  exact mul_nonneg (mul_nonneg (hw_nonneg _ _) ENNReal.toReal_nonneg) (obsW_nonneg _ _ _ _)

lemma pubHist_succ (A : Alg n L) (τ : Fin T → Step n L) (t : ℕ) (ht : t < T) :
    pubHist A τ (t + 1) = pubHist A τ t ++
      [(ranking A τ ⟨t, ht⟩, (τ ⟨t, ht⟩).2.1.isSome, (τ ⟨t, ht⟩).2.2)] := by
  unfold pubHist
  rw [List.take_add_one]
  simp [ht]

lemma budget_path (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∀ s, s ≤ T → ((pubHist A τ s).filter (fun s => s.2.1)).length ≤ F ∧
      (((pubHist A τ s).filter (fun s => s.2.1)).length : ℝ) =
        ∑ t ∈ Finset.range s, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
  intro s
  induction s with
  | zero => intro _; simp [pubHist]
  | succ s ih =>
    intro hs
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [pubHist_succ A τ s (by omega), List.filter_append, List.length_append,
      Finset.sum_range_succ, dif_pos (show s < T by omega), ← ih2]
    have hstep := hτ ⟨s, by omega⟩
    by_cases hF : F ≤ ((pubHist A τ s).filter (fun s => s.2.1)).length
    · have hPn := hP _ hF
      have hnone : (τ ⟨s, by omega⟩).2.1 = none := by
        by_contra hc
        apply hstep
        unfold stepW
        rw [hPn, PMF.pure_apply, if_neg hc]
        simp
      simp [hnone]
      omega
    · constructor
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h] <;> omega
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h]

lemma fake_count_le (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) ≤ F := by
  obtain ⟨b1, b2⟩ := budget_path inst P A F hP τ hτ T le_rfl
  have : ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) =
      ∑ t ∈ Finset.range T, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => if h : t < T then
      (if (τ ⟨t, h⟩).2.1.isSome then (1 : ℝ) else 0) else 0) T]
    apply Finset.sum_congr rfl
    intro s _
    rw [dif_pos s.isLt]
  rw [this, ← b2]
  exact_mod_cast b1

lemma foldl_fst (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) (l : List (Fin L × Obs n))
    (acc : List (Fin L × Obs n) × State n L) :
    (l.foldl (fun (acc : List (Fin L × Obs n) × State n L) (x : Fin L × Obs n) =>
      (acc.1 ++ [x], acc.2.update n T (forcRank tb fb acc.1 acc.2 x.1) x.1 x.2)) acc).1
      = acc.1 ++ l := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih]

lemma forcState_snoc (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) (l : List (Fin L × Obs n))
    (x : Fin L × Obs n) :
    forcState n T tb fb (l ++ [x]) =
      (forcState n T tb fb l).update n T (forcRank tb fb l (forcState n T tb fb l) x.1) x.1 x.2 := by
  unfold forcState
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_fst]
  simp

lemma forcState_nil (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) :
    forcState n T tb fb [] = State.init := rfl

lemma algHist_succ {T : ℕ} (τ : Fin T → Step n L) (t : ℕ) (ht : t < T) :
    algHist τ (t + 1) = algHist τ t ++ [((τ ⟨t, ht⟩).1, (τ ⟨t, ht⟩).2.2)] := by
  unfold algHist
  rw [List.take_add_one]
  simp [ht]

lemma stateAt_succ_eq {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : Fin T) :
    stateAt tb fb τ ((t : ℕ) + 1) =
      (stateAt tb fb τ t).update n T (ranking (forc n T tb fb) τ t) (τ t).1 (τ t).2.2 := by
  unfold stateAt
  rw [algHist_succ τ t t.isLt, forcState_snoc]
  rfl

lemma stateAt_zero {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) : stateAt tb fb τ 0 = State.init := by
  unfold stateAt algHist; simp [forcState_nil]

lemma sum_lt_succ {T : ℕ} (P : Fin T → Prop) [DecidablePred P] (m : ℕ) (hm : m < T) :
    (∑ t : Fin T, if (t : ℕ) < m + 1 ∧ P t then (1 : ℝ) else 0) =
      (∑ t : Fin T, if (t : ℕ) < m ∧ P t then (1 : ℝ) else 0) +
        if P ⟨m, hm⟩ then 1 else 0 := by
  have hsplit : ∀ t : Fin T,
      (if (t : ℕ) < m + 1 ∧ P t then (1 : ℝ) else 0) =
      (if (t : ℕ) < m ∧ P t then (1 : ℝ) else 0) +
        (if t = ⟨m, hm⟩ then (if P t then 1 else 0) else 0) := by
    intro t
    by_cases h1 : (t : ℕ) < m
    · have h2 : (t : ℕ) < m + 1 := by omega
      have h3 : t ≠ ⟨m, hm⟩ := by intro he; rw [he] at h1; exact lt_irrefl _ h1
      by_cases hP : P t <;> simp [h1, h2, h3, hP]
    · by_cases h2 : (t : ℕ) < m + 1
      · have h3 : (t : ℕ) = m := by omega
        have h4 : t = ⟨m, hm⟩ := Fin.ext h3
        subst h4
        by_cases hP : P ⟨m, hm⟩ <;> simp [h1, h2, hP]
      · have h3 : t ≠ ⟨m, hm⟩ := by intro he; rw [he] at h2; simp at h2
        simp [h1, h2, h3]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

open Classical in
lemma stateAt_cnt_eq_sum {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (g : Fin (numLevels T)) (i : Fin n) :
    ∀ m ≤ T, ((stateAt tb fb τ m).cnt g i : ℝ) =
      ∑ t : Fin T, if (t : ℕ) < m ∧ (τ t).1 = g ∧
        (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 then (1 : ℝ) else 0 := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [stateAt_zero]
    simp [State.init]
  | succ m ih =>
    intro hm
    have hm_lt : m < T := by omega
    rw [sum_lt_succ (fun t => (τ t).1 = g ∧ (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1) m hm_lt]
    rw [← ih (by omega)]
    have hst := stateAt_succ_eq tb fb τ ⟨m, hm_lt⟩
    dsimp only at hst
    rw [hst]
    unfold State.update
    dsimp only
    by_cases h1 : g = (τ ⟨m, hm_lt⟩).1
    · subst h1
      by_cases h2 : (ranking (forc n T tb fb) τ ⟨m, hm_lt⟩).symm i ≤ (τ ⟨m, hm_lt⟩).2.2.1 <;>
        simp [h2]
    · have h1' : (τ ⟨m, hm_lt⟩).1 ≠ g := Ne.symm h1
      simp [h1, h1']

open Classical in
lemma stateAt_clk_eq_sum {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (g : Fin (numLevels T)) (i : Fin n) :
    ∀ m ≤ T, ((stateAt tb fb τ m).clk g i : ℝ) =
      ∑ t : Fin T, if (t : ℕ) < m ∧ (τ t).1 = g ∧
        (τ t).2.2.2 = true ∧ i = ranking (forc n T tb fb) τ t (τ t).2.2.1 then (1 : ℝ) else 0 := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [stateAt_zero]
    simp [State.init]
  | succ m ih =>
    intro hm
    have hm_lt : m < T := by omega
    rw [sum_lt_succ (fun t => (τ t).1 = g ∧ (τ t).2.2.2 = true ∧
      i = ranking (forc n T tb fb) τ t (τ t).2.2.1) m hm_lt]
    rw [← ih (by omega)]
    have hst := stateAt_succ_eq tb fb τ ⟨m, hm_lt⟩
    dsimp only at hst
    rw [hst]
    unfold State.update
    dsimp only
    by_cases h1 : g = (τ ⟨m, hm_lt⟩).1
    · subst h1
      by_cases h2 : (τ ⟨m, hm_lt⟩).2.2.2 = true ∧
          i = ranking (forc n T tb fb) τ ⟨m, hm_lt⟩ (τ ⟨m, hm_lt⟩).2.2.1 <;>
        simp [h2]
    · have h1' : (τ ⟨m, hm_lt⟩).1 ≠ g := Ne.symm h1
      simp [h1, h1']

open Classical in
noncomputable def cntR {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) : ℝ :=
  ∑ t : Fin T, if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1 = none ∧
    (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 then 1 else 0

open Classical in
noncomputable def clkR {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) : ℝ :=
  ∑ t : Fin T, if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1 = none ∧
    (τ t).2.2.2 = true ∧ i = ranking (forc n T tb fb) τ t (τ t).2.2.1 then 1 else 0

open Classical in
noncomputable def cntF {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) : ℝ :=
  ∑ t : Fin T, if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1.isSome ∧
    (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 then 1 else 0

open Classical in
noncomputable def clkF {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) : ℝ :=
  ∑ t : Fin T, if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1.isSome ∧
    (τ t).2.2.2 = true ∧ i = ranking (forc n T tb fb) τ t (τ t).2.2.1 then 1 else 0

lemma cnt_decomp {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) :
    ((stateAt tb fb τ ((s : ℕ) + 1)).cnt g i : ℝ) =
      cntR tb fb τ s i g + cntF tb fb τ s i g := by
  rw [stateAt_cnt_eq_sum tb fb τ g i ((s : ℕ) + 1) (by omega)]
  unfold cntR cntF
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have hle : ((t : ℕ) < (s : ℕ) + 1) ↔ t ≤ s := by
    rw [Fin.le_def]; omega
  by_cases hts : t ≤ s
  · have hts' : (t : ℕ) < (s : ℕ) + 1 := hle.mpr hts
    cases hact : (τ t).2.1 with
    | none =>
      by_cases h1 : (τ t).1 = g <;>
        by_cases h2 : (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 <;>
        simp [hts, hts', hact, h1, h2]
    | some a =>
      by_cases h1 : (τ t).1 = g <;>
        by_cases h2 : (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 <;>
        simp [hts, hts', hact, h1, h2]
  · have hts' : ¬ ((t : ℕ) < (s : ℕ) + 1) := fun h => hts (hle.mp h)
    simp [hts, hts']

lemma clk_decomp {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) :
    ((stateAt tb fb τ ((s : ℕ) + 1)).clk g i : ℝ) =
      clkR tb fb τ s i g + clkF tb fb τ s i g := by
  rw [stateAt_clk_eq_sum tb fb τ g i ((s : ℕ) + 1) (by omega)]
  unfold clkR clkF
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have hle : ((t : ℕ) < (s : ℕ) + 1) ↔ t ≤ s := by
    rw [Fin.le_def]; omega
  by_cases hts : t ≤ s
  · have hts' : (t : ℕ) < (s : ℕ) + 1 := hle.mpr hts
    cases hact : (τ t).2.1 with
    | none =>
      by_cases h1 : (τ t).1 = g <;>
        by_cases h2 : (τ t).2.2.2 = true ∧ i = ranking (forc n T tb fb) τ t (τ t).2.2.1 <;>
        simp [hts, hts', hact, h1, h2]
    | some a =>
      by_cases h1 : (τ t).1 = g <;>
        by_cases h2 : (τ t).2.2.2 = true ∧ i = ranking (forc n T tb fb) τ t (τ t).2.2.1 <;>
        simp [hts, hts', hact, h1, h2]
  · have hts' : ¬ ((t : ℕ) < (s : ℕ) + 1) := fun h => hts (hle.mp h)
    simp [hts, hts']

lemma clkR_bounds {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) :
    0 ≤ clkR tb fb τ s i g ∧ clkR tb fb τ s i g ≤ cntR tb fb τ s i g := by
  unfold clkR cntR
  refine ⟨Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num), ?_⟩
  apply Finset.sum_le_sum
  intro t _
  split_ifs with h1 h2
  · norm_num
  · exfalso
    apply h2
    refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
    have hsymm : (ranking (forc n T tb fb) τ t).symm i = (τ t).2.2.1 :=
      Equiv.symm_apply_eq (ranking (forc n T tb fb) τ t) |>.mpr h1.2.2.2.2
    rw [hsymm]
  · norm_num
  · norm_num

lemma clkF_bounds {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) :
    0 ≤ clkF tb fb τ s i g ∧ clkF tb fb τ s i g ≤ cntF tb fb τ s i g := by
  unfold clkF cntF
  refine ⟨Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num), ?_⟩
  apply Finset.sum_le_sum
  intro t _
  split_ifs with h1 h2
  · norm_num
  · exfalso
    apply h2
    refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
    have hsymm : (ranking (forc n T tb fb) τ t).symm i = (τ t).2.2.1 :=
      Equiv.symm_apply_eq (ranking (forc n T tb fb) τ t) |>.mpr h1.2.2.2.2
    rw [hsymm]
  · norm_num
  · norm_num

lemma cntF_le_exposure {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (g : Fin (numLevels T)) :
    cntF tb fb τ s i g ≤ (exposure g τ : ℝ) := by
  unfold cntF exposure
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_le_sum
  intro t _
  split_ifs with h1 h2
  · norm_num
  · exfalso; exact h2 ⟨h1.2.1, h1.2.2.1⟩
  · norm_num
  · norm_num

lemma sum_cntF_le_fake {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (s : Fin T) (i : Fin n) (k : Fin (numLevels T)) :
    ∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k), cntF tb fb τ s i g ≤
      ∑ t : Fin T, if (τ t).2.1.isSome then (1 : ℝ) else 0 := by
  calc ∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k), cntF tb fb τ s i g
      ≤ ∑ g : Fin (numLevels T), cntF tb fb τ s i g := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro g
        exact le_trans (clkF_bounds tb fb τ s i g).1 (clkF_bounds tb fb τ s i g).2
    _ = ∑ t : Fin T, ∑ g : Fin (numLevels T),
          if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1.isSome ∧
            (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 then (1 : ℝ) else 0 := by
        unfold cntF
        rw [Finset.sum_comm]
    _ ≤ ∑ t : Fin T, if (τ t).2.1.isSome then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro t _
        have h_eq : (∑ g : Fin (numLevels T),
            if t ≤ s ∧ (τ t).1 = g ∧ (τ t).2.1.isSome ∧
              (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 then (1 : ℝ) else 0) =
          ∑ g : Fin (numLevels T),
            if (τ t).1 = g then
              (if t ≤ s ∧ (τ t).2.1.isSome ∧
                (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 then (1 : ℝ) else 0)
            else 0 := by
          apply Finset.sum_congr rfl
          intro g _
          by_cases hg : (τ t).1 = g <;> by_cases h1 : t ≤ s <;>
            by_cases h2 : ((τ t).2.1.isSome : Prop) <;>
            by_cases h3 : (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 <;>
            simp [hg, h1, h2, h3]
        rw [h_eq, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        split_ifs with h1 h2
        · norm_num
        · exfalso; exact h2 h1.2.1
        · norm_num
        · norm_num

open Classical in
lemma real_perturbation_reduction (μ A B ηR cR ηF cF : ℝ)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hA0 : 0 ≤ A) (hB4 : 4 ≤ B)
    (hcR0 : 0 ≤ cR) (hcR_le : cR ≤ ηR)
    (hcF0 : 0 ≤ cF) (hcF_le : cF ≤ ηF)
    (hηF_le : ηF ≤ B)
    (hviol : ¬ (
      (if ηR + ηF = 0 then 0 else (cR + cF) / (ηR + ηF)) -
        (Real.sqrt ((3 / 2) * A / max (ηR + ηF) 1) + B / max (ηR + ηF) 1) ≤ μ ∧
      μ ≤ (if ηR + ηF = 0 then 0 else (cR + cF) / (ηR + ηF)) +
        (Real.sqrt ((3 / 2) * A / max (ηR + ηF) 1) + B / max (ηR + ηF) 1))) :
    0 < ηR ∧ Real.sqrt ((3 / 2) * A / ηR) < |cR / ηR - μ| := by
  set η := ηR + ηF
  set r := if η = 0 then (0 : ℝ) else (cR + cF) / η
  set w := Real.sqrt ((3 / 2) * A / max η 1) + B / max η 1
  have hηR0 : 0 ≤ ηR := le_trans hcR0 hcR_le
  have hηF0 : 0 ≤ ηF := le_trans hcF0 hcF_le
  have hη0 : 0 ≤ η := by linarith
  have hr0 : 0 ≤ r := by
    unfold r
    split_ifs
    · norm_num
    · positivity
  have hr1 : r ≤ 1 := by
    unfold r
    split_ifs with h0
    · norm_num
    · have hpos : 0 < η := lt_of_le_of_ne hη0 (Ne.symm h0)
      rw [div_le_one hpos]
      linarith
  have hmax_pos : 0 < max η 1 := lt_of_lt_of_le zero_lt_one (le_max_right η 1)
  have hB_lt_max : B < max η 1 := by
    by_contra hle
    push_neg at hle
    have hdiv1 : 1 ≤ B / max η 1 := (one_le_div hmax_pos).mpr hle
    have hsqrt0 : 0 ≤ Real.sqrt ((3 / 2) * A / max η 1) := Real.sqrt_nonneg _
    have hw1 : 1 ≤ w := by unfold w; linarith
    exact hviol ⟨by linarith, by linarith⟩
  have h1_lt_η : 1 < η := by
    by_contra hle
    push_neg at hle
    have hmax1 : max η 1 = 1 := max_eq_right hle
    rw [hmax1] at hB_lt_max
    linarith
  have hmax_eq : max η 1 = η := max_eq_left h1_lt_η.le
  have hB_lt_η : B < η := by rwa [hmax_eq] at hB_lt_max
  have hηR_pos : 0 < ηR := by linarith
  have hη_pos : 0 < η := by linarith
  have hη_ne : η ≠ 0 := hη_pos.ne'
  have hηR_ne : ηR ≠ 0 := hηR_pos.ne'
  have hr_eq : r = (cR + cF) / η := if_neg hη_ne
  have hw_eq : w = Real.sqrt ((3 / 2) * A / η) + B / η := by
    unfold w; rw [hmax_eq]
  have hw_lt_abs : w < |r - μ| := by
    by_contra hle
    push_neg at hle
    have habs := abs_le.mp hle
    exact hviol ⟨by linarith, by linarith⟩
  have hdecomp : r - μ = (cR - ηR * μ) / η + (cF - ηF * μ) / η := by
    rw [hr_eq]
    have : η = ηR + ηF := rfl
    field_simp
    ring
  have hcF_abs : |(cF - ηF * μ) / η| ≤ B / η := by
    rw [abs_div, abs_of_pos hη_pos]
    apply div_le_div_of_nonneg_right _ hη_pos.le
    rw [abs_le]
    have h1 : 0 ≤ ηF * μ := mul_nonneg hηF0 hμ0
    have h2 : ηF * μ ≤ ηF := by nlinarith
    constructor <;> linarith
  have htri : |r - μ| ≤ |(cR - ηR * μ) / η| + |(cF - ηF * μ) / η| := by
    rw [hdecomp]
    exact abs_add_le _ _
  have hsqrt_lt : Real.sqrt ((3 / 2) * A / η) < |(cR - ηR * μ) / η| := by
    linarith
  have hfactor : (cR - ηR * μ) / η = (ηR / η) * (cR / ηR - μ) := by
    field_simp
  have habs_factor : |(cR - ηR * μ) / η| = (ηR / η) * |cR / ηR - μ| := by
    rw [hfactor, abs_mul, abs_of_pos (div_pos hηR_pos hη_pos)]
  rw [habs_factor] at hsqrt_lt
  have hmul : (η / ηR) * Real.sqrt ((3 / 2) * A / η) < |cR / ηR - μ| := by
    have hpos : 0 < η / ηR := div_pos hη_pos hηR_pos
    have h1 := mul_lt_mul_of_pos_left hsqrt_lt hpos
    have h2 : (η / ηR) * ((ηR / η) * |cR / ηR - μ|) = |cR / ηR - μ| := by
      field_simp
    rwa [h2] at h1
  have hsqrt_le : Real.sqrt ((3 / 2) * A / ηR) ≤ (η / ηR) * Real.sqrt ((3 / 2) * A / η) := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hsq_eq : (η / ηR) ^ 2 * ((3 / 2) * A / η) = (η / ηR) * ((3 / 2) * A / ηR) := by
      field_simp
    rw [hsq_eq]
    have h1_le : 1 ≤ η / ηR := (one_le_div hηR_pos).mpr (by linarith)
    have hnn : 0 ≤ (3 / 2) * A / ηR := by positivity
    nlinarith
  exact ⟨hηR_pos, lt_of_le_of_lt hsqrt_le hmul⟩

end SolGoodG1StepOnGoodG2

open Classical in
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (s : Fin T) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) (i : Fin n) :
    prob inst P (forc n T tb fb) T
      (fun τ => goodG2 F τ ∧ ¬ (
        rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i -
          window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i ≤ inst.μ i ∧
        inst.μ i ≤
          rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i +
            window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i)) ≤
      delta n T / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) := by
  set Alg0 := forc n T tb fb
  have hw_nonneg : ∀ h k, 0 ≤ Alg0.w h k := fun _ k => SolGoodG1StepOnGoodG2.levelW_nonneg _ k
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hL1 : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hL1' : (1 : ℝ) ≤ numLevels T := by exact_mod_cast hL1
  have hA0 : 0 ≤ Real.log (4 * (n : ℝ) * T / delta n T) := by
    have e1 : 4 * (n : ℝ) * T / delta n T = 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
      unfold delta; field_simp
    rw [e1]
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
    nlinarith
  have hB0 : 0 ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) := by
    have e2 : 2 * (numLevels T : ℝ) / delta n T = 2 * (numLevels T : ℝ) * (n : ℝ) ^ 3 * T := by
      unfold delta; field_simp
    rw [e2]
    apply Real.log_nonneg
    have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
    have h2L : (1 : ℝ) ≤ 2 * (numLevels T : ℝ) * (n : ℝ) ^ 3 := by nlinarith
    nlinarith
  refine le_trans ?_ (real_rHat_step_concentration n T F hn hT inst hμ P hP tb htb fb s k hk i)
  unfold prob expect
  apply Finset.sum_le_sum
  intro τ _
  by_cases hW0 : trajW inst P Alg0 T τ = 0
  · rw [hW0]; simp
  have hτ : ∀ t, stepW inst P Alg0 τ t ≠ 0 := by
    intro t ht; apply hW0; unfold trajW
    exact Finset.prod_eq_zero (Finset.mem_univ t) ht
  have hW_nn : 0 ≤ trajW inst P Alg0 T τ :=
    Finset.prod_nonneg (fun t _ => SolGoodG1StepOnGoodG2.stepW_nonneg inst P Alg0 hw_nonneg τ t)
  apply mul_le_mul_of_nonneg_left _ hW_nn
  dsimp only
  split_ifs with hviol hconc
  · norm_num
  · exfalso
    apply hconc
    obtain ⟨hG2, hnot_win⟩ := hviol
    let ηR := (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k),
        SolGoodG1StepOnGoodG2.cntR tb fb τ s i g) / 2 ^ ((k : ℕ) + 1) +
      SolGoodG1StepOnGoodG2.cntR tb fb τ s i k
    let cR := (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k),
        SolGoodG1StepOnGoodG2.clkR tb fb τ s i g) / 2 ^ ((k : ℕ) + 1) +
      SolGoodG1StepOnGoodG2.clkR tb fb τ s i k
    let ηF := (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k),
        SolGoodG1StepOnGoodG2.cntF tb fb τ s i g) / 2 ^ ((k : ℕ) + 1) +
      SolGoodG1StepOnGoodG2.cntF tb fb τ s i k
    let cF := (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k),
        SolGoodG1StepOnGoodG2.clkF tb fb τ s i g) / 2 ^ ((k : ℕ) + 1) +
      SolGoodG1StepOnGoodG2.clkF tb fb τ s i k
    have hη_eq : etaHat (stateAt tb fb τ ((s : ℕ) + 1)) k i = ηR + ηF := by
      unfold etaHat ηR ηF
      simp_rw [SolGoodG1StepOnGoodG2.cnt_decomp tb fb τ s i]
      rw [Finset.sum_add_distrib]
      ring
    have hr_eq : rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i =
        if ηR + ηF = 0 then 0 else (cR + cF) / (ηR + ηF) := by
      unfold rHat
      rw [hη_eq]
      have hclk_eq : ((∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k),
          ((stateAt tb fb τ ((s : ℕ) + 1)).clk g i : ℝ)) / 2 ^ ((k : ℕ) + 1) +
            (stateAt tb fb τ ((s : ℕ) + 1)).clk k i) = cR + cF := by
        unfold cR cF
        simp_rw [SolGoodG1StepOnGoodG2.clk_decomp tb fb τ s i]
        rw [Finset.sum_add_distrib]
        ring
      rw [hclk_eq]
    have hw_eq : window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i =
        Real.sqrt ((3 / 2) * Real.log (4 * (n : ℝ) * T / delta n T) / max (ηR + ηF) 1) +
          (Real.log (2 * (numLevels T : ℝ) / delta n T) + 4) / max (ηR + ηF) 1 := by
      unfold window21
      rw [hη_eq]
    rw [hr_eq, hw_eq] at hnot_win
    have hcR0 : 0 ≤ cR := by
      unfold cR
      apply add_nonneg
      · apply div_nonneg
        · exact Finset.sum_nonneg (fun g _ => (SolGoodG1StepOnGoodG2.clkR_bounds tb fb τ s i g).1)
        · positivity
      · exact (SolGoodG1StepOnGoodG2.clkR_bounds tb fb τ s i k).1
    have hcR_le : cR ≤ ηR := by
      unfold cR ηR
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact Finset.sum_le_sum (fun g _ => (SolGoodG1StepOnGoodG2.clkR_bounds tb fb τ s i g).2)
      · exact (SolGoodG1StepOnGoodG2.clkR_bounds tb fb τ s i k).2
    have hcF0 : 0 ≤ cF := by
      unfold cF
      apply add_nonneg
      · apply div_nonneg
        · exact Finset.sum_nonneg (fun g _ => (SolGoodG1StepOnGoodG2.clkF_bounds tb fb τ s i g).1)
        · positivity
      · exact (SolGoodG1StepOnGoodG2.clkF_bounds tb fb τ s i k).1
    have hcF_le : cF ≤ ηF := by
      unfold cF ηF
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact Finset.sum_le_sum (fun g _ => (SolGoodG1StepOnGoodG2.clkF_bounds tb fb τ s i g).2)
      · exact (SolGoodG1StepOnGoodG2.clkF_bounds tb fb τ s i k).2
    have hηF_le : ηF ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 4 := by
      unfold ηF
      have h1 : (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < k),
          SolGoodG1StepOnGoodG2.cntF tb fb τ s i g) / 2 ^ ((k : ℕ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hsum := SolGoodG1StepOnGoodG2.sum_cntF_le_fake tb fb τ s i k
        have hfake := SolGoodG1StepOnGoodG2.fake_count_le inst P Alg0 F hP τ hτ
        have hk' : (F : ℝ) ≤ 2 ^ ((k : ℕ) + 1) := by exact_mod_cast hk
        linarith
      have h2 : SolGoodG1StepOnGoodG2.cntF tb fb τ s i k ≤
          Real.log (2 * (numLevels T : ℝ) / delta n T) + 3 :=
        le_trans (SolGoodG1StepOnGoodG2.cntF_le_exposure tb fb τ s i k) (hG2 k hk)
      linarith
    exact SolGoodG1StepOnGoodG2.real_perturbation_reduction
      (inst.μ i)
      (Real.log (4 * (n : ℝ) * T / delta n T))
      (Real.log (2 * (numLevels T : ℝ) / delta n T) + 4)
      ηR cR ηF cF
      (inst.μ_mem i).1 (inst.μ_mem i).2
      hA0 (by linarith) hcR0 hcR_le hcF0 hcF_le hηF_le hnot_win
  · norm_num
  · norm_num
