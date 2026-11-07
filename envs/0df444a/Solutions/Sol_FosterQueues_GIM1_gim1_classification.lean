-- Prove2me | solution 1 for FosterQueues.GIM1.gim1_classification
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:35:15.304897+00:00
-- url     : https://prove2.me/submissions/a5559b62-a105-4d61-a321-dde67533ede2

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_FosterQueues_GIM1_Model
import Theorems.Thm_QueueingFundamentals_Foundations_foster_criterion
import Theorems.Thm_FosterQueues_MG1_theorem3_first_passage_equations
import Theorems.Thm_FosterQueues_MG1_theorem4_transience_criterion
import Theorems.Thm_FosterQueues_MG1_theorem5_recurrence_criterion

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace GIM1Aux
open FosterQueues.GIM1

noncomputable def alpha (a : ℕ → ℝ) (i : ℕ) : ℝ := ∑' m : ℕ, a (i + 1 + m)

lemma summ_shift {a : ℕ → ℝ} (hsum : HasSum a 1) (i : ℕ) :
    Summable (fun m => a (i + 1 + m)) := by
  have := (summable_nat_add_iff (i+1)).mpr hsum.summable
  simpa [add_comm] using this

lemma split_one {a : ℕ → ℝ} (hsum : HasSum a 1) (i : ℕ) :
    ∑ n ∈ Finset.range (i+1), a n + alpha a i = 1 := by
  have := hsum.summable.sum_add_tsum_nat_add (i+1)
  rw [hsum.tsum_eq] at this
  rw [alpha, ← this]
  congr 1
  apply tsum_congr; intro m; congr 1; ring

lemma alpha_pos {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1) (i : ℕ) :
    0 < alpha a i :=
  (summ_shift hsum i).tsum_pos (fun _ => (ha _).le) 0 (ha _)

lemma alpha_succ {a : ℕ → ℝ} (hsum : HasSum a 1) (k : ℕ) :
    alpha a k = a (k+1) + alpha a (k+1) := by
  unfold alpha
  rw [(summ_shift hsum k).tsum_eq_zero_add]
  congr 1
  apply tsum_congr; intro m; congr 1; ring

/-- the row formula -/
lemma row {a : ℕ → ℝ} (i : ℕ) (f : ℕ → ℝ) :
    HasSum (fun j => gim1Matrix a i j * f j)
      (alpha a i * f 0 + ∑ n ∈ Finset.range (i+1), a n * f (i + 1 - n)) := by
  have h1 : HasSum (fun j => gim1Matrix a i j * f j)
      (∑ j ∈ Finset.range (i+2), gim1Matrix a i j * f j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    have : gim1Matrix a i j = 0 := by
      unfold gim1Matrix
      rw [if_neg (by omega), if_neg (by omega)]
    simp [this]
  convert h1 using 1
  symm
  rw [Finset.sum_range_succ']
  have h0 : gim1Matrix a i 0 = alpha a i := by simp [gim1Matrix, alpha]
  rw [h0, add_comm]
  congr 1
  rw [← Finset.sum_range_reflect (fun n => a n * f (i + 1 - n))]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_range] at hn
  have : gim1Matrix a i (n + 1) = a (i + 1 - 1 - n) := by
    unfold gim1Matrix
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1; omega
  rw [this]
  congr 2; omega


lemma stepProb_bounds (P : TransitionMatrix) : ∀ n i j, 0 ≤ P.stepProb n i j ∧ P.stepProb n i j ≤ 1 := by
  intro n
  induction n with
  | zero => intro i j; simp only [TransitionMatrix.stepProb]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    simp only [TransitionMatrix.stepProb]
    have hs : Summable (fun k => P.p i k * P.stepProb n k j) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (P.nonneg i k) (ih k j).1)
        (fun k => by
          have := mul_le_mul_of_nonneg_left (ih k j).2 (P.nonneg i k)
          simpa using this) (P.row_sum i).summable
    refine ⟨tsum_nonneg (fun k => mul_nonneg (P.nonneg i k) (ih k j).1), ?_⟩
    rw [← (P.row_sum i).tsum_eq]
    exact hs.tsum_le_tsum (fun k => by
          have := mul_le_mul_of_nonneg_left (ih k j).2 (P.nonneg i k)
          simpa using this) (P.row_sum i).summable

lemma stepProb_succ_ge (P : TransitionMatrix) (n i j k : ℕ) :
    P.p i k * P.stepProb n k j ≤ P.stepProb (n+1) i j := by
  simp only [TransitionMatrix.stepProb]
  have hs : Summable (fun k => P.p i k * P.stepProb n k j) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (P.nonneg i k) (stepProb_bounds P n k j).1)
      (fun k => by
        have := mul_le_mul_of_nonneg_left (stepProb_bounds P n k j).2 (P.nonneg i k)
        simpa using this) (P.row_sum i).summable
  exact hs.le_tsum k (fun l _ => mul_nonneg (P.nonneg i l) (stepProb_bounds P n l j).1)

lemma irred {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = gim1Matrix a) : P.Irreducible := by
  have up : ∀ n i, 0 < P.stepProb n i (i + n) := by
    intro n
    induction n with
    | zero => intro i; simp [TransitionMatrix.stepProb]
    | succ n ih =>
      intro i
      have h1 := stepProb_succ_ge P n i (i + (n+1)) (i+1)
      have h2 : P.p i (i+1) = a 0 := by
        rw [hP]; unfold gim1Matrix; rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
      have h3 := ih (i+1)
      rw [show i + 1 + n = i + (n+1) by ring] at h3
      rw [h2] at h1
      exact lt_of_lt_of_le (mul_pos (ha 0) h3) h1
  intro i j
  refine ⟨j+1, ?_⟩
  have h1 := stepProb_succ_ge P j i j 0
  have h2 : P.p i 0 = alpha a i := by rw [hP]; simp [gim1Matrix, alpha]
  have h3 := up j 0
  rw [zero_add] at h3
  rw [h2] at h1
  exact lt_of_lt_of_le (mul_pos (alpha_pos ha hsum i) h3) h1

lemma aper {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = gim1Matrix a) : P.Aperiodic := by
  intro k d hd
  have h1 := stepProb_succ_ge P 0 k k k
  have h0 : P.stepProb 0 k k = 1 := by simp [TransitionMatrix.stepProb]
  rw [h0, mul_one] at h1
  have hpos : 0 < P.p k k := by
    rw [hP]; unfold gim1Matrix
    by_cases hk : k = 0
    · subst hk; simp only [if_true]; simpa [alpha] using alpha_pos ha hsum 0
    · rw [if_neg hk, if_pos (by omega)]; exact ha _
  have := hd 1 one_pos (lt_of_lt_of_le hpos h1)
  exact Nat.dvd_one.mp this


/-- `T i = ∑_{n ≤ i} n a_n` -/
noncomputable def Tsum (a : ℕ → ℝ) (i : ℕ) : ℝ := ∑ n ∈ Finset.range (i+1), (n : ℝ) * a n

lemma sum_alpha {a : ℕ → ℝ} (hsum : HasSum a 1) (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), alpha a k = Tsum a K + (K+1) * alpha a K := by
  induction K with
  | zero => simp [Tsum]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, alpha_succ hsum K]
    simp only [Tsum]
    rw [Finset.sum_range_succ _ (K+1)]
    push_cast; ring

lemma Pl {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (r : ℝ) (hr : ENNReal.ofReal r < rhoInv a) :
    ∃ N, r < ∑ n ∈ Finset.range N, (n : ℝ) * a n := by
  unfold rhoInv at hr
  rw [ENNReal.tsum_eq_iSup_nat, lt_iSup_iff] at hr
  obtain ⟨N, hN⟩ := hr
  refine ⟨N, ?_⟩
  have : ∑ n ∈ Finset.range N, (n : ℝ≥0∞) * ENNReal.ofReal (a n) =
      ENNReal.ofReal (∑ n ∈ Finset.range N, (n : ℝ) * a n) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (ha n).le)]
    apply Finset.sum_congr rfl; intro n _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [this, ENNReal.ofReal_lt_ofReal_iff'] at hN
  exact hN.1

lemma Sb {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : rhoInv a ≤ ENNReal.ofReal r) (i : ℕ) :
    Tsum a i + (i+1) * alpha a i ≤ r := by
  rw [← ENNReal.ofReal_le_ofReal_iff hr0]
  refine le_trans ?_ hr
  unfold rhoInv
  have hsp := (ENNReal.summable (f := fun m : ℕ => (((m + (i+1) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (a (m + (i+1)))))).sum_add_tsum_nat_add'
      (f := fun n : ℕ => (n : ℝ≥0∞) * ENNReal.ofReal (a n))
  rw [← hsp]
  have hT : 0 ≤ Tsum a i :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (ha n).le)
  rw [ENNReal.ofReal_add hT (mul_nonneg (by positivity) (alpha_pos ha hsum i).le)]
  gcongr
  · rw [Tsum, ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (ha n).le)]
    apply le_of_eq; apply Finset.sum_congr rfl; intro n _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · rw [alpha, ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg
      (fun m => mul_nonneg (by positivity) (ha _).le) ((summ_shift hsum i).mul_left _)]
    apply ENNReal.tsum_le_tsum; intro m
    rw [ENNReal.ofReal_mul (by positivity), show m + (i+1) = i + 1 + m by ring]
    gcongr
    rw [show ((i:ℝ) + 1) = ((i + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
    exact_mod_cast (by omega : i + 1 ≤ i + 1 + m)


lemma lin_sum {a : ℕ → ℝ} (hsum : HasSum a 1) (i : ℕ) (u v : ℝ) :
    ∑ n ∈ Finset.range (i+1), a n * (u * ((i + 1 - n : ℕ) : ℝ) + v) =
      (u * (i+1) + v) * (1 - alpha a i) - u * Tsum a i := by
  have h1 := split_one hsum i
  have : ∑ n ∈ Finset.range (i+1), a n * (u * ((i + 1 - n : ℕ) : ℝ) + v) =
      ∑ n ∈ Finset.range (i+1), ((u * (i+1) + v) * a n - u * ((n : ℝ) * a n)) := by
    apply Finset.sum_congr rfl; intro n hn
    simp only [Finset.mem_range] at hn
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Tsum]
  rw [show ∑ n ∈ Finset.range (i+1), a n = 1 - alpha a i by linarith]

lemma partC {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = gim1Matrix a) (h1 : 1 < rhoInv a) :
    P.PositiveRecurrent := by
  obtain ⟨N, hN⟩ := Pl ha 1 (by simpa using h1)
  set δ := ∑ n ∈ Finset.range N, (n : ℝ) * a n - 1 with hδ
  have hδpos : 0 < δ := by linarith
  set K : ℝ := ∑ i ∈ Finset.range N, (1 + δ) / alpha a i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun i _ => div_nonneg (by linarith)
    (alpha_pos ha hsum i).le)
  set c : ℝ := 1 / δ with hc
  have hcpos : 0 < c := by positivity
  let x : ℕ → ℝ := fun j => if j = 0 then 0 else c * (j : ℝ) + c * K
  have hx : ∀ j, 0 ≤ x j := by
    intro j; simp only [x]; split_ifs
    · exact le_rfl
    · positivity
  have hrow : ∀ i, HasSum (fun j => P.p i j * x j)
      ((c * (i+1) + c * K) * (1 - alpha a i) - c * Tsum a i) := by
    intro i
    rw [hP]
    convert row (a := a) i x using 1
    simp only [x, if_true, mul_zero, zero_add]
    rw [← lin_sum hsum i c (c * K)]
    apply Finset.sum_congr rfl; intro n hn
    simp only [Finset.mem_range] at hn
    rw [if_neg (by omega)]
  refine foster_criterion P (irred ha hsum P hP) (aper ha hsum P hP) x hx
    (fun i => (hrow i).summable) ?_
  intro i hi
  rw [(hrow i).tsum_eq]
  simp only [x, if_neg hi]
  -- need: (i+1+K) α_i + T_i ≥ 1 + δ
  have key : 1 + δ ≤ ((i:ℝ) + 1 + K) * alpha a i + Tsum a i := by
    have hα := (alpha_pos ha hsum i)
    have hT0 : 0 ≤ Tsum a i :=
      Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (ha n).le)
    by_cases hiN : N ≤ i
    · have : ∑ n ∈ Finset.range N, (n : ℝ) * a n ≤ Tsum a i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun n _ _ => mul_nonneg (Nat.cast_nonneg _) (ha n).le)
      have : 0 ≤ ((i:ℝ) + 1 + K) * alpha a i := by positivity
      linarith
    · have hle : (1 + δ) / alpha a i ≤ K :=
        Finset.single_le_sum (f := fun i => (1 + δ) / alpha a i)
          (fun j _ => div_nonneg (by linarith) (alpha_pos ha hsum j).le)
          (Finset.mem_range.mpr (by omega))
      have : 1 + δ ≤ K * alpha a i := by
        rwa [div_le_iff₀ hα] at hle
      have : 0 ≤ ((i:ℝ) + 1) * alpha a i := by positivity
      nlinarith
  have hcδ : c * δ = 1 := by rw [hc]; field_simp
  nlinarith


/-- the substochastic operator of the chain killed at `0` -/
noncomputable def op (a : ℕ → ℝ) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else ∑ n ∈ Finset.range (i+1), a n * f (i + 1 - n)

lemma op_mono {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {f g : ℕ → ℝ} (h : ∀ j, f j ≤ g j) (i : ℕ) :
    op a f i ≤ op a g i := by
  unfold op; split_ifs
  · exact le_rfl
  · exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (h _) (ha n))

lemma op_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {f : ℕ → ℝ} (h : ∀ j, 0 ≤ f j) (i : ℕ) :
    0 ≤ op a f i := by
  unfold op; split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg (fun n _ => mul_nonneg (ha n) (h _))

lemma op_add (a f g : ℕ → ℝ) : op a (f + g) = op a f + op a g := by
  funext i; unfold op; simp only [Pi.add_apply]; split_ifs
  · simp
  · rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro n _; ring

lemma it_mono {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (t : ℕ) : ∀ {f g : ℕ → ℝ}, (∀ j, f j ≤ g j) →
    ∀ i, (op a)^[t] f i ≤ (op a)^[t] g i := by
  induction t with
  | zero => intro f g h i; exact h i
  | succ t ih =>
    intro f g h i
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (op_mono ha h) i

lemma it_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (t : ℕ) : ∀ {f : ℕ → ℝ}, (∀ j, 0 ≤ f j) →
    ∀ i, 0 ≤ (op a)^[t] f i := by
  induction t with
  | zero => intro f h i; exact h i
  | succ t ih =>
    intro f h i
    rw [Function.iterate_succ_apply]
    exact ih (op_nonneg ha h) i

lemma it_add (a : ℕ → ℝ) (t : ℕ) : ∀ f g : ℕ → ℝ, (op a)^[t] (f + g) = (op a)^[t] f + (op a)^[t] g := by
  induction t with
  | zero => intro f g; rfl
  | succ t ih =>
    intro f g
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      op_add, ih]

lemma partD {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = gim1Matrix a) (h1 : rhoInv a ≤ 1) :
    ¬ P.PositiveRecurrent := by
  intro hpr
  have ha' : ∀ n, 0 ≤ a n := fun n => (ha n).le
  obtain ⟨hfin, heq, -⟩ := FosterQueues.MG1.theorem3_first_passage_equations P
    (irred ha hsum P hP) (aper ha hsum P hP) hpr
  set μ : ℕ → ℝ≥0∞ := fun j => FosterQueues.MG1.meanFirstPassage P j 0 with hμ
  set d : ℕ → ℝ := fun j => if j = 0 then 0 else (μ j).toReal with hdd
  set e : ℕ → ℝ := fun j => if j = 0 then 0 else 1 with he
  have hd0 : ∀ j, 0 ≤ d j := by
    intro j; simp only [hdd]; split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  have he0 : ∀ j, 0 ≤ e j := by
    intro j; simp only [he]; split_ifs <;> norm_num
  have hd : d = e + op a d := by
    funext i
    simp only [Pi.add_apply]
    by_cases hi : i = 0
    · simp [hdd, he, op, hi]
    have hrow := row (a := a) i d
    have hd00 : d 0 = 0 := by simp [hdd]
    rw [hd00, mul_zero, zero_add] at hrow
    have hop : op a d i = ∑ n ∈ Finset.range (i+1), a n * d (i + 1 - n) := by
      simp [op, hi]
    rw [← hop] at hrow
    have hnn : ∀ j, 0 ≤ gim1Matrix a i j * d j := fun j =>
      mul_nonneg (by rw [← hP]; exact P.nonneg i j) (hd0 j)
    have hE : ∑' j : ℕ, ENNReal.ofReal (P.p i (j+1)) * μ (j+1) = ENNReal.ofReal (op a d i) := by
      rw [← hrow.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hrow.summable,
        tsum_eq_zero_add' (f := fun j => ENNReal.ofReal (gim1Matrix a i j * d j)) ENNReal.summable]
      simp only [hd00, mul_zero, ENNReal.ofReal_zero, zero_add]
      apply tsum_congr; intro j
      rw [ENNReal.ofReal_mul (by rw [← hP]; exact P.nonneg i (j+1)), hP]
      congr 1
      simp only [hdd, if_neg (Nat.succ_ne_zero j)]
      exact (ENNReal.ofReal_toReal (hfin (j+1) (Nat.succ_ne_zero j)).ne).symm
    have := heq i hi
    simp only [hdd, he, if_neg hi]
    rw [show FosterQueues.MG1.meanFirstPassage P i 0 = μ i from rfl] at this
    rw [this]
    have hE' : ∑' j : ℕ, ENNReal.ofReal (P.p i (j+1)) * FosterQueues.MG1.meanFirstPassage P (j+1) 0 =
        ENNReal.ofReal (op a d i) := hE
    rw [hE', ENNReal.toReal_add ENNReal.one_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_one,
      ENNReal.toReal_ofReal (op_nonneg ha' hd0 i)]
  -- the subharmonic function `Y i = i`
  set Y : ℕ → ℝ := fun i => (i : ℝ) with hY
  have hYop : ∀ i, Y i ≤ op a Y i := by
    intro i
    by_cases hi : i = 0
    · simp [hY, op, hi]
    simp only [op, if_neg hi, hY]
    have := lin_sum hsum i 1 0
    simp only [one_mul, add_zero, mul_one] at this
    rw [this]
    have hS := Sb ha hsum 1 zero_le_one (by simpa using h1) i
    nlinarith
  have hYit : ∀ t i, Y i ≤ (op a)^[t] Y i := by
    intro t
    induction t with
    | zero => intro i; exact le_rfl
    | succ t ih =>
      intro i
      rw [Function.iterate_succ_apply]
      exact le_trans (ih i) (it_mono ha' t hYop i)
  have hbound : ∀ t i, (op a)^[t] Y i ≤ ((i : ℝ) + t) * (op a)^[t] e i := by
    intro t
    induction t with
    | zero =>
      intro i
      by_cases hi : i = 0
      · simp [hY, he, hi]
      · simp [hY, he, hi]
    | succ t ih =>
      intro i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      by_cases hi : i = 0
      · simp [op, hi]
      simp only [op, if_neg hi]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.mem_range] at hn
      have h2 := ih (i + 1 - n)
      have h3 : ((i + 1 - n : ℕ) : ℝ) ≤ (i : ℝ) + 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have h4 := it_nonneg ha' t he0 (i + 1 - n)
      have h5 : ((i + 1 - n : ℕ) + (t : ℝ)) * (op a)^[t] e (i + 1 - n) ≤
          ((i : ℝ) + ↑(t + 1)) * (op a)^[t] e (i + 1 - n) := by
        apply mul_le_mul_of_nonneg_right _ h4; push_cast; linarith
      calc a n * (op a)^[t] Y (i + 1 - n) ≤ a n * (((i + 1 - n : ℕ) + (t : ℝ)) *
            (op a)^[t] e (i + 1 - n)) := mul_le_mul_of_nonneg_left h2 (ha' n)
        _ ≤ a n * (((i : ℝ) + ↑(t + 1)) * (op a)^[t] e (i + 1 - n)) :=
            mul_le_mul_of_nonneg_left h5 (ha' n)
        _ = ((i : ℝ) + ↑(t + 1)) * (a n * (op a)^[t] e (i + 1 - n)) := by ring
  have hdec : ∀ T i, d i = ∑ s ∈ Finset.range T, (op a)^[s] e i + (op a)^[T] d i := by
    intro T
    induction T with
    | zero => intro i; simp
    | succ T ih =>
      intro i
      rw [ih i, Finset.sum_range_succ]
      have : (op a)^[T] d = (op a)^[T] e + (op a)^[T+1] d := by
        conv_lhs => rw [hd]
        rw [it_add, Function.iterate_succ_apply]
      rw [this, Pi.add_apply]; ring
  have hlow : ∀ s : ℕ, 1 / ((s : ℝ) + 1) ≤ (op a)^[s] e 1 := by
    intro s
    have h1' := le_trans (hYit s 1) (hbound s 1)
    simp only [hY, Nat.cast_one] at h1'
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hT := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop (d 1)).exists
  obtain ⟨T, hT⟩ := hT
  have := hdec T 1
  have h6 : ∑ s ∈ Finset.range T, (1 / ((s : ℝ) + 1)) ≤ ∑ s ∈ Finset.range T, (op a)^[s] e 1 :=
    Finset.sum_le_sum (fun s _ => hlow s)
  have h7 := it_nonneg ha' T hd0 1
  linarith


/-- the harmonic function of the chain off `0`, normalised by `h 0 = 0`, `h 1 = 1` -/
noncomputable def hfun (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | M+1 => 1 + (1 / a 0) * ∑ k ∈ Finset.range M, alpha a (k+1) * hfun a (M - k)
decreasing_by all_goals omega

lemma hfun_zero (a : ℕ → ℝ) : hfun a 0 = 0 := by rw [hfun]

lemma hfun_ident {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (M : ℕ) :
    a 0 * hfun a (M+1) = a 0 + ∑ k ∈ Finset.range M, alpha a (k+1) * hfun a (M - k) := by
  rw [hfun]
  have := (ha 0).ne'
  field_simp

lemma hfun_one {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) : hfun a 1 = 1 := by
  have := hfun_ident ha 0
  simp only [Finset.range_zero, Finset.sum_empty, add_zero] at this
  have h0 := (ha 0).ne'
  field_simp at this
  linarith [this]

lemma hfun_diff {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1) (M : ℕ) :
    a 0 * (hfun a (M+2) - hfun a (M+1)) =
      alpha a 1 * hfun a (M+1) - ∑ k ∈ Finset.range M, a (k+2) * hfun a (M - k) := by
  have h1 := hfun_ident ha (M+1)
  have h2 := hfun_ident ha M
  rw [Finset.sum_range_succ'] at h1
  simp only [Nat.add_sub_add_right, Nat.sub_zero, zero_add] at h1
  have h3 : ∑ k ∈ Finset.range M, alpha a (k+1) * hfun a (M - k) =
      ∑ k ∈ Finset.range M, (a (k+2) * hfun a (M - k) + alpha a (k+1+1) * hfun a (M - k)) := by
    apply Finset.sum_congr rfl; intro k _
    rw [alpha_succ hsum (k+1)]; ring
  rw [h3, Finset.sum_add_distrib] at h2
  rw [mul_sub, h1, h2]; ring

lemma hfun_harm {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1) (i : ℕ) (hi : i ≠ 0) :
    HasSum (fun j => gim1Matrix a i j * hfun a j) (hfun a i) := by
  convert row (a := a) i (hfun a) using 1
  rw [hfun_zero, mul_zero, zero_add]
  obtain ⟨M, rfl⟩ : ∃ M, i = M + 1 := ⟨i - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.sub_zero, zero_add]
  have hd := hfun_diff ha hsum M
  have hs := split_one hsum 1
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add] at hs
  have hc : ∑ k ∈ Finset.range M, a (k + 1 + 1) * hfun a (M + 1 + 1 - (k + 1 + 1)) =
      ∑ k ∈ Finset.range M, a (k+2) * hfun a (M - k) := by
    apply Finset.sum_congr rfl; intro k hk
    simp only [Finset.mem_range] at hk
    congr 2; omega
  rw [hc, show M + 1 + 1 - 1 = M + 1 by omega, show M + 1 + 1 = M + 2 by omega]
  linear_combination -hd - hfun a (M+1) * hs

lemma hfun_mono_aux {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1) :
    ∀ M, ∀ i ≤ M, 0 ≤ hfun a i ∧ hfun a i ≤ hfun a M := by
  intro M
  induction M with
  | zero => intro i hi; rw [show i = 0 by omega, hfun_zero]; exact ⟨le_rfl, le_rfl⟩
  | succ M ih =>
    have hstep : hfun a M ≤ hfun a (M+1) := by
      rcases M with _ | M
      · rw [hfun_zero, zero_add, hfun_one ha]; norm_num
      · have hd := hfun_diff ha hsum M
        have hM0 := (ih (M+1) le_rfl).1
        have hle : ∑ k ∈ Finset.range M, a (k+2) * hfun a (M - k) ≤
            ∑ k ∈ Finset.range M, a (k+2) * hfun a (M+1) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (ih (M - k) (by omega)).2
            (ha _).le)
        have hpart : ∑ k ∈ Finset.range M, a (k+2) ≤ alpha a 1 := by
          unfold alpha
          have := (summ_shift hsum 1).sum_le_tsum (Finset.range M) (fun m _ => (ha _).le)
          convert this using 2 with k
          congr 1; ring
        rw [← Finset.sum_mul] at hle
        have : 0 ≤ a 0 * (hfun a (M + 2) - hfun a (M + 1)) := by
          rw [hd]; nlinarith
        have h0 := ha 0
        have : 0 ≤ hfun a (M + 2) - hfun a (M + 1) := by
          by_contra hneg; push_neg at hneg; nlinarith
        linarith
    intro i hi
    rcases Nat.lt_or_ge i (M+1) with h | h
    · have := ih i (by omega)
      exact ⟨this.1, le_trans this.2 hstep⟩
    · rw [show i = M + 1 by omega]
      exact ⟨le_trans (ih M le_rfl).1 hstep, le_rfl⟩

lemma hfun_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1) (i : ℕ) :
    0 ≤ hfun a i := (hfun_mono_aux ha hsum i i le_rfl).1

lemma hfun_mono {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1) : Monotone (hfun a) :=
  fun i j hij => (hfun_mono_aux ha hsum j i hij).2

lemma sumA {a : ℕ → ℝ} (hsum : HasSum a 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, alpha a (k+1) = Tsum a N + (N+1) * alpha a N - (1 - a 0) := by
  have h1 := sum_alpha hsum N
  rw [Finset.sum_range_succ'] at h1
  have h2 := split_one hsum 0
  simp only [zero_add, Finset.range_one, Finset.sum_singleton] at h2
  push_cast at h1 ⊢
  linarith

lemma partE {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = gim1Matrix a) (h1 : 1 ≤ rhoInv a) :
    FosterQueues.MG1.IsRecurrent P := by
  have hlim : Filter.Tendsto (hfun a) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop_of_monotone (hfun_mono ha hsum)
    by_contra hcon
    push_neg at hcon
    obtain ⟨b, hb⟩ := hcon
    set B := max b 1 with hB
    have hB1 : 1 ≤ B := le_max_right _ _
    have hBpos : 0 < B := by linarith
    have ha0 := ha 0
    set δ := a 0 / (2 * B) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := Pl ha (1 - δ) (lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr (by linarith)) h1)
    have hA : a 0 - δ < ∑ k ∈ Finset.range N, alpha a (k+1) := by
      rw [sumA hsum N]
      have : ∑ n ∈ Finset.range N, (n : ℝ) * a n ≤ Tsum a N :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun n _ _ => mul_nonneg (Nat.cast_nonneg _) (ha n).le)
      have : 0 ≤ ((N:ℝ) + 1) * alpha a N := by have := alpha_pos ha hsum N; positivity
      linarith
    have hstep : ∀ j, hfun a j + 1/2 ≤ hfun a (j + N + 1) := by
      intro j
      have hI := hfun_ident ha (j + N)
      have hj0 := hfun_nonneg ha hsum j
      have hsub : ∑ k ∈ Finset.range N, alpha a (k+1) * hfun a j ≤
          ∑ k ∈ Finset.range (j+N), alpha a (k+1) * hfun a (j + N - k) := by
        calc ∑ k ∈ Finset.range N, alpha a (k+1) * hfun a j
            ≤ ∑ k ∈ Finset.range N, alpha a (k+1) * hfun a (j + N - k) :=
              Finset.sum_le_sum (fun k hk => by
                simp only [Finset.mem_range] at hk
                exact mul_le_mul_of_nonneg_left (hfun_mono ha hsum (by omega))
                  (alpha_pos ha hsum _).le)
          _ ≤ ∑ k ∈ Finset.range (j+N), alpha a (k+1) * hfun a (j + N - k) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
                (fun k _ _ => mul_nonneg (alpha_pos ha hsum _).le (hfun_nonneg ha hsum _))
      rw [← Finset.sum_mul] at hsub
      have hjB : hfun a j ≤ B := le_trans (hb j).le (le_max_left _ _)
      have hδB : δ * hfun a j ≤ a 0 / 2 := by
        calc δ * hfun a j ≤ δ * B := mul_le_mul_of_nonneg_left hjB hδpos.le
          _ = a 0 / 2 := by rw [hδ]; field_simp
      have : a 0 * (hfun a j + 1/2) ≤ a 0 * hfun a (j + N + 1) := by nlinarith
      exact le_of_mul_le_mul_left this ha0
    have hiter : ∀ r : ℕ, (r : ℝ) / 2 ≤ hfun a (r * (N+1)) := by
      intro r
      induction r with
      | zero => simp [hfun_zero]
      | succ r ih =>
        have := hstep (r * (N+1))
        rw [show r * (N+1) + N + 1 = (r+1) * (N+1) by ring] at this
        push_cast; linarith
    have := hiter (Nat.ceil (2 * B))
    have hc := Nat.le_ceil (2 * B)
    have := hb (Nat.ceil (2 * B) * (N+1))
    have : b ≤ B := le_max_left _ _
    linarith
  refine FosterQueues.MG1.theorem5_recurrence_criterion P (irred ha hsum P hP)
    (aper ha hsum P hP) (hfun a) (fun i hi => ?_) (fun i hi => ?_) hlim
  · rw [hP]; exact (hfun_harm ha hsum i hi).summable
  · rw [hP, (hfun_harm ha hsum i hi).tsum_eq]

lemma partF {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = gim1Matrix a) (h1 : rhoInv a < 1) :
    ¬ FosterQueues.MG1.IsRecurrent P := by
  intro hrec
  have hne : rhoInv a ≠ ⊤ := ne_top_of_lt h1
  set r := (rhoInv a).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hrr : rhoInv a = ENNReal.ofReal r := (ENNReal.ofReal_toReal hne).symm
  have hr1 : r < 1 := by
    rw [hrr] at h1; exact (ENNReal.ofReal_lt_one).mp h1
  have ha0 := ha 0
  set ε := 1 - r with hε
  have hεpos : 0 < ε := by linarith
  set C := a 0 / ε with hC
  have hCpos : 0 < C := by positivity
  have hbd : ∀ M, ∀ i ≤ M, hfun a i ≤ C := by
    intro M
    induction M with
    | zero => intro i hi; rw [show i = 0 by omega, hfun_zero]; exact hCpos.le
    | succ M ih =>
      intro i hi
      rcases Nat.lt_or_ge i (M+1) with h | h
      · exact ih i (by omega)
      rw [show i = M + 1 by omega]
      have hI := hfun_ident ha M
      have hle : ∑ k ∈ Finset.range M, alpha a (k+1) * hfun a (M - k) ≤
          ∑ k ∈ Finset.range M, alpha a (k+1) * C :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (ih (M - k) (by omega))
          (alpha_pos ha hsum _).le)
      rw [← Finset.sum_mul, sumA hsum M] at hle
      have hS := Sb ha hsum r hr0 hrr.le M
      have hCε : C * ε = a 0 := by rw [hC]; field_simp
      have : a 0 * hfun a (M+1) ≤ a 0 * C := by nlinarith
      exact le_of_mul_le_mul_left this ha0
  have htr : FosterQueues.MG1.IsTransient P := by
    rw [FosterQueues.MG1.theorem4_transience_criterion P (irred ha hsum P hP) (aper ha hsum P hP)]
    refine ⟨hfun a, ⟨C, fun i => ?_⟩, ⟨0, 1, ?_⟩, fun i hi => ?_⟩
    · rw [abs_of_nonneg (hfun_nonneg ha hsum i)]; exact hbd i i le_rfl
    · rw [hfun_zero, hfun_one ha]; norm_num
    · rw [hP]; exact hfun_harm ha hsum i hi
  have := htr 0
  rw [hrec 0] at this
  exact lt_irrefl _ this

end GIM1Aux

open GIM1Aux in
theorem solution (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = FosterQueues.GIM1.gim1Matrix a) :
    (P.PositiveRecurrent ↔ FosterQueues.GIM1.rho a < 1) ∧
      (FosterQueues.MG1.IsRecurrent P ↔ FosterQueues.GIM1.rho a ≤ 1) := by
  unfold FosterQueues.GIM1.rho
  rw [ENNReal.inv_lt_one, ENNReal.inv_le_one]
  constructor
  · constructor
    · intro hpr
      by_contra h
      exact partD ha hsum P hP (not_lt.mp h) hpr
    · exact partC ha hsum P hP
  · constructor
    · intro hrec
      by_contra h
      exact partF ha hsum P hP (not_le.mp h) hrec
    · exact partE ha hsum P hP
