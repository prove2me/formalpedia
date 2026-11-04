-- Prove2me | solution 1 for CorruptRobustRL.Supervised.lemma4_4_value_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:08:18.770983+00:00
-- url     : https://prove2.me/submissions/6e998b74-4245-4f4d-ba6c-6302a646e024

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

open CorruptRobustRL.Supervised
open Finset

namespace CRRL_L44

/-- Geometric tail: `Σ_{m ∈ (f, L]} 2^{-(m-f)} ≤ 1`. -/
theorem geom_tail (f L : ℕ) : ∑ m ∈ Ioc f L, (2 : ℝ)⁻¹ ^ (m - f) ≤ 1 := by
  rcases le_or_gt f L with hfL | hfL
  · have key : ∀ L, f ≤ L → ∑ m ∈ Ioc f L, (2 : ℝ)⁻¹ ^ (m - f) = 1 - (2 : ℝ)⁻¹ ^ (L - f) := by
      intro L hL
      induction L, hL using Nat.le_induction with
      | base => simp
      | succ L hL ih =>
        rw [Finset.sum_Ioc_succ_top hL, ih, show L + 1 - f = (L - f) + 1 by omega, pow_succ]
        ring
    rw [key L hfL]
    have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (L - f) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]; simp

theorem stepProb_nonneg (H ℓmax f n : ℕ) : 0 ≤ stepProb H ℓmax f n := by
  unfold stepProb
  split_ifs with h1 h2
  · positivity
  · have hle : ∑ m ∈ Ioc f ℓmax, 1 / (2 * (m : ℝ) * H) * (2 : ℝ)⁻¹ ^ (m - f) ≤
        ∑ m ∈ Ioc f ℓmax, (2 : ℝ)⁻¹ ^ (m - f) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm1 : (1 : ℝ) ≤ m := by
        have := (Finset.mem_Ioc.mp hm).1; exact_mod_cast (show 1 ≤ m by omega)
      have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (m - f) := by positivity
      have hc : 1 / (2 * (m : ℝ) * H) ≤ 1 := by
        rcases Nat.eq_zero_or_pos H with hH | hH
        · subst hH; simp
        · have : (1 : ℝ) ≤ H := by exact_mod_cast hH
          rw [div_le_one (by positivity)]; nlinarith
      calc 1 / (2 * (m : ℝ) * H) * (2 : ℝ)⁻¹ ^ (m - f) ≤ 1 * (2 : ℝ)⁻¹ ^ (m - f) :=
            mul_le_mul_of_nonneg_right hc hp
        _ = _ := one_mul _
    have := geom_tail f ℓmax
    linarith
  · exact le_rfl

/-- `Σ_{y ∈ [ℓmax]} P[D_f = y] = 1` for `f ∈ [ℓmax]`. -/
theorem stepProb_sum (H ℓmax f : ℕ) (hf : 1 ≤ f) (hfm : f ≤ ℓmax) :
    ∑ y : Fin ℓmax, stepProb H ℓmax f ((y : ℕ) + 1) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => stepProb H ℓmax f (i + 1)) ℓmax]
  have e : ∑ i ∈ range ℓmax, stepProb H ℓmax f (i + 1) = ∑ n ∈ Ioc 0 ℓmax, stepProb H ℓmax f n := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n => stepProb H ℓmax f n), zero_add,
      show Ico (0 + 1) (ℓmax + 1) = Ioc 0 ℓmax by ext; simp; omega]
  rw [e, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le f) hfm]
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le f')]
  have h0 : ∑ n ∈ Ioc 0 f', stepProb H ℓmax (f' + 1) n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have := (Finset.mem_Ioc.mp hn)
    unfold stepProb
    rw [if_neg (by omega), if_neg (by omega)]
  have h1 : ∑ n ∈ Ioc (f' + 1) ℓmax, stepProb H ℓmax (f' + 1) n =
      ∑ m ∈ Ioc (f' + 1) ℓmax, 1 / (2 * (m : ℝ) * H) * (2 : ℝ)⁻¹ ^ (m - (f' + 1)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have := (Finset.mem_Ioc.mp hn)
    unfold stepProb
    rw [if_pos (by omega)]
  have h2 : stepProb H ℓmax (f' + 1) (f' + 1) =
      1 - ∑ m ∈ Ioc (f' + 1) ℓmax, 1 / (2 * (m : ℝ) * H) * (2 : ℝ)⁻¹ ^ (m - (f' + 1)) := by
    unfold stepProb
    rw [if_neg (by omega), if_pos rfl]
  rw [h0, h1, h2]; ring

/-- Weight of a schedule of length `n` started from layer `f`. -/
noncomputable def Wt (H L f n : ℕ) (s : Fin n → Fin L) : ℝ :=
  ∏ t : Fin n,
    stepProb H L
      (if (t : ℕ) = 0 then f
        else ((s ⟨(t : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ : Fin L) : ℕ) + 1)
      ((s t : ℕ) + 1)

theorem snoc_lt {L n : ℕ} (s' : Fin n → Fin L) (y : Fin L) (k : ℕ) (hk : k < n)
    (h : k < n + 1) : (Fin.snoc (α := fun _ => Fin L) s' y ⟨k, h⟩ : Fin L) = s' ⟨k, hk⟩ := by
  simp [Fin.snoc, hk, Fin.castLT]

theorem snoc_n {L n : ℕ} (s' : Fin n → Fin L) (y : Fin L)
    (h : n < n + 1) : (Fin.snoc (α := fun _ => Fin L) s' y ⟨n, h⟩ : Fin L) = y := by
  simp [Fin.snoc]

theorem Wt_snoc (H L f n : ℕ) (s' : Fin n → Fin L) (y : Fin L) :
    Wt H L f (n + 1) (Fin.snoc (α := fun _ => Fin L) s' y) =
      Wt H L f n s' * stepProb H L
        (if hn : n = 0 then f else
          ((s' ⟨n - 1, by omega⟩ : Fin L) : ℕ) + 1) ((y : ℕ) + 1) := by
  unfold Wt
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc]
    split_ifs with hi
    · rfl
    · rw [snoc_lt s' y ((i : ℕ) - 1) (by omega)]
  · simp only [Fin.val_last, Fin.snoc_last]
    split_ifs with hn
    · rfl
    · rw [snoc_lt s' y (n - 1) (by omega)]

theorem Wt_sum (H L f : ℕ) (hf : 1 ≤ f) (hfL : f ≤ L) : ∀ n, ∑ s, Wt H L f n s = 1 := by
  intro n
  induction n with
  | zero => simp [Wt]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ => Fin L)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    change ∑ s' : Fin n → Fin L, ∑ y : Fin L, Wt H L f (n + 1) (Fin.snoc (α := fun _ => Fin L) s' y) = 1
    simp only [Wt_snoc]
    rw [← ih]
    apply Finset.sum_congr rfl
    intro s' _
    rw [← Finset.mul_sum, stepProb_sum, mul_one]
    · split_ifs with hn
      · exact hf
      · omega
    · split_ifs with hn
      · exact hfL
      · have := (s' ⟨n - 1, by omega⟩).isLt; omega

theorem schedWeight_eq (H ℓmax : ℕ) (s : Sched H ℓmax) : schedWeight s = Wt H ℓmax 1 H s := rfl

theorem schedWeight_nonneg (H ℓmax : ℕ) (s : Sched H ℓmax) : 0 ≤ schedWeight s :=
  Finset.prod_nonneg fun t _ => stepProb_nonneg _ _ _ _

theorem schedWeight_sum (H ℓmax : ℕ) (hℓ : 1 ≤ ℓmax) : ∑ s : Sched H ℓmax, schedWeight s = 1 := by
  simp only [schedWeight_eq]; exact Wt_sum H ℓmax 1 le_rfl hℓ H

theorem last_le (H ℓmax : ℕ) (hH : 1 ≤ H) (s : Sched H ℓmax) : s.last ≤ ℓmax := by
  unfold Sched.last Sched.lay
  rw [dif_pos (by omega)]
  have := (s ⟨H - 1, by omega⟩).isLt
  omega

theorem cond_mix {S : Type} [Fintype S] (P : S → Prop) [DecidablePred P] (w v : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (c : ℝ) :
    (∑ s, if P s then w s else 0) *
        (c - ∑ s, (if P s then w s / (∑ s', if P s' then w s' else 0) else 0) * v s) =
      ∑ s, (if P s then w s else 0) * (c - v s) := by
  set Q := ∑ s', if P s' then w s' else 0 with hQ
  by_cases h0 : Q = 0
  · have hz : ∀ s, (if P s then w s else 0) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (s := univ)
        (f := fun s => if P s then w s else 0)
        (fun s _ => by split_ifs; exacts [hw s, le_rfl])).mp h0.symm.symm
      exact fun s => this s (mem_univ s)
    rw [h0, zero_mul]
    symm
    exact Finset.sum_eq_zero fun s _ => by rw [hz s, zero_mul]
  · rw [mul_sub, Finset.mul_sum]
    have e1 : ∀ s, Q * ((if P s then w s / Q else 0) * v s) = (if P s then w s else 0) * v s := by
      intro s; split_ifs
      · field_simp
      · simp
    simp only [e1]
    rw [hQ, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring

end CRRL_L44

open CRRL_L44 in
theorem solution
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (base : ℕ → DetPolicy X A) (lst : ℕ) (hlst : 1 ≤ lst) (hlstmax : lst ≤ ℓmax) :
    Vstar0 M H - mixValue M H (master H ℓmax base) =
      qLe H ℓmax lst * (Vstar0 M H - mixValue M H (masterLe H ℓmax base lst)) +
        ∑ ℓ ∈ Ioc lst ℓmax, q H ℓmax ℓ * (Vstar0 M H - mixValue M H (masterEq H ℓmax base ℓ)) := by
  set c := Vstar0 M H
  set v : Sched H ℓmax → ℝ := fun s => value M H (schedPolicy base s)
  have hm : mixValue M H (master H ℓmax base) = ∑ s, schedWeight s * v s := rfl
  have hle : qLe H ℓmax lst * (c - mixValue M H (masterLe H ℓmax base lst)) =
      ∑ s, (if s.last ≤ lst then schedWeight s else 0) * (c - v s) :=
    cond_mix (fun s : Sched H ℓmax => s.last ≤ lst) schedWeight v (schedWeight_nonneg H ℓmax) c
  have heq : ∀ ℓ, q H ℓmax ℓ * (c - mixValue M H (masterEq H ℓmax base ℓ)) =
      ∑ s, (if s.last = ℓ then schedWeight s else 0) * (c - v s) := fun ℓ =>
    cond_mix (fun s : Sched H ℓmax => s.last = ℓ) schedWeight v (schedWeight_nonneg H ℓmax) c
  rw [hle, Finset.sum_congr rfl (fun ℓ _ => heq ℓ), Finset.sum_comm, ← Finset.sum_add_distrib, hm]
  have h1 : c - ∑ s, schedWeight s * v s = ∑ s, schedWeight s * (c - v s) := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, schedWeight_sum H ℓmax (by omega), one_mul]
  rw [h1]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_mul, Finset.sum_ite_eq]
  have := last_le H ℓmax hH s
  by_cases h2 : s.last ≤ lst
  · rw [if_pos h2, if_neg (by rw [Finset.mem_Ioc]; omega)]; ring
  · rw [if_neg h2, if_pos (by rw [Finset.mem_Ioc]; omega)]; ring
