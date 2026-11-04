-- Prove2me | solution 1 for CorruptRobustRL.Supervised.proposition4_2_visitation_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:25:31.51097+00:00
-- url     : https://prove2.me/submissions/43d1185c-d667-475b-8fd8-9e0c9ffe09dd

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

open CorruptRobustRL.Supervised
open Finset QSupervisor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CRRL_P42

variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

theorem snoc_lt {L : Type} {n : ℕ} (s' : Fin n → L) (y : L) (k : ℕ) (hk : k < n)
    (h : k < n + 1) : (Fin.snoc (α := fun _ => L) s' y ⟨k, h⟩ : L) = s' ⟨k, hk⟩ := by
  simp [Fin.snoc, hk, Fin.castLT]

/-- The transition factor appended when a trajectory of length `n` is extended by `y`. -/
noncomputable def kern (M : NominalMDP X A) (σ : DetPolicy X A) (n : ℕ) (s' : Fin n → X) (y : X) : ℝ :=
  if hn : n = 0 then M.p0 y
  else M.pstar (s' ⟨n - 1, by omega⟩) (σ (n - 1) (s' ⟨n - 1, by omega⟩)) y

theorem traj_snoc (M : NominalMDP X A) (σ : DetPolicy X A) (n : ℕ) (s' : Fin n → X) (y : X) :
    trajProb M (n + 1) σ (Fin.snoc (α := fun _ => X) s' y) = trajProb M n σ s' * kern M σ n s' y := by
  unfold trajProb kern
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp only [Fin.val_castSucc, Fin.snoc_castSucc]
    split_ifs with hi
    · rfl
    · rw [snoc_lt s' y ((i : ℕ) - 1) (by omega)]
  · simp only [Fin.val_last, Fin.snoc_last]
    split_ifs with hn
    · rfl
    · rw [snoc_lt s' y (n - 1) (by omega)]

theorem kern_sum (M : NominalMDP X A) (hM : M.IsNominal) (σ : DetPolicy X A) (n : ℕ)
    (s' : Fin n → X) : ∑ y, kern M σ n s' y = 1 := by
  unfold kern
  split_ifs
  · exact hM.1.2
  · exact (hM.2.1 _ _).2

theorem kern_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (σ : DetPolicy X A) (n : ℕ)
    (s' : Fin n → X) (y : X) : 0 ≤ kern M σ n s' y := by
  unfold kern
  split_ifs
  · exact hM.1.1 _
  · exact (hM.2.1 _ _).1 _

theorem trajProb_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (n : ℕ) (σ : DetPolicy X A)
    (s : Fin n → X) : 0 ≤ trajProb M n σ s := by
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact hM.1.1 _
  · exact (hM.2.1 _ _).1 _

theorem sum_snoc {n : ℕ} (F : (Fin (n + 1) → X) → ℝ) :
    ∑ s, F s = ∑ s' : Fin n → X, ∑ y : X, F (Fin.snoc (α := fun _ => X) s' y) := by
  rw [← (Fin.snocEquiv (fun _ => X)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The state distribution at the 0-based stage `t`, as the last marginal of a length-`t+1`
trajectory. -/
noncomputable def dist (M : NominalMDP X A) (σ : DetPolicy X A) (t : ℕ) (x : X) : ℝ :=
  ∑ s : Fin (t + 1) → X, if s (Fin.last t) = x then trajProb M (t + 1) σ s else 0

theorem dist_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (σ : DetPolicy X A) (t : ℕ) (x : X) :
    0 ≤ dist M σ t x :=
  Finset.sum_nonneg fun s _ => by split_ifs; exacts [trajProb_nonneg M hM _ σ s, le_rfl]

theorem sum_last (M : NominalMDP X A) (σ : DetPolicy X A) (n : ℕ) (G : X → ℝ) :
    ∑ s : Fin (n + 1) → X, trajProb M (n + 1) σ s * G (s (Fin.last n)) =
      ∑ x, dist M σ n x * G x := by
  unfold dist
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single (s (Fin.last n))]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
  · intro h; exact absurd (mem_univ _) h

theorem dist_zero (M : NominalMDP X A) (σ : DetPolicy X A) (x : X) : dist M σ 0 x = M.p0 x := by
  unfold dist
  rw [sum_snoc]
  simp only [traj_snoc, Fin.snoc_last]
  rw [Fintype.sum_unique]
  simp [trajProb, kern]

theorem dist_succ (M : NominalMDP X A) (σ : DetPolicy X A) (n : ℕ) (y : X) :
    dist M σ (n + 1) y = ∑ x, dist M σ n x * M.pstar x (σ n x) y := by
  rw [← sum_last M σ n (fun x => M.pstar x (σ n x) y)]
  unfold dist
  rw [sum_snoc]
  apply Finset.sum_congr rfl
  intro s' _
  simp only [Fin.snoc_last, traj_snoc]
  rw [Finset.sum_eq_single y]
  · rw [if_pos rfl]
    unfold kern
    rw [dif_neg (by omega)]
    simp only [mul_one, add_tsub_cancel_right]
    rfl
  · intro b _ hb; rw [if_neg hb]
  · intro h; exact absurd (mem_univ _) h

theorem marg (M : NominalMDP X A) (hM : M.IsNominal) (σ : DetPolicy X A) (n : ℕ)
    (F : (Fin n → X) → ℝ) :
    ∑ s : Fin (n + 1) → X, trajProb M (n + 1) σ s * F (Fin.init s) =
      ∑ s' : Fin n → X, trajProb M n σ s' * F s' := by
  rw [sum_snoc]
  apply Finset.sum_congr rfl
  intro s' _
  simp only [traj_snoc, Fin.init_snoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum, kern_sum M hM, mul_one]

theorem expect_eq (M : NominalMDP X A) (hM : M.IsNominal) (σ : DetPolicy X A)
    (g : ℕ → X → A → ℝ) : ∀ n, expectDet M n σ g =
      ∑ t ∈ range n, ∑ x, dist M σ t x * g t x (σ t x) := by
  intro n
  induction n with
  | zero => simp [expectDet]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, ← sum_last M σ n (fun x => g n x (σ n x))]
    unfold expectDet
    simp only [Fin.sum_univ_castSucc, mul_add, Finset.sum_add_distrib, Fin.val_last,
      Fin.val_castSucc]
    congr 1
    exact marg M hM σ n (fun s' => ∑ i : Fin n, g i (s' i) (σ i (s' i)))

theorem dist_congr (M : NominalMDP X A) (σ σ' : DetPolicy X A) (t : ℕ)
    (h : ∀ u < t, ∀ x, σ u x = σ' u x) (x : X) : dist M σ t x = dist M σ' t x := by
  unfold dist trajProb
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · rw [h _ (by have := i.isLt; omega)]

theorem Vstar_eq_sup (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) :
    Vstar M H h x = univ.sup' univ_nonempty (Qstar M H h x) := by
  unfold Vstar Qstar
  rw [show H - h = (H - (h + 1)) + 1 by omega, VstarRem]
  rfl

theorem Qstar_le_Vstar (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) (a : A) :
    Qstar M H h x a ≤ Vstar M H h x := by
  rw [Vstar_eq_sup M H h hh x]; exact Finset.le_sup' _ (mem_univ a)

theorem exists_opt (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) :
    ∃ a, a ∈ optActions M H h x := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (Qstar M H h x)
  refine ⟨a, ?_⟩
  unfold optActions
  simp only [Finset.mem_filter, mem_univ, true_and]
  rw [Vstar_eq_sup M H h hh x, ha]

theorem mem_opt (M : NominalMDP X A) (H h : ℕ) (x : X) (a : A) (ha : a ∈ optActions M H h x) :
    Qstar M H h x a = Vstar M H h x := by
  unfold optActions at ha
  simpa using ha


theorem tele (M : NominalMDP X A) (σ : DetPolicy X A) (H : ℕ) (f : ℕ → X → ℝ)
    (hf : ∀ x, f H x = 0) :
    ∀ k τ0, τ0 + k = H → ∑ x, dist M σ τ0 x * f τ0 x =
      ∑ t ∈ Ico τ0 H, ∑ x, dist M σ t x * (f t x - ∑ y, M.pstar x (σ t x) y * f (t + 1) y) := by
  intro k
  induction k with
  | zero =>
    intro τ0 h
    have : τ0 = H := by omega
    subst this
    simp [hf]
  | succ k ih =>
    intro τ0 h
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), ← ih (τ0 + 1) (by omega)]
    have e : ∑ x, dist M σ (τ0 + 1) x * f (τ0 + 1) x =
        ∑ x, dist M σ τ0 x * ∑ y, M.pstar x (σ τ0 x) y * f (τ0 + 1) y := by
      simp only [dist_succ, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem psum_sub (M : NominalMDP X A) (x : X) (a : A) (V W : X → ℝ) :
    ∑ y, M.pstar x a y * (V y - W y) = ∑ y, M.pstar x a y * V y - ∑ y, M.pstar x a y * W y := by
  rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun y _ => by ring

theorem Vlow_le_of_plaus (H : ℕ) (T : QSupervisor X A) (h : ℕ) (hh : h < H) (x : X) (a : A)
    (ha : a ∈ plaus T h x) : Vlow H T h x ≤ T.Qbar h x a := by
  simp only [plaus, Finset.mem_filter] at ha
  unfold Vlow
  rw [if_pos hh, dif_pos ⟨a, ha.1⟩]
  exact Finset.sup'_le _ _ fun a' ha' => ha.2 a' ha'

theorem Qlow_le_Vlow (H : ℕ) (T : QSupervisor X A) (h : ℕ) (hh : h < H) (x : X) (a : A)
    (ha : a ∈ T.act h x) : T.Qlow h x a ≤ Vlow H T h x := by
  unfold Vlow
  rw [if_pos hh, dif_pos ⟨a, ha⟩]
  exact Finset.le_sup' (T.Qlow h x) ha

theorem Vstar_le_Vbar0 (M : NominalMDP X A) (H : ℕ) (hH : 1 ≤ H) (T : QSupervisor X A)
    (hT : T.IsQSupervisor H) (hadm : IsAdmissible M H T) (x : X) :
    Vstar M H 0 x ≤ Vbar H T 0 x := by
  obtain ⟨a0, ha0⟩ := exists_opt M H 0 (by omega) x
  obtain ⟨hsub, hQ⟩ := hadm 0 (by omega) x
  unfold Vbar
  rw [if_pos (by omega)]
  calc Vstar M H 0 x = Qstar M H 0 x a0 := (mem_opt M H 0 x a0 ha0).symm
    _ ≤ T.Qbar 0 x a0 := (hQ a0).2
    _ ≤ _ := (hT.2 0 (by omega) x).2 a0 (hsub ha0)

theorem gap_bound (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (T : QSupervisor X A)
    (hT : T.IsQSupervisor H) (σ : DetPolicy X A) (t : ℕ) (ht : t < H) :
    ∑ x, dist M σ t x * (Vbar H T t x - Vlow H T t x) ≤
      expectDet M H (concat σ t T.ucb)
        (fun τ x a => if t ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0) := by
  set σ' := concat σ t T.ucb
  have hd : ∀ x, dist M σ t x = dist M σ' t x := fun x =>
    dist_congr M σ σ' t (fun u hu y => by simp [σ', concat, hu]) x
  simp only [hd]
  rw [tele M σ' H (fun u x => Vbar H T u x - Vlow H T u x) (fun x => by simp [Vbar, Vlow])
    (H - t) t (by omega)]
  rw [expect_eq M hM σ', ← Finset.sum_range_add_sum_Ico _ ht.le]
  have h0 : ∑ u ∈ range t, ∑ x, dist M σ' u x * (if t ≤ u then upperBell M H T u x (σ' u x) -
      lowerBell M H T u x (σ' u x) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro u hu
    rw [Finset.mem_range] at hu
    simp [show ¬ t ≤ u by omega]
  rw [h0, zero_add]
  apply Finset.sum_le_sum
  intro u hu
  rw [Finset.mem_Ico] at hu
  apply Finset.sum_le_sum
  intro x _
  rw [if_pos hu.1]
  apply mul_le_mul_of_nonneg_left _ (dist_nonneg M hM σ' u x)
  have hs : σ' u x = T.ucb u x := by simp [σ', concat, show ¬ u < t by omega]
  rw [hs, psum_sub]
  have h1 : Vbar H T u x = T.Qbar u x (T.ucb u x) := by simp [Vbar, hu.2]
  have h2 := Qlow_le_Vlow H T u hu.2 x (T.ucb u x) ((hT.2 u hu.2 x).1)
  unfold upperBell lowerBell
  linarith

/-- Proposition 4.1 for a deterministic Markov policy. -/
theorem det_bound (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (T : QSupervisor X A) (hT : T.IsQSupervisor H) (hadm : IsAdmissible M H T)
    (σ : DetPolicy X A) (hsup : ∀ h < H, ∀ x, σ h x ∈ plaus T h x) :
    Vstar0 M H - value M H σ ≤
      expectDet M H σ (upperBell M H T) +
        ∑ h ∈ range H, expectDet M H (concat σ h T.ucb)
          (fun τ x a => if h ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0) := by
  have h1 : Vstar0 M H ≤ ∑ x, M.p0 x * Vbar H T 0 x :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
      (Vstar_le_Vbar0 M H hH T hT hadm x) (hM.1.1 x)
  have h2 : ∑ x, M.p0 x * Vbar H T 0 x = ∑ t ∈ range H, ∑ x, dist M σ t x *
      (Vbar H T t x - ∑ y, M.pstar x (σ t x) y * Vbar H T (t + 1) y) := by
    rw [Finset.range_eq_Ico, ← tele M σ H (Vbar H T) (fun x => by simp [Vbar]) H 0 (by omega)]
    simp only [dist_zero]
  have h3 : ∑ t ∈ range H, ∑ x, dist M σ t x *
      (Vbar H T t x - ∑ y, M.pstar x (σ t x) y * Vbar H T (t + 1) y) ≤
      ∑ t ∈ range H, (∑ x, dist M σ t x * M.rstar x (σ t x) +
        ∑ x, dist M σ t x * upperBell M H T t x (σ t x) +
        ∑ x, dist M σ t x * (Vbar H T t x - Vlow H T t x)) := by
    apply Finset.sum_le_sum; intro t ht
    rw [Finset.mem_range] at ht
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro x _
    rw [← mul_add, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (dist_nonneg M hM σ t x)
    have := Vlow_le_of_plaus H T t ht x (σ t x) (hsup t ht x)
    unfold upperBell
    linarith
  have h4 : ∀ t ∈ range H, ∑ x, dist M σ t x * (Vbar H T t x - Vlow H T t x) ≤
      expectDet M H (concat σ t T.ucb)
        (fun τ x a => if t ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0) :=
    fun t ht => gap_bound M hM H T hT σ t (Finset.mem_range.mp ht)
  have hv : value M H σ = ∑ t ∈ range H, ∑ x, dist M σ t x * M.rstar x (σ t x) :=
    expect_eq M hM σ _ H
  have he : expectDet M H σ (upperBell M H T) =
      ∑ t ∈ range H, ∑ x, dist M σ t x * upperBell M H T t x (σ t x) :=
    expect_eq M hM σ _ H
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h3
  have h5 := Finset.sum_le_sum h4
  rw [hv, he]
  linarith

theorem prop41
    (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (T : QSupervisor X A) (hT : T.IsQSupervisor H) (hadm : IsAdmissible M H T)
    (π : Mixture X A) (hπ : π.IsMixture) (hsup : IsQSupervised H π T) :
    Vstar0 M H - mixValue M H π ≤
      mixExpect M H π (upperBell M H T) +
        ∑ h ∈ range H, mixExpect M H (concatMix π h T.ucb)
          (fun τ x a => if h ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0) := by
  have e1 : Vstar0 M H - mixValue M H π = ∑ i, π.w i * (Vstar0 M H - value M H (π.σ i)) := by
    unfold mixValue
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2, one_mul]
  have e2 : mixExpect M H π (upperBell M H T) +
      ∑ h ∈ range H, mixExpect M H (concatMix π h T.ucb)
        (fun τ x a => if h ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0) =
      ∑ i, π.w i * (expectDet M H (π.σ i) (upperBell M H T) +
        ∑ h ∈ range H, expectDet M H (concat (π.σ i) h T.ucb)
          (fun τ x a => if h ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0)) := by
    have hc : ∀ h (g : ℕ → X → A → ℝ), mixExpect M H (concatMix π h T.ucb) g =
        ∑ i : π.ι, π.w i * expectDet M H (concat (π.σ i) h T.ucb) g := fun h g => rfl
    simp only [hc]
    unfold mixExpect
    simp only [mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm
  rw [e1, e2]
  apply Finset.sum_le_sum
  intro i _
  rcases eq_or_lt_of_le (hπ.1 i) with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left
      (det_bound M hM H hH T hT hadm (π.σ i) (fun h hh x => hsup i hpos h hh x)) hpos.le

theorem pick2 {S : Type} [Fintype S] (u : X) (v : X → A) (c : X → A → ℝ) :
    ∑ x, ∑ a, (if u = x ∧ v x = a then c x a else 0) = c u (v u) := by
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single (v u)]
    · simp
    · intro b _ hb; rw [if_neg]; rintro ⟨-, h⟩; exact hb h.symm
    · intro h; exact absurd (mem_univ _) h
  · intro b _ hb
    apply Finset.sum_eq_zero; intro a _
    rw [if_neg]; rintro ⟨h, -⟩; exact hb h.symm
  · intro h; exact absurd (mem_univ _) h

theorem occ_identity (M : NominalMDP X A) (H : ℕ) (σ : DetPolicy X A) (g : ℕ → X → A → ℝ) :
    expectDet M H σ g = ∑ τ ∈ range H, ∑ x, ∑ a, occ M H σ τ x a * g τ x a := by
  have per : ∀ τ (hτ : τ < H), ∑ x, ∑ a, occ M H σ τ x a * g τ x a =
      ∑ s : Fin H → X, trajProb M H σ s * g τ (s ⟨τ, hτ⟩) (σ τ (s ⟨τ, hτ⟩)) := by
    intro τ hτ
    unfold occ
    simp only [dif_pos hτ, Finset.sum_mul, ite_mul, zero_mul]
    have e : ∀ x : X, ∑ a : A, ∑ s : Fin H → X,
        (if s ⟨τ, hτ⟩ = x ∧ σ τ x = a then trajProb M H σ s * g τ x a else 0) =
        ∑ s : Fin H → X, ∑ a : A,
        (if s ⟨τ, hτ⟩ = x ∧ σ τ x = a then trajProb M H σ s * g τ x a else 0) :=
      fun x => Finset.sum_comm
    simp only [e]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    exact pick2 (S := Unit) (s ⟨τ, hτ⟩) (σ τ) (fun x a => trajProb M H σ s * g τ x a)
  rw [← Fin.sum_univ_eq_sum_range (fun τ => ∑ x, ∑ a, occ M H σ τ x a * g τ x a) H]
  simp only [per _ (Fin.isLt _)]
  unfold expectDet
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem occ_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (σ : DetPolicy X A)
    (τ : ℕ) (x : X) (a : A) : 0 ≤ occ M H σ τ x a := by
  unfold occ
  split_ifs
  · exact Finset.sum_nonneg fun s _ => by split_ifs; exacts [trajProb_nonneg M hM _ σ s, le_rfl]
  · exact le_rfl

theorem mix_occ_identity (M : NominalMDP X A) (H : ℕ) (π : Mixture X A) (g : ℕ → X → A → ℝ) :
    mixExpect M H π g = ∑ τ ∈ range H, ∑ x, ∑ a, mixOcc M H π τ x a * g τ x a := by
  unfold mixExpect mixOcc
  simp only [occ_identity, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro τ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem mixExpect_mono (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (π : Mixture X A)
    (hw : ∀ i, 0 ≤ π.w i) (g g' : ℕ → X → A → ℝ) (hg : ∀ t < H, ∀ x a, g t x a ≤ g' t x a) :
    mixExpect M H π g ≤ mixExpect M H π g' := by
  apply Finset.sum_le_sum; intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply Finset.sum_le_sum; intro s _
  apply mul_le_mul_of_nonneg_left _ (trajProb_nonneg M hM H _ s)
  exact Finset.sum_le_sum fun t _ => hg t t.isLt _ _

end CRRL_P42

open CRRL_P42 in
theorem solution
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (T : QSupervisor X A) (hT : T.IsQSupervisor H) (hadm : IsAdmissible M H T)
    (π : Mixture X A) (hπ : π.IsMixture) (hsup : IsQSupervised H π T)
    (ρ : ℝ) (hρ : HasVisitRatio M H π T.ucb ρ) :
    Vstar0 M H - mixValue M H π ≤
      ρ * (1 + H) * mixExpect M H π
        (fun h x a => max 0 (max (upperBell M H T h x a)
          (upperBell M H T h x a - lowerBell M H T h x a))) := by
  set G : ℕ → X → A → ℝ := fun h x a => max 0 (max (upperBell M H T h x a)
          (upperBell M H T h x a - lowerBell M H T h x a)) with hG
  have hG0 : ∀ h x a, 0 ≤ G h x a := fun h x a => le_max_left _ _
  have h41 := prop41 M hM H hH T hT hadm π hπ hsup
  have hρ1 : 1 ≤ ρ := hρ.1
  have hocc0 : ∀ τ x a, 0 ≤ mixOcc M H π τ x a := fun τ x a =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hπ.1 i) (occ_nonneg M hM H _ τ x a)
  have hEG : 0 ≤ mixExpect M H π G := by
    rw [mix_occ_identity]
    exact Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun x _ =>
      Finset.sum_nonneg fun a _ => mul_nonneg (hocc0 τ x a) (hG0 τ x a)
  have hA : mixExpect M H π (upperBell M H T) ≤ mixExpect M H π G :=
    mixExpect_mono M hM H π hπ.1 _ _ fun t _ x a =>
      le_trans (le_max_left _ _) (le_max_right _ _)
  have hB : ∀ h ∈ range H, mixExpect M H (concatMix π h T.ucb)
      (fun τ x a => if h ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0) ≤
      ρ * mixExpect M H π G := by
    intro h _
    have hw : ∀ i, 0 ≤ (concatMix π h T.ucb).w i := hπ.1
    refine le_trans (mixExpect_mono M hM H (concatMix π h T.ucb) hw _
      (fun τ x a => if h ≤ τ then G τ x a else 0) ?_) ?_
    · intro t _ x a
      split_ifs
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
      · exact le_rfl
    · rw [mix_occ_identity, mix_occ_identity, Finset.mul_sum]
      apply Finset.sum_le_sum; intro τ hτ
      rw [Finset.mem_range] at hτ
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro a _
      split_ifs with hhτ
      · have := hρ.2 h τ x a hhτ hτ
        calc mixOcc M H (concatMix π h T.ucb) τ x a * G τ x a ≤
            (ρ * mixOcc M H π τ x a) * G τ x a := mul_le_mul_of_nonneg_right this (hG0 τ x a)
          _ = _ := by ring
      · rw [mul_zero]
        exact mul_nonneg (by linarith) (mul_nonneg (hocc0 τ x a) (hG0 τ x a))
  have hBs := Finset.sum_le_sum hB
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hBs
  have : mixExpect M H π G ≤ ρ * mixExpect M H π G := le_mul_of_one_le_left hEG hρ1
  calc Vstar0 M H - mixValue M H π ≤ _ := h41
    _ ≤ mixExpect M H π G + (H : ℝ) * (ρ * mixExpect M H π G) := add_le_add hA hBs
    _ ≤ ρ * mixExpect M H π G + (H : ℝ) * (ρ * mixExpect M H π G) := by linarith
    _ = ρ * (1 + H) * mixExpect M H π G := by ring
