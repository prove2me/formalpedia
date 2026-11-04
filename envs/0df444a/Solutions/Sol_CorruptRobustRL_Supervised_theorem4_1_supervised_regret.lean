-- Prove2me | solution 1 for CorruptRobustRL.Supervised.theorem4_1_supervised_regret
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:12:47.121367+00:00
-- url     : https://prove2.me/submissions/2a14d20d-4577-4368-b1a3-46c18ea72371

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm
import Theorems.Thm_CorruptRobustRL_Supervised_lemma4_4_value_decomposition
import Theorems.Thm_CorruptRobustRL_Supervised_lemma4_5_q_supervision
import Theorems.Thm_CorruptRobustRL_Supervised_lemma4_6_admissible_of_valid
import Theorems.Thm_CorruptRobustRL_Supervised_proposition4_2_visitation_ratio_bound
import Theorems.Thm_CorruptRobustRL_Supervised_lemma4_7_bellman_error_bound
import Theorems.Thm_CorruptRobustRL_Supervised_lemma4_10_visitation_ratios

open CorruptRobustRL.Supervised
open Finset QSupervisor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CRRL_T41

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

section Gen
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

theorem backup_nonneg (H : ℕ) (m : ModelEst X A) (hm : m.IsModelEst H) (V : X → ℝ)
    (hV : ∀ x, 0 ≤ V x) (x : X) (a : A) : 0 ≤ backup m V x a := by
  obtain ⟨⟨hr, -⟩, ⟨hp, -⟩, -⟩ := hm x a
  unfold backup
  exact add_nonneg hr (Finset.sum_nonneg fun y _ => mul_nonneg (hp y) (hV y))

theorem backup_le (H : ℕ) (m : ModelEst X A) (hm : m.IsModelEst H) (V : X → ℝ) (c : ℝ)
    (hV : ∀ x, V x ≤ c) (x : X) (a : A) : backup m V x a ≤ 1 + c := by
  obtain ⟨⟨-, hr⟩, ⟨hp, hp1⟩, -⟩ := hm x a
  unfold backup
  have : ∑ x', m.p x a x' * V x' ≤ ∑ x', m.p x a x' * c :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hV y) (hp y)
  rw [← Finset.sum_mul, hp1, one_mul] at this
  linarith

theorem vals_bounds (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A)
    (sel : Selector A) (hgl : gl.IsModelEst H) (hsb : sb.IsModelEst H) :
    ∀ n x, (0 ≤ (ucbviVals H act gl sb sel n).1 x ∧ (ucbviVals H act gl sb sel n).1 x ≤ H) ∧
      (0 ≤ (ucbviVals H act gl sb sel n).2 x ∧ (ucbviVals H act gl sb sel n).2 x ≤ n) := by
  intro n
  induction n with
  | zero => intro x; simp [ucbviVals]
  | succ n ih =>
    intro x
    simp only [ucbviVals]
    refine ⟨⟨?_, min_le_left _ _⟩, ?_⟩
    · apply le_min (Nat.cast_nonneg _)
      apply le_min
      · exact add_nonneg (backup_nonneg H gl hgl _ (fun y => (ih y).1.1) _ _)
          ((hgl x _).2.2.1)
      · exact add_nonneg (backup_nonneg H sb hsb _ (fun y => (ih y).1.1) _ _)
          ((hsb x _).2.2.1)
    · have hq : ∀ a, 0 ≤ qLow gl sb (ucbviVals H act gl sb sel n).2 x a ∧
          qLow gl sb (ucbviVals H act gl sb sel n).2 x a ≤ (n + 1 : ℕ) := by
        intro a
        refine ⟨le_max_left _ _, max_le (by positivity) (max_le ?_ ?_)⟩
        · have h1 := backup_le H gl hgl _ (n : ℝ) (fun y => (ih y).2.2) x a
          have h2 := (hgl x a).2.2.1
          push_cast; linarith
        · have h1 := backup_le H sb hsb _ (n : ℝ) (fun y => (ih y).2.2) x a
          have h2 := (hsb x a).2.2.1
          push_cast; linarith
      unfold CorruptRobustRL.Supervised.maxOn
      split_ifs with hne
      · obtain ⟨a0, ha0⟩ := hne
        exact ⟨le_trans (hq a0).1 (Finset.le_sup' _ ha0),
          Finset.sup'_le _ _ fun a _ => (hq a).2⟩
      · exact ⟨le_rfl, by positivity⟩


theorem stepProb_diag_pos (H ℓmax f : ℕ) (hH : 1 ≤ H) : 0 < stepProb H ℓmax f f := by
  unfold stepProb
  rw [if_neg (by omega), if_pos rfl]
  have hle : ∑ m ∈ Ioc f ℓmax, 1 / (2 * (m : ℝ) * H) * (2 : ℝ)⁻¹ ^ (m - f) ≤
      ∑ m ∈ Ioc f ℓmax, (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ (m - f) := by
    apply Finset.sum_le_sum; intro m hm
    have hm1 : (1 : ℝ) ≤ m := by
      have := (Finset.mem_Ioc.mp hm).1; exact_mod_cast (show 1 ≤ m by omega)
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hc : 1 / (2 * (m : ℝ) * H) ≤ 2⁻¹ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  rw [← Finset.mul_sum] at hle
  have h2 := mul_le_of_le_one_right (show (0 : ℝ) ≤ 2⁻¹ by norm_num) (geom_tail f ℓmax)
  linarith

theorem stepProb_up_pos (H ℓmax f n : ℕ) (hH : 1 ≤ H) (h1 : f < n) (h2 : n ≤ ℓmax) :
    0 < stepProb H ℓmax f n := by
  unfold stepProb
  rw [if_pos ⟨h1, h2⟩]
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  exact mul_pos (div_pos one_pos (mul_pos (mul_pos two_pos hn) hH0)) (by positivity)

def constSched (H ℓmax ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ ℓmax) : Sched H ℓmax :=
  fun _ => ⟨ℓ - 1, by omega⟩

theorem constSched_last (H ℓmax ℓ : ℕ) (hH : 1 ≤ H) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ ℓmax) :
    (constSched H ℓmax ℓ h1 h2).last = ℓ := by
  unfold Sched.last Sched.lay constSched
  rw [dif_pos (by omega)]
  simp only; omega

theorem constSched_pos (H ℓmax ℓ : ℕ) (hH : 1 ≤ H) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ ℓmax) :
    0 < schedWeight (constSched H ℓmax ℓ h1 h2) := by
  apply Finset.prod_pos
  intro t _
  simp only [Sched.lay, constSched]
  rw [show ℓ - 1 + 1 = ℓ by omega]
  split_ifs with ht
  · rcases eq_or_lt_of_le h1 with h | h
    · subst h; exact stepProb_diag_pos H ℓmax 1 hH
    · exact stepProb_up_pos H ℓmax 1 ℓ hH h h2
  · exact stepProb_diag_pos H ℓmax ℓ hH

theorem q_pos (H ℓmax ℓ : ℕ) (hH : 1 ≤ H) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ ℓmax) : 0 < q H ℓmax ℓ := by
  have := Finset.single_le_sum (f := fun s : Sched H ℓmax => if s.last = ℓ then schedWeight s else 0)
    (fun s _ => by split_ifs; exacts [schedWeight_nonneg H ℓmax s, le_rfl])
    (mem_univ (constSched H ℓmax ℓ h1 h2))
  simp only [constSched_last H ℓmax ℓ hH h1 h2, if_true] at this
  exact lt_of_lt_of_le (constSched_pos H ℓmax ℓ hH h1 h2) this

theorem qLe_pos (H ℓmax ℓ : ℕ) (hH : 1 ≤ H) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ ℓmax) : 0 < qLe H ℓmax ℓ := by
  have := Finset.single_le_sum (f := fun s : Sched H ℓmax => if s.last ≤ ℓ then schedWeight s else 0)
    (fun s _ => by split_ifs; exacts [schedWeight_nonneg H ℓmax s, le_rfl])
    (mem_univ (constSched H ℓmax 1 le_rfl (le_trans h1 h2)))
  simp only [constSched_last H ℓmax 1 hH le_rfl (le_trans h1 h2), if_pos h1] at this
  exact lt_of_lt_of_le (constSched_pos H ℓmax 1 hH le_rfl (le_trans h1 h2)) this

theorem masterEq_mix (H ℓmax : ℕ) (base : ℕ → DetPolicy X A) (ℓ : ℕ) (hq : 0 < q H ℓmax ℓ) :
    (masterEq H ℓmax base ℓ).IsMixture := by
  refine ⟨fun s => ?_, ?_⟩
  · show 0 ≤ (if s.last = ℓ then schedWeight s / q H ℓmax ℓ else 0)
    split_ifs
    · exact div_nonneg (schedWeight_nonneg H ℓmax s) hq.le
    · exact le_rfl
  · show ∑ s : Sched H ℓmax, (if s.last = ℓ then schedWeight s / q H ℓmax ℓ else 0) = 1
    have e : ∀ s : Sched H ℓmax, (if s.last = ℓ then schedWeight s / q H ℓmax ℓ else 0) =
        (if s.last = ℓ then schedWeight s else 0) / q H ℓmax ℓ := by
      intro s; split_ifs <;> simp
    simp only [e]
    rw [← Finset.sum_div]
    exact div_self hq.ne'

theorem masterLe_mix (H ℓmax : ℕ) (base : ℕ → DetPolicy X A) (ℓ : ℕ) (hq : 0 < qLe H ℓmax ℓ) :
    (masterLe H ℓmax base ℓ).IsMixture := by
  refine ⟨fun s => ?_, ?_⟩
  · show 0 ≤ (if s.last ≤ ℓ then schedWeight s / qLe H ℓmax ℓ else 0)
    split_ifs
    · exact div_nonneg (schedWeight_nonneg H ℓmax s) hq.le
    · exact le_rfl
  · show ∑ s : Sched H ℓmax, (if s.last ≤ ℓ then schedWeight s / qLe H ℓmax ℓ else 0) = 1
    have e : ∀ s : Sched H ℓmax, (if s.last ≤ ℓ then schedWeight s / qLe H ℓmax ℓ else 0) =
        (if s.last ≤ ℓ then schedWeight s else 0) / qLe H ℓmax ℓ := by
      intro s; split_ifs <;> simp
    simp only [e]
    rw [← Finset.sum_div]
    exact div_self hq.ne'

theorem trajProb_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (σ : DetPolicy X A)
    (s : Fin H → X) : 0 ≤ trajProb M H σ s := by
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact hM.1.1 _
  · exact (hM.2.1 _ _).1 _

theorem mixExpect_mono (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (π : Mixture X A)
    (hw : ∀ i, 0 ≤ π.w i) (g g' : ℕ → X → A → ℝ) (hg : ∀ t < H, ∀ x a, g t x a ≤ g' t x a) :
    mixExpect M H π g ≤ mixExpect M H π g' := by
  apply Finset.sum_le_sum; intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply Finset.sum_le_sum; intro s _
  apply mul_le_mul_of_nonneg_left _ (trajProb_nonneg M hM H _ s)
  exact Finset.sum_le_sum fun t _ => hg t t.isLt _ _

theorem mixExpect_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (π : Mixture X A)
    (hw : ∀ i, 0 ≤ π.w i) (g : ℕ → X → A → ℝ) (hg : ∀ t < H, ∀ x a, 0 ≤ g t x a) :
    0 ≤ mixExpect M H π g := by
  have := mixExpect_mono M hM H π hw (fun _ _ _ => 0) g hg
  have h0 : mixExpect M H π (fun _ _ _ => 0) = 0 := by simp [mixExpect, expectDet]
  linarith

theorem layerAct_nonempty (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A) (ℓ h : ℕ) (x : X) :
    (layerAct H ℓmax E sel ℓ h x).Nonempty := by
  unfold layerAct
  generalize ℓmax - ℓ = d
  induction d generalizing h x with
  | zero => exact univ_nonempty
  | succ d ih =>
    simp only [layerActAux]
    unfold nextAct
    dsimp only
    split_ifs with hs
    · exact hs
    · exact ih h x

theorem ucbviSup_isQSup (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A)
    (sel : Selector A) (hact : ∀ h x, (act h x).Nonempty)
    (hgl : gl.IsModelEst H) (hsb : sb.IsModelEst H) (hsel : IsArgmaxSelector sel) :
    IsQSupervisor H (ucbviSup H act gl sb sel) := by
  refine ⟨fun h hh x a => ?_, fun h hh x => hsel _ _ (hact h x)⟩
  have hb := vals_bounds H act gl sb sel hgl hsb (H - (h + 1))
  have hc : ((H - (h + 1) : ℕ) : ℝ) + 1 ≤ H := by
    exact_mod_cast (show H - (h + 1) + 1 ≤ H by omega)
  refine ⟨?_, min_le_left _ _, le_max_left _ _, ?_⟩
  · apply le_min (Nat.cast_nonneg _)
    apply le_min
    · exact add_nonneg (backup_nonneg H gl hgl _ (fun y => (hb y).1.1) _ _) ((hgl x _).2.2.1)
    · exact add_nonneg (backup_nonneg H sb hsb _ (fun y => (hb y).1.1) _ _) ((hsb x _).2.2.1)
  · refine max_le (Nat.cast_nonneg _) (max_le ?_ ?_)
    · have h1 := backup_le H gl hgl _ _ (fun y => (hb y).2.2) x a
      have h2 := (hgl x a).2.2.1
      show backup gl _ x a - gl.b x a ≤ (H : ℝ)
      linarith
    · have h1 := backup_le H sb hsb _ _ (fun y => (hb y).2.2) x a
      have h2 := (hsb x a).2.2.1
      show backup sb _ x a - sb.b x a ≤ (H : ℝ)
      linarith

end Gen

end CRRL_T41

open CRRL_T41 in
theorem solution
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal)
    (H ℓmax K C : ℕ) (hH : 1 ≤ H) (hℓmax : 1 ≤ ℓmax) (hC : 1 ≤ C) (hCℓ : C ≤ 2 ^ ℓmax)
    (E : Fin K → EpisodeEst X A)
    (hrange : ∀ k ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      ((E k).gl ℓ).IsModelEst H ∧ ((E k).sb ℓ).IsModelEst H)
    (sel : Selector A) (hsel : IsArgmaxSelector sel)
    (hvalid : ∀ k ℓ, lstar C ≤ ℓ → ℓ ≤ ℓmax →
      ((E k).gl ℓ).IsValid M H (layerSup H ℓmax (E k) sel ℓ) ∧
        ((E k).sb ℓ).IsValid M H (layerSup H ℓmax (E k) sel ℓ)) :
    (C : ℝ) * H + ∑ k, (Vstar0 M H - mixValue M H (master H ℓmax (basePolicies H ℓmax (E k) sel))) ≤
      (C : ℝ) * H
        + 8 * Real.exp 1 * (H : ℝ) ^ 2 *
            (∑ ℓ ∈ Ioc (lstar C) ℓmax, (ℓ : ℝ) * q H ℓmax ℓ * ∑ k, deltaEq M H ℓmax (E k) sel ℓ)
        + 8 * Real.exp 1 * (C : ℝ) * (H : ℝ) ^ 2 * Real.logb 2 (2 * C) * qLe H ℓmax (lstar C) *
            ∑ k, deltaLe M H ℓmax (E k) sel (lstar C) := by
  have hlst1 : 1 ≤ lstar C := le_max_left _ _
  have hlstm : lstar C ≤ ℓmax := max_le hℓmax (Nat.clog_le_of_le_pow hCℓ)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  -- the generic per-learner bound: Proposition 4.2 + Lemma 4.7
  have gen : ∀ (k : Fin K) (ℓ : ℕ), lstar C ≤ ℓ → ℓ ≤ ℓmax → ∀ (π : Mixture X A), π.IsMixture →
      IsQSupervised H π (layerSup H ℓmax (E k) sel ℓ) → ∀ ρ : ℝ,
      HasVisitRatio M H π (basePolicies H ℓmax (E k) sel ℓ) ρ → ∀ useSb : Bool,
      Vstar0 M H - mixValue M H π ≤ ρ * (2 * H) * mixExpect M H π
        (deltaTerm M H (layerSup H ℓmax (E k) sel ℓ)
          (if useSb then (E k).bsb ℓ else (E k).bgl ℓ)
          (if useSb then (E k).psb ℓ else (E k).pgl)) := by
    intro k ℓ hl hlm π hπ hsup ρ hρ useSb
    have h1 : 1 ≤ ℓ := le_trans hlst1 hl
    have hQS : IsQSupervisor H (layerSup H ℓmax (E k) sel ℓ) :=
      ucbviSup_isQSup H _ _ _ sel (layerAct_nonempty H ℓmax (E k) sel ℓ)
        (hrange k ℓ h1 hlm).1 (hrange k ℓ h1 hlm).2 hsel
    have hadm := lemma4_6_admissible_of_valid M hM H ℓmax hH (E k) (hrange k) sel hsel
      (lstar C) hlst1 hlstm (hvalid k) ℓ hl hlm
    have h42 := proposition4_2_visitation_ratio_bound M hM H hH _ hQS hadm π hπ hsup ρ hρ
    have h47 := lemma4_7_bellman_error_bound M hM H hH (layerAct H ℓmax (E k) sel ℓ)
      ((E k).gl ℓ) ((E k).sb ℓ) sel (layerSup H ℓmax (E k) sel ℓ) rfl
      (hrange k ℓ h1 hlm).1 (hrange k ℓ h1 hlm).2 (hvalid k ℓ hl hlm).1 (hvalid k ℓ hl hlm).2
    have hmono := mixExpect_mono M hM H π hπ.1
      (fun h x a => max 0 (max (upperBell M H (layerSup H ℓmax (E k) sel ℓ) h x a)
          (upperBell M H (layerSup H ℓmax (E k) sel ℓ) h x a -
            lowerBell M H (layerSup H ℓmax (E k) sel ℓ) h x a)))
      (deltaTerm M H (layerSup H ℓmax (E k) sel ℓ)
          (if useSb then (E k).bsb ℓ else (E k).bgl ℓ)
          (if useSb then (E k).psb ℓ else (E k).pgl))
      (by
        intro h hh x a
        cases useSb
        · exact max_le_max le_rfl (h47 h hh x a).1
        · exact max_le_max le_rfl (h47 h hh x a).2)
    have hnn := mixExpect_nonneg M hM H π hπ.1
      (fun h x a => max 0 (max (upperBell M H (layerSup H ℓmax (E k) sel ℓ) h x a)
          (upperBell M H (layerSup H ℓmax (E k) sel ℓ) h x a -
            lowerBell M H (layerSup H ℓmax (E k) sel ℓ) h x a)))
      (fun h _ x a => le_max_left _ _)
    have hρ1 : 1 ≤ ρ := hρ.1
    calc Vstar0 M H - mixValue M H π ≤ ρ * (1 + H) * _ := h42
      _ ≤ ρ * (2 * H) * _ := by
          apply mul_le_mul_of_nonneg_right _ hnn
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by nlinarith)
  -- per-episode bound
  have key : ∀ k : Fin K,
      Vstar0 M H - mixValue M H (master H ℓmax (basePolicies H ℓmax (E k) sel)) ≤
        qLe H ℓmax (lstar C) * (8 * Real.exp 1 * C * (H : ℝ) ^ 2 * Real.logb 2 (2 * C) *
          deltaLe M H ℓmax (E k) sel (lstar C)) +
        ∑ ℓ ∈ Ioc (lstar C) ℓmax, q H ℓmax ℓ * (8 * Real.exp 1 * (H : ℝ) ^ 2 * ℓ *
          deltaEq M H ℓmax (E k) sel ℓ) := by
    intro k
    rw [lemma4_4_value_decomposition M hM H ℓmax hH (basePolicies H ℓmax (E k) sel) (lstar C)
      hlst1 hlstm]
    have hsup := lemma4_5_q_supervision M hM H ℓmax hH (E k) sel hsel
    have hrat := lemma4_10_visitation_ratios M hM H ℓmax hH (basePolicies H ℓmax (E k) sel)
    have hadm := lemma4_6_admissible_of_valid M hM H ℓmax hH (E k) (hrange k) sel hsel
      (lstar C) hlst1 hlstm (hvalid k)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (qLe_pos H ℓmax (lstar C) hH hlst1 hlstm).le
      have := gen k (lstar C) le_rfl hlstm _
        (masterLe_mix H ℓmax _ _ (qLe_pos H ℓmax (lstar C) hH hlst1 hlstm))
        (hsup.1 (lstar C) hlst1 hlstm (hadm (lstar C) le_rfl hlstm)) _
        (hrat.2.2 C hC hCℓ) false
      refine le_trans this (le_of_eq ?_)
      simp only [Bool.false_eq_true, if_false]
      unfold deltaLe
      ring
    · apply Finset.sum_le_sum
      intro ℓ hℓ
      have hℓ' := Finset.mem_Ioc.mp hℓ
      have h1 : 1 ≤ ℓ := by omega
      apply mul_le_mul_of_nonneg_left _ (q_pos H ℓmax ℓ hH h1 hℓ'.2).le
      have := gen k ℓ hℓ'.1.le hℓ'.2 _
        (masterEq_mix H ℓmax _ _ (q_pos H ℓmax ℓ hH h1 hℓ'.2))
        (hsup.2 ℓ h1 hℓ'.2 (hadm ℓ hℓ'.1.le hℓ'.2)) _
        (hrat.1 ℓ h1 hℓ'.2) true
      refine le_trans this (le_of_eq ?_)
      simp only [if_true]
      unfold deltaEq
      ring
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin K))) => key k)
  have eq : ∑ k : Fin K, (qLe H ℓmax (lstar C) * (8 * Real.exp 1 * C * (H : ℝ) ^ 2 *
        Real.logb 2 (2 * C) * deltaLe M H ℓmax (E k) sel (lstar C)) +
        ∑ ℓ ∈ Ioc (lstar C) ℓmax, q H ℓmax ℓ * (8 * Real.exp 1 * (H : ℝ) ^ 2 * ℓ *
          deltaEq M H ℓmax (E k) sel ℓ)) =
      8 * Real.exp 1 * (H : ℝ) ^ 2 *
            (∑ ℓ ∈ Ioc (lstar C) ℓmax, (ℓ : ℝ) * q H ℓmax ℓ * ∑ k, deltaEq M H ℓmax (E k) sel ℓ)
        + 8 * Real.exp 1 * (C : ℝ) * (H : ℝ) ^ 2 * Real.logb 2 (2 * C) * qLe H ℓmax (lstar C) *
            ∑ k, deltaLe M H ℓmax (E k) sel (lstar C) := by
    rw [Finset.sum_add_distrib, Finset.sum_comm, add_comm]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
  linarith
