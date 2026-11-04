-- Prove2me | solution 1 for CorruptRobustRL.Supervised.claim4_8_layer_marginal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:43:07.51523+00:00
-- url     : https://prove2.me/submissions/9b03f5ce-cbd8-44c7-ba1b-b5f1df81cd9d

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

open CorruptRobustRL.Supervised
open Finset QSupervisor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace CRRL_C48

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

variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

/-- The layer reached after a schedule segment started from layer `g`. -/
def lastL {L n : ℕ} (g : ℕ) (s : Fin n → Fin L) : ℕ :=
  if hn : n = 0 then g else ((s ⟨n - 1, by omega⟩ : Fin L) : ℕ) + 1

theorem Wt_snoc' (H L f n : ℕ) (s' : Fin n → Fin L) (y : Fin L) :
    Wt H L f (n + 1) (Fin.snoc (α := fun _ => Fin L) s' y) =
      Wt H L f n s' * stepProb H L (lastL f s') ((y : ℕ) + 1) := Wt_snoc H L f n s' y

theorem append_lt {α : Type} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) (k : ℕ) (hk : k < m)
    (h : k < m + n) : Fin.append u v ⟨k, h⟩ = u ⟨k, hk⟩ := by
  have : (⟨k, h⟩ : Fin (m + n)) = Fin.castAdd n ⟨k, hk⟩ := Fin.ext rfl
  rw [this, Fin.append_left]

theorem append_ge {α : Type} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) (k : ℕ) (hk : m ≤ k)
    (h : k < m + n) : Fin.append u v ⟨k, h⟩ = v ⟨k - m, by omega⟩ := by
  have : (⟨k, h⟩ : Fin (m + n)) = Fin.natAdd m ⟨k - m, by omega⟩ := Fin.ext (by simp; omega)
  rw [this, Fin.append_right]

theorem fin_app_congr {α : Type} {m : ℕ} (u : Fin m → α) {k k' : ℕ} (hk : k < m) (hk' : k' < m)
    (h : k = k') : u ⟨k, hk⟩ = u ⟨k', hk'⟩ := by subst h; rfl

theorem Wt_append (H L f m n : ℕ) (p : Fin m → Fin L) (r : Fin n → Fin L) :
    Wt H L f (m + n) (Fin.append p r) = Wt H L f m p * Wt H L (lastL f p) n r := by
  unfold Wt
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp only [Fin.coe_castAdd, Fin.append_left]
    split_ifs with hi
    · rfl
    · rw [append_lt p r ((i : ℕ) - 1) (by omega)]
  · apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.coe_natAdd, Fin.append_right]
    unfold lastL
    by_cases hj : (j : ℕ) = 0
    · rw [if_pos hj]
      by_cases hm : m = 0
      · rw [if_pos (by omega), dif_pos hm]
      · rw [if_neg (by omega), dif_neg hm, append_lt p r _ (by omega)]
        rw [fin_app_congr p _ (by omega) (show m + (j : ℕ) - 1 = m - 1 by omega)]
    · rw [if_neg hj, if_neg (by omega), append_ge p r _ (by omega)]
      rw [fin_app_congr r _ (by omega) (show m + (j : ℕ) - 1 - m = (j : ℕ) - 1 by omega)]

theorem sum_append {α : Type} [Fintype α] [DecidableEq α] {m n : ℕ} (Φ : (Fin (m + n) → α) → ℝ) :
    ∑ s, Φ s = ∑ p : Fin m → α, ∑ r : Fin n → α, Φ (Fin.append p r) := by
  rw [← (Fin.appendEquiv m n).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The kernel of the layer schedule as a matrix on `Fin L` (index `i` is layer `i + 1`). -/
noncomputable def K (H L : ℕ) : Matrix (Fin L) (Fin L) ℝ :=
  fun i j => stepProb H L ((i : ℕ) + 1) ((j : ℕ) + 1)

theorem lastL_range {L n : ℕ} (g : ℕ) (hg1 : 1 ≤ g) (hgL : g ≤ L) (s : Fin n → Fin L) :
    1 ≤ lastL g s ∧ lastL g s ≤ L := by
  unfold lastL
  split_ifs
  · exact ⟨hg1, hgL⟩
  · have := (s ⟨n - 1, by omega⟩).isLt; omega

theorem suffix_eq (H L : ℕ) : ∀ n (g : ℕ) (hg1 : 1 ≤ g) (hgL : g ≤ L) (z : Fin L),
    ∑ r : Fin n → Fin L, (if lastL g r = (z : ℕ) + 1 then Wt H L g n r else 0) =
      (K H L ^ n) ⟨g - 1, by omega⟩ z := by
  intro n
  induction n with
  | zero =>
    intro g hg1 hgL z
    rw [pow_zero, Matrix.one_apply, Fintype.sum_unique]
    have h1 : lastL g (default : Fin 0 → Fin L) = g := by simp [lastL]
    have h2 : Wt H L g 0 (default : Fin 0 → Fin L) = 1 := by simp [Wt]
    rw [h1, h2]
    by_cases h : g = (z : ℕ) + 1
    · rw [if_pos h, if_pos (Fin.ext (by dsimp only; omega))]
    · rw [if_neg h, if_neg (fun h' => h (by have := congrArg Fin.val h'; dsimp only at this; omega))]
  | succ n ih =>
    intro g hg1 hgL z
    rw [pow_succ, Matrix.mul_apply]
    rw [← (Fin.snocEquiv (fun _ => Fin L)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    change ∑ s' : Fin n → Fin L, ∑ y : Fin L, (if lastL g (Fin.snoc (α := fun _ => Fin L) s' y) =
      (z : ℕ) + 1 then Wt H L g (n + 1) (Fin.snoc (α := fun _ => Fin L) s' y) else 0) = _
    have hl : ∀ (s' : Fin n → Fin L) (y : Fin L),
        lastL g (Fin.snoc (α := fun _ => Fin L) s' y) = (y : ℕ) + 1 := by
      intro s' y
      unfold lastL
      rw [dif_neg (by omega)]
      congr 2
      have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
      rw [this, Fin.snoc_last]
    simp only [hl, Wt_snoc']
    have e1 : ∀ s' : Fin n → Fin L, ∑ y : Fin L, (if (y : ℕ) + 1 = (z : ℕ) + 1 then
        Wt H L g n s' * stepProb H L (lastL g s') ((y : ℕ) + 1) else 0) =
        Wt H L g n s' * stepProb H L (lastL g s') ((z : ℕ) + 1) := by
      intro s'
      rw [Finset.sum_eq_single z]
      · rw [if_pos rfl]
      · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext (by omega))
      · intro h; exact absurd (mem_univ _) h
    simp only [e1]
    simp only [← ih g hg1 hgL, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s' _
    obtain ⟨h1, h2⟩ := lastL_range g hg1 hgL s'
    rw [Finset.sum_eq_single ⟨lastL g s' - 1, by omega⟩]
    · rw [if_pos (by simp; omega)]
      unfold K
      congr 2
      simp; omega
    · intro b _ hb
      rw [if_neg, zero_mul]
      intro h; apply hb; apply Fin.ext; simp; omega
    · intro h; exact absurd (mem_univ _) h

theorem K_nonneg (H L : ℕ) (i j : Fin L) : 0 ≤ K H L i j := stepProb_nonneg _ _ _ _

theorem K_below (H L : ℕ) (i j : Fin L) (h : j < i) : K H L i j = 0 := by
  unfold K stepProb
  have : (j : ℕ) < i := h
  rw [if_neg (by omega), if_neg (by omega)]

theorem K_diag_le (H L : ℕ) (i : Fin L) : K H L i i ≤ 1 := by
  unfold K stepProb
  rw [if_neg (by omega), if_pos rfl]
  have : 0 ≤ ∑ m ∈ Ioc ((i : ℕ) + 1) L, 1 / (2 * (m : ℝ) * H) * (2 : ℝ)⁻¹ ^ (m - ((i : ℕ) + 1)) :=
    Finset.sum_nonneg fun m _ => by positivity
  linarith

theorem K_diag_ge (H L : ℕ) (hH : 1 ≤ H) (i : Fin L) : 1 - 1 / (2 * (H : ℝ)) ≤ K H L i i := by
  unfold K stepProb
  rw [if_neg (by omega), if_pos rfl]
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hle : ∑ m ∈ Ioc ((i : ℕ) + 1) L, 1 / (2 * (m : ℝ) * H) * (2 : ℝ)⁻¹ ^ (m - ((i : ℕ) + 1)) ≤
      ∑ m ∈ Ioc ((i : ℕ) + 1) L, 1 / (2 * (H : ℝ)) * (2 : ℝ)⁻¹ ^ (m - ((i : ℕ) + 1)) := by
    apply Finset.sum_le_sum; intro m hm
    have hm1 : (1 : ℝ) ≤ m := by
      have := (Finset.mem_Ioc.mp hm).1; exact_mod_cast (show 1 ≤ m by omega)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [← Finset.mul_sum] at hle
  have h2 := mul_le_of_le_one_right (show (0 : ℝ) ≤ 1 / (2 * H) by positivity)
    (geom_tail ((i : ℕ) + 1) L)
  linarith

theorem K_up (H L : ℕ) (i j : Fin L) (h : i < j) :
    K H L i j = 1 / (2 * (((j : ℕ) + 1 : ℕ) : ℝ) * H) * (2 : ℝ)⁻¹ ^ ((j : ℕ) - i) := by
  unfold K stepProb
  have : (i : ℕ) < j := h
  rw [if_pos ⟨by omega, by have := j.isLt; omega⟩]
  congr 2
  omega

theorem K_up_le (H L : ℕ) (hH : 1 ≤ H) (i j : Fin L) (h : i < j) :
    K H L i j ≤ (2 : ℝ)⁻¹ ^ ((j : ℕ) - i) / (2 * H) * (1 / ((j : ℕ) + 1)) := by
  rw [K_up H L i j h]
  push_cast
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  apply le_of_eq
  field_simp

/-- The invariant for the `n`-step kernel started from layer `f`. -/
theorem Kpow_bounds (H L : ℕ) (hH : 1 ≤ H) (f : Fin L) : ∀ n, n ≤ H →
    (∀ y, 0 ≤ (K H L ^ n) f y) ∧ (∀ y, y < f → (K H L ^ n) f y = 0) ∧
    (K H L ^ n) f f ≤ 1 ∧
    (∀ z, f < z → (K H L ^ n) f z ≤ n * ((2 : ℝ)⁻¹ ^ ((z : ℕ) - f) / (2 * H))) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun y => ?_, fun y hy => ?_, ?_, fun z hz => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · rw [pow_zero, Matrix.one_apply, if_neg (ne_of_gt hy)]
    · rw [pow_zero, Matrix.one_apply, if_pos rfl]
    · rw [pow_zero, Matrix.one_apply, if_neg (ne_of_lt hz)]; simp
  | succ n ih =>
    intro hn
    obtain ⟨P1, P2, P3, P4⟩ := ih (by omega)
    -- `K^n f y ≤ 2^{-(y-f)}` for `y ≥ f`
    have Q : ∀ y, f ≤ y → (K H L ^ n) f y ≤ (2 : ℝ)⁻¹ ^ ((y : ℕ) - f) := by
      intro y hy
      rcases eq_or_lt_of_le hy with h | h
      · subst h; simpa using P3
      · refine le_trans (P4 y h) ?_
        have hn' : (n : ℝ) ≤ H := by exact_mod_cast (show n ≤ H by omega)
        have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ ((y : ℕ) - f) := by positivity
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    have expand : ∀ z, (K H L ^ (n + 1)) f z = ∑ y, (K H L ^ n) f y * K H L y z := by
      intro z; rw [pow_succ, Matrix.mul_apply]
    refine ⟨fun y => ?_, fun y hy => ?_, ?_, fun z hz => ?_⟩
    · rw [expand]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (P1 x) (K_nonneg H L x y)
    · rw [expand]
      apply Finset.sum_eq_zero
      intro x _
      rcases lt_or_ge x f with h | h
      · rw [P2 x h, zero_mul]
      · rw [K_below H L x y (lt_of_lt_of_le hy h), mul_zero]
    · rw [expand, Finset.sum_eq_single f]
      · exact le_trans (mul_le_of_le_one_right (P1 f) (K_diag_le H L f)) P3
      · intro x _ hx
        rcases lt_or_gt_of_ne hx with h | h
        · rw [P2 x h, zero_mul]
        · rw [K_below H L x f h, mul_zero]
      · intro h; exact absurd (mem_univ _) h
    · rw [expand]
      set A : ℝ := n * ((2 : ℝ)⁻¹ ^ ((z : ℕ) - f) / (2 * H))
      set B : ℝ := (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) / (2 * H) * (1 / ((z : ℕ) + 1))
      have hterm : ∀ y, (K H L ^ n) f y * K H L y z ≤
          (if y = z then A else if y < z then B else 0) := by
        intro y
        split_ifs with h1 h2
        · subst h1
          exact le_trans (mul_le_of_le_one_right (P1 y) (K_diag_le H L y)) (P4 y hz)
        · rcases lt_or_ge y f with h3 | h3
          · rw [P2 y h3, zero_mul]; positivity
          · have e1 := Q y h3
            have e2 := K_up_le H L hH y z h2
            have hyz : (y : ℕ) < z := h2
            have hfy : (f : ℕ) ≤ y := h3
            calc (K H L ^ n) f y * K H L y z ≤ (2 : ℝ)⁻¹ ^ ((y : ℕ) - f) *
                ((2 : ℝ)⁻¹ ^ ((z : ℕ) - y) / (2 * H) * (1 / ((z : ℕ) + 1))) :=
                  mul_le_mul e1 e2 (K_nonneg H L y z) (by positivity)
              _ = B := by
                  simp only [B]
                  rw [show (z : ℕ) - f = ((y : ℕ) - f) + ((z : ℕ) - y) by omega, pow_add]
                  ring
        · have : z < y := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
          rw [K_below H L y z this, mul_zero]
      refine le_trans (Finset.sum_le_sum fun y _ => hterm y) ?_
      have hsplit : ∑ y : Fin L, (if y = z then A else if y < z then B else 0) =
          A + ∑ y : Fin L, (if y < z then B else 0) := by
        have pw : ∀ y : Fin L, (if y = z then A else if y < z then B else 0) =
            (if y = z then A else 0) + (if y < z then B else 0) := by
          intro y
          by_cases h1 : y = z
          · subst h1; simp
          · simp [h1]
        simp only [pw]
        rw [Finset.sum_add_distrib]
        congr 1
        simp
      rw [hsplit, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_gt_eq_Iio,
        Fin.card_Iio]
      have hz1 : ((z : ℕ) : ℝ) * (1 / ((z : ℕ) + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) / (2 * H) := by positivity
      simp only [A, B]
      push_cast
      nlinarith

theorem Wt_const (H L f n : ℕ) (c : Fin L) :
    Wt H L f (n + 1) (fun _ => c) =
      stepProb H L f ((c : ℕ) + 1) * stepProb H L ((c : ℕ) + 1) ((c : ℕ) + 1) ^ n := by
  unfold Wt
  rw [Fin.prod_univ_succ]
  simp

theorem stay_pow (H L : ℕ) (hH : 1 ≤ H) (c : Fin L) (n : ℕ) (hn : n ≤ H) :
    (1 : ℝ) / 2 ≤ K H L c c ^ n := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have h1 := K_diag_ge H L hH c
  have hb : 1 + (n : ℝ) * (-(1 / (2 * (H : ℝ)))) ≤ (1 + -(1 / (2 * (H : ℝ)))) ^ n := by
    apply one_add_mul_le_pow
    have : 1 / (2 * (H : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    linarith
  have h2 : (1 + -(1 / (2 * (H : ℝ)))) ^ n ≤ K H L c c ^ n := by
    apply pow_le_pow_left₀ _ (by linarith)
    have : 1 / (2 * (H : ℝ)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    linarith
  have h3 : (n : ℝ) * (1 / (2 * (H : ℝ))) ≤ 1 / 2 := by
    have : (n : ℝ) ≤ H := by exact_mod_cast hn
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  linarith

theorem e_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp 1; linarith

/-- Per-prefix bound for `π^master_ℓ`. -/
theorem prefix_eq (H L : ℕ) (hH : 1 ≤ H) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ H) (g ℓ : ℕ)
    (hg1 : 1 ≤ g) (hgL : g ≤ L) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    ∑ r : Fin n → Fin L, (if lastL g r = ℓ then Wt H L g n r else 0) ≤
      4 * Real.exp 1 * H * ℓ * Wt H L g n (fun _ => (⟨ℓ - 1, by omega⟩ : Fin L)) := by
  set z : Fin L := ⟨ℓ - 1, by omega⟩
  have hz : ℓ = (z : ℕ) + 1 := by simp [z]; omega
  have e1 := suffix_eq H L n g hg1 hgL z
  rw [← hz] at e1
  rw [e1]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Wt_const]
  set f : Fin L := ⟨g - 1, by omega⟩
  have hgf : g = (f : ℕ) + 1 := by simp [f]; omega
  obtain ⟨P1, P2, P3, P4⟩ := Kpow_bounds H L hH f (n' + 1) hn
  have hst := stay_pow H L hH z n' (by omega)
  have hK : stepProb H L ((z : ℕ) + 1) ((z : ℕ) + 1) = K H L z z := rfl
  have hKf : stepProb H L g ((z : ℕ) + 1) = K H L f z := by rw [hgf]; rfl
  rw [hK, hKf]
  have he := e_ge_one
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hKzz0 := K_nonneg H L z z
  have hR0 : 0 ≤ 4 * Real.exp 1 * H * ℓ * (K H L f z * K H L z z ^ n') := by
    have := K_nonneg H L f z; positivity
  rcases lt_trichotomy z f with h | h | h
  · rw [P2 z h]; exact hR0
  · rw [← h] at P3
    rw [← h]
    have hst2 := stay_pow H L hH z (n' + 1) hn
    rw [pow_succ] at hst2
    have : (1 : ℝ) ≤ 4 * Real.exp 1 * H * ℓ * (K H L z z * K H L z z ^ n') := by
      have h4 : (2 : ℝ) ≤ 4 * Real.exp 1 * H * ℓ := by
        have : (1 : ℝ) ≤ Real.exp 1 * H * ℓ := by
          have := mul_le_mul he hH1 (by norm_num) (by linarith)
          have := mul_le_mul this hℓ1' (by norm_num) (by positivity)
          linarith
        linarith
      rw [mul_comm (K H L z z) _]
      nlinarith
    linarith
  · have h4 := P4 z h
    rw [K_up H L f z h]
    have hzℓ : (((z : ℕ) + 1 : ℕ) : ℝ) = ℓ := by rw [hz]
    rw [hzℓ]
    have hn' : ((n' + 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hn
    have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) := by positivity
    have hH0 : (0 : ℝ) < H := by linarith
    have hl0 : (0 : ℝ) < ℓ := by linarith
    have eq1 : 4 * Real.exp 1 * H * ℓ * (1 / (2 * ℓ * H) * (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) * K H L z z ^ n') =
        2 * Real.exp 1 * (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) * K H L z z ^ n' := by
      field_simp
      ring
    rw [eq1]
    have h5 : ((n' + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ ((z : ℕ) - f) / (2 * H)) ≤
        (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h6 : (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) / 2 ≤ 2 * Real.exp 1 * (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) * K H L z z ^ n' := by
      have : (1 : ℝ) ≤ 2 * Real.exp 1 * K H L z z ^ n' := by nlinarith
      nlinarith
    linarith

/-- Per-prefix bound for `π^master_{≤ℓ}`. -/
theorem prefix_le (H L : ℕ) (hH : 1 ≤ H) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ H) (g ℓ : ℕ)
    (hg1 : 1 ≤ g) (hgL : g ≤ L) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    ∑ r : Fin n → Fin L, (if lastL g r ≤ ℓ then Wt H L g n r else 0) ≤
      2 * 2 ^ ℓ * Real.exp 1 * H * ℓ * Wt H L g n (fun _ => (⟨ℓ - 1, by omega⟩ : Fin L)) := by
  set z : Fin L := ⟨ℓ - 1, by omega⟩
  have hz : ℓ = (z : ℕ) + 1 := by simp [z]; omega
  set f : Fin L := ⟨g - 1, by omega⟩
  have hgf : g = (f : ℕ) + 1 := by simp [f]; omega
  have he := e_ge_one
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hRW : 0 ≤ Wt H L g n (fun _ => z) := Finset.prod_nonneg fun t _ => stepProb_nonneg _ _ _ _
  rcases lt_or_ge ℓ g with hgt | hle
  · -- no schedule segment started above `ℓ` ends at or below `ℓ`
    have decomp : ∀ r : Fin n → Fin L, (if lastL g r ≤ ℓ then Wt H L g n r else 0) =
        ∑ y : Fin L, if (y : ℕ) + 1 ≤ ℓ then
          (if lastL g r = (y : ℕ) + 1 then Wt H L g n r else 0) else 0 := by
      intro r
      obtain ⟨h1, h2⟩ := lastL_range g hg1 hgL r
      rw [Finset.sum_eq_single ⟨lastL g r - 1, by omega⟩]
      · simp only
        by_cases hc : lastL g r ≤ ℓ
        · rw [if_pos hc, if_pos (by omega), if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
      · intro b _ hb
        split_ifs with h3 h4
        · exact absurd (Fin.ext (by simp; omega)) hb
        · rfl
        · rfl
      · intro h; exact absurd (mem_univ _) h
    simp only [decomp]
    rw [Finset.sum_comm]
    have : ∑ y : Fin L, ∑ r : Fin n → Fin L, (if (y : ℕ) + 1 ≤ ℓ then
        (if lastL g r = (y : ℕ) + 1 then Wt H L g n r else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro y _
      by_cases hy : (y : ℕ) + 1 ≤ ℓ
      · simp only [if_pos hy]
        rw [suffix_eq H L n g hg1 hgL y]
        obtain ⟨-, P2, -, -⟩ := Kpow_bounds H L hH f n hn
        exact P2 y (by show (y : ℕ) < f; simp [f]; omega)
      · simp [hy]
    rw [this]
    positivity
  · have hsum : ∑ r : Fin n → Fin L, (if lastL g r ≤ ℓ then Wt H L g n r else 0) ≤ 1 := by
      rw [← Wt_sum H L g hg1 hgL n]
      apply Finset.sum_le_sum; intro r _
      split_ifs
      · exact le_rfl
      · exact Finset.prod_nonneg fun t _ => stepProb_nonneg _ _ _ _
    refine le_trans hsum ?_
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Wt_const]
    have hst := stay_pow H L hH z n' (by omega)
    have hK : stepProb H L ((z : ℕ) + 1) ((z : ℕ) + 1) = K H L z z := rfl
    have hKf : stepProb H L g ((z : ℕ) + 1) = K H L f z := by rw [hgf]; rfl
    rw [hK, hKf]
    have h2l : (2 : ℝ) ≤ 2 ^ ℓ := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ1
    have hρ : (4 : ℝ) ≤ 2 * 2 ^ ℓ * Real.exp 1 * H * ℓ := by
      have a1 : (1 : ℝ) ≤ Real.exp 1 * H := by nlinarith
      have a2 : (1 : ℝ) ≤ Real.exp 1 * H * ℓ := by nlinarith
      nlinarith
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hfz : f = z := Fin.ext (by simp [f, z]; omega)
      rw [hfz]
      have hst2 := stay_pow H L hH z (n' + 1) hn
      rw [pow_succ, mul_comm] at hst2
      nlinarith
    · have hfz : f < z := by show (f : ℕ) < z; simp [f, z]; omega
      rw [K_up H L f z hfz]
      have hzℓ : (((z : ℕ) + 1 : ℕ) : ℝ) = ℓ := by rw [hz]
      rw [hzℓ]
      have hpow : (2 : ℝ)⁻¹ ^ (ℓ - 1) ≤ (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simp [f, z] <;> omega)
      have h22 : (2 : ℝ) ^ ℓ * (2 : ℝ)⁻¹ ^ (ℓ - 1) = 2 := by
        obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
        rw [show k + 1 - 1 = k by omega, pow_succ, mul_comm ((2 : ℝ) ^ k) 2, mul_assoc,
          ← mul_pow]
        norm_num
      have hH0 : (0 : ℝ) < H := by linarith
      have hl0 : (0 : ℝ) < ℓ := by linarith
      have eq1 : 2 * 2 ^ ℓ * Real.exp 1 * H * ℓ * (1 / (2 * ℓ * H) * (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) *
          K H L z z ^ n') = 2 ^ ℓ * Real.exp 1 * (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) * K H L z z ^ n' := by
        field_simp
        try ring
      rw [eq1]
      have h3 : (2 : ℝ) ≤ 2 ^ ℓ * (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) := by
        calc (2 : ℝ) = 2 ^ ℓ * (2 : ℝ)⁻¹ ^ (ℓ - 1) := h22.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      have h4 : (1 : ℝ) ≤ 2 ^ ℓ * (2 : ℝ)⁻¹ ^ ((z : ℕ) - f) * K H L z z ^ n' := by nlinarith
      nlinarith


theorem split_lay (HH L k m : ℕ) (hk : 1 ≤ k) (p : Fin k → Fin L) (r : Fin m → Fin L) :
    Sched.lay (H := k + m) (ℓmax := L) (Fin.append p r) ⟨k - 1, by omega⟩ = lastL 1 p := by
  unfold Sched.lay lastL
  rw [dif_neg (by omega), append_lt p r (k - 1) (by omega)]

theorem split_last (L k m : ℕ) (hk : 1 ≤ k) (p : Fin k → Fin L) (r : Fin m → Fin L) :
    Sched.last (H := k + m) (ℓmax := L) (Fin.append p r) = lastL (lastL 1 p) r := by
  unfold Sched.last Sched.lay
  rw [dif_pos (by omega)]
  by_cases hm : m = 0
  · subst hm
    unfold lastL
    rw [dif_pos rfl, dif_neg (by omega), append_lt p r _ (by omega),
      fin_app_congr p _ (by omega) (show k + 0 - 1 = k - 1 by omega)]
  · unfold lastL
    rw [dif_neg hm, append_ge p r _ (by omega),
      fin_app_congr r _ (by omega) (show k + m - 1 - k = m - 1 by omega)]

theorem Kpow_nonneg (H L : ℕ) (z : Fin L) : ∀ m y, 0 ≤ (K H L ^ m) z y := by
  intro m
  induction m with
  | zero => intro y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ m ih =>
    intro y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (ih w) (K_nonneg H L w y)

theorem Kpow_diag_ge (H L : ℕ) (z : Fin L) : ∀ m, K H L z z ^ m ≤ (K H L ^ m) z z := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply]
    refine le_trans ?_ (Finset.single_le_sum (f := fun y => (K H L ^ m) z y * K H L y z)
      (fun y _ => mul_nonneg (Kpow_nonneg H L z m y) (K_nonneg H L y z)) (mem_univ z))
    exact mul_le_mul_of_nonneg_right ih (K_nonneg H L z z)

/-- `P[ℓ_k = f]` for a schedule of length `k + m` is the `(1, f)` entry of `K^k`, and
`P[ℓ_k = f ∧ ℓ_last = f] = P[ℓ_k = f] · (K^m)_{ff}`. -/
theorem layer_split (HH L k m : ℕ) (hk : 1 ≤ k) (f : ℕ) (hf1 : 1 ≤ f) (hfL : f ≤ L) :
    (∑ s : Fin (k + m) → Fin L, (if Sched.lay (H := k + m) (ℓmax := L) s ⟨k - 1, by omega⟩ = f
        then Wt HH L 1 (k + m) s else 0)) = (K HH L ^ k) ⟨0, by omega⟩ ⟨f - 1, by omega⟩ ∧
    (∑ s : Fin (k + m) → Fin L, (if Sched.lay (H := k + m) (ℓmax := L) s ⟨k - 1, by omega⟩ = f ∧
        Sched.last (H := k + m) (ℓmax := L) s = f then Wt HH L 1 (k + m) s else 0)) =
      (K HH L ^ k) ⟨0, by omega⟩ ⟨f - 1, by omega⟩ * (K HH L ^ m) ⟨f - 1, by omega⟩ ⟨f - 1, by omega⟩ := by
  have e0 := suffix_eq HH L k 1 le_rfl (by omega) ⟨f - 1, by omega⟩
  simp only [show ((⟨f - 1, by omega⟩ : Fin L) : ℕ) + 1 = f by simp; omega] at e0
  have e0' : (⟨1 - 1, by omega⟩ : Fin L) = ⟨0, by omega⟩ := rfl
  rw [e0'] at e0
  constructor
  · rw [sum_append, ← e0]
    apply Finset.sum_congr rfl; intro p _
    simp only [split_lay HH L k m hk p, Wt_append]
    split_ifs with h1
    · rw [← Finset.mul_sum, Wt_sum HH L _ (lastL_range 1 le_rfl (by omega) p).1
        (lastL_range 1 le_rfl (by omega) p).2 m, mul_one]
    · simp
  · rw [sum_append, ← e0, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    simp only [split_lay HH L k m hk p, split_last L k m hk p, Wt_append]
    by_cases h1 : lastL 1 p = f
    · rw [if_pos h1]
      have e1 := suffix_eq HH L m f hf1 hfL ⟨f - 1, by omega⟩
      simp only [show ((⟨f - 1, by omega⟩ : Fin L) : ℕ) + 1 = f by simp; omega] at e1
      rw [← e1, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      rw [h1]
      split_ifs with h2 h3 h3
      · rfl
      · exact absurd h2.2 h3
      · exact absurd ⟨rfl, h3⟩ h2
      · simp
    · rw [if_neg h1, zero_mul]
      apply Finset.sum_eq_zero; intro r _
      rw [if_neg (fun h => h1 h.1)]

theorem layerProb_split (H ℓmax t m : ℕ) (hH : H = t + 1 + m) (ht : t < H) (f : ℕ) (hf1 : 1 ≤ f)
    (hfL : f ≤ ℓmax) :
    layerProb H ℓmax ⟨t, ht⟩ f = (K H ℓmax ^ (t + 1)) ⟨0, by omega⟩ ⟨f - 1, by omega⟩ ∧
    layerStayProb H ℓmax ⟨t, ht⟩ f =
      (K H ℓmax ^ (t + 1)) ⟨0, by omega⟩ ⟨f - 1, by omega⟩ * (K H ℓmax ^ m) ⟨f - 1, by omega⟩ ⟨f - 1, by omega⟩ := by
  subst hH
  have := layer_split (t + 1 + m) ℓmax (t + 1) m (by omega) f hf1 hfL
  exact this

end CRRL_C48

open CRRL_C48 in
theorem solution
    (H ℓmax : ℕ) (hH : 1 ≤ H) (t : Fin H) (f : ℕ) (hf : 1 ≤ f) (hfmax : f ≤ ℓmax) :
    layerProb H ℓmax t f ≤ (2 : ℝ) ^ (1 - (f : ℤ)) ∧
      (1 < f → layerProb H ℓmax t f ≤ (2 : ℝ) ^ (-(f : ℤ))) := by
  obtain ⟨t, ht⟩ := t
  obtain ⟨e1, -⟩ := layerProb_split H ℓmax t (H - (t + 1)) (by omega) ht f hf hfmax
  rw [e1]
  obtain ⟨-, -, P3, P4⟩ := Kpow_bounds H ℓmax hH ⟨0, by omega⟩ (t + 1) (by omega)
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have key : 1 < f → (K H ℓmax ^ (t + 1)) ⟨0, by omega⟩ ⟨f - 1, by omega⟩ ≤ (2 : ℝ) ^ (-(f : ℤ)) := by
    intro h1
    have h4 := P4 ⟨f - 1, by omega⟩ (by show 0 < f - 1; omega)
    simp only [Nat.sub_zero] at h4
    refine le_trans h4 ?_
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    have ht' : ((t + 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast ht
    have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (f - 1) := by positivity
    have hf' : (2 : ℝ)⁻¹ ^ f = (2 : ℝ)⁻¹ ^ (f - 1) / 2 := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [show g + 1 - 1 = g by omega, pow_succ]; ring
    rw [hf', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨?_, key⟩
  rcases eq_or_lt_of_le hf with h | h
  · subst h
    simpa using P3
  · refine le_trans (key h) ?_
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
