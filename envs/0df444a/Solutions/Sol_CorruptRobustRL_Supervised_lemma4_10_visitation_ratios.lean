-- Prove2me | solution 1 for CorruptRobustRL.Supervised.lemma4_10_visitation_ratios
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:39:34.767341+00:00
-- url     : https://prove2.me/submissions/65cd7b64-4f9f-4ed1-ba84-8973b5b64a2b

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

open CorruptRobustRL.Supervised
open Finset QSupervisor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace CRRL_L410

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

section Occ
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

theorem trajProb_nonneg' (M : NominalMDP X A) (hM : M.IsNominal) (n : ℕ) (σ : DetPolicy X A)
    (s : Fin n → X) : 0 ≤ trajProb M n σ s := by
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact hM.1.1 _
  · exact (hM.2.1 _ _).1 _

theorem occ_nonneg (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (σ : DetPolicy X A)
    (τ : ℕ) (x : X) (a : A) : 0 ≤ occ M H σ τ x a := by
  unfold occ
  split_ifs
  · exact Finset.sum_nonneg fun s _ => by split_ifs; exacts [trajProb_nonneg' M hM _ σ s, le_rfl]
  · exact le_rfl

theorem occ_congr (M : NominalMDP X A) (H : ℕ) (σ σ' : DetPolicy X A)
    (h : ∀ t < H, ∀ x, σ t x = σ' t x) (τ : ℕ) (x : X) (a : A) :
    occ M H σ τ x a = occ M H σ' τ x a := by
  unfold occ
  split_ifs with hτ
  · apply Finset.sum_congr rfl
    intro s _
    rw [h τ hτ x]
    congr 1
    unfold trajProb
    apply Finset.prod_congr rfl
    intro t _
    split_ifs
    · rfl
    · rw [h _ (by have := t.isLt; omega)]
  · rfl

theorem concat_agree (h n L : ℕ) (base : ℕ → DetPolicy X A) (ℓ : ℕ) (z : Fin L)
    (hz : (z : ℕ) + 1 = ℓ) (p : Fin h → Fin L) (r : Fin n → Fin L) :
    ∀ t < h + n, ∀ x, concat (schedPolicy (H := h + n) (ℓmax := L) base (Fin.append p r)) h (base ℓ) t x =
      schedPolicy (H := h + n) (ℓmax := L) base (Fin.append p (fun _ => z)) t x := by
  intro t ht x
  unfold concat schedPolicy Sched.lay
  rw [dif_pos ht, dif_pos ht]
  split_ifs with h1
  · rw [append_lt p r t h1, append_lt p _ t h1]
  · rw [append_ge p _ t (by omega), hz]

theorem last_append (h n L : ℕ) (hn : 1 ≤ n) (g : ℕ) (p : Fin h → Fin L) (r : Fin n → Fin L) :
    Sched.last (H := h + n) (ℓmax := L) (Fin.append p r) = lastL g r := by
  unfold Sched.last Sched.lay lastL
  rw [dif_pos (by omega), dif_neg (by omega), append_ge p r _ (by omega)]
  rw [fin_app_congr r _ (by omega) (show h + n - 1 - h = n - 1 by omega)]

theorem assembly (M : NominalMDP X A) (hM : M.IsNominal) (h n : ℕ) (hn1 : 1 ≤ n) (L : ℕ)
    (base : ℕ → DetPolicy X A) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L)
    (P : ℕ → Prop) [DecidablePred P] (hPℓ : P ℓ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hb : ∀ g, 1 ≤ g → g ≤ L → ∑ r : Fin n → Fin L, (if P (lastL g r) then Wt (h + n) L g n r else 0) ≤
      ρ * Wt (h + n) L g n (fun _ => (⟨ℓ - 1, by omega⟩ : Fin L))) (τ : ℕ) (x : X) (a : A) :
    ∑ s : Sched (h + n) L, (if P s.last then schedWeight s else 0) *
        occ M (h + n) (concat (schedPolicy base s) h (base ℓ)) τ x a ≤
      ρ * ∑ s : Sched (h + n) L, (if P s.last then schedWeight s else 0) *
        occ M (h + n) (schedPolicy base s) τ x a := by
  set z : Fin L := ⟨ℓ - 1, by omega⟩
  have hz : (z : ℕ) + 1 = ℓ := by simp [z]; omega
  set O : (Fin h → Fin L) → ℝ := fun p =>
    occ M (h + n) (schedPolicy (H := h + n) (ℓmax := L) base (Fin.append p (fun _ => z))) τ x a
  have hO0 : ∀ p, 0 ≤ O p := fun p => occ_nonneg M hM _ _ τ x a
  have hW : ∀ (p : Fin h → Fin L) (r : Fin n → Fin L),
      schedWeight (H := h + n) (ℓmax := L) (Fin.append p r) =
        Wt (h + n) L 1 h p * Wt (h + n) L (lastL 1 p) n r := fun p r =>
    Wt_append (h + n) L 1 h n p r
  have hWp : ∀ p : Fin h → Fin L, 0 ≤ Wt (h + n) L 1 h p :=
    fun p => Finset.prod_nonneg fun t _ => stepProb_nonneg _ _ _ _
  have hWr : ∀ g (r : Fin n → Fin L), 0 ≤ Wt (h + n) L g n r :=
    fun g r => Finset.prod_nonneg fun t _ => stepProb_nonneg _ _ _ _
  have hg : ∀ p : Fin h → Fin L, 1 ≤ lastL 1 p ∧ lastL 1 p ≤ L :=
    fun p => lastL_range 1 le_rfl (by omega) p
  -- left side
  have hL : ∑ s : Sched (h + n) L, (if P s.last then schedWeight s else 0) *
        occ M (h + n) (concat (schedPolicy base s) h (base ℓ)) τ x a =
      ∑ p : Fin h → Fin L, (Wt (h + n) L 1 h p * O p) *
        ∑ r : Fin n → Fin L, (if P (lastL (lastL 1 p) r) then Wt (h + n) L (lastL 1 p) n r else 0) := by
    rw [sum_append]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [last_append h n L hn1 (lastL 1 p) p r, hW p r,
      occ_congr M (h + n) _ _ (concat_agree h n L base ℓ z hz p r) τ x a]
    split_ifs <;> ring
  -- right side
  have hR : ∑ p : Fin h → Fin L, (Wt (h + n) L 1 h p * O p) * Wt (h + n) L (lastL 1 p) n (fun _ => z) ≤
      ∑ s : Sched (h + n) L, (if P s.last then schedWeight s else 0) *
        occ M (h + n) (schedPolicy base s) τ x a := by
    rw [sum_append]
    apply Finset.sum_le_sum; intro p _
    have hlz : lastL (lastL 1 p) (fun _ : Fin n => z) = ℓ := by
      unfold lastL; rw [dif_neg (by omega)]; exact hz
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun r : Fin n → Fin L =>
      (if P (Sched.last (H := h + n) (ℓmax := L) (Fin.append p r)) then schedWeight (H := h + n) (ℓmax := L)
        (Fin.append p r) else 0) * occ M (h + n) (schedPolicy base (Fin.append p r)) τ x a)
      (fun r _ => mul_nonneg (by split_ifs; exacts [schedWeight_nonneg _ _ _, le_rfl])
        (occ_nonneg M hM _ _ τ x a)) (mem_univ (fun _ : Fin n => z)))
    show _ = (if P (Sched.last (H := h + n) (ℓmax := L) (Fin.append p (fun _ : Fin n => z))) then
        schedWeight (H := h + n) (ℓmax := L) (Fin.append p (fun _ : Fin n => z)) else 0) *
        occ M (h + n) (schedPolicy base (Fin.append p (fun _ : Fin n => z))) τ x a
    rw [last_append h n L hn1 (lastL 1 p) p, hlz, if_pos hPℓ, hW p]
    ring
  rw [hL]
  calc ∑ p : Fin h → Fin L, (Wt (h + n) L 1 h p * O p) *
        ∑ r : Fin n → Fin L, (if P (lastL (lastL 1 p) r) then Wt (h + n) L (lastL 1 p) n r else 0)
      ≤ ∑ p : Fin h → Fin L, (Wt (h + n) L 1 h p * O p) *
          (ρ * Wt (h + n) L (lastL 1 p) n (fun _ => z)) := by
        apply Finset.sum_le_sum; intro p _
        exact mul_le_mul_of_nonneg_left (hb _ (hg p).1 (hg p).2) (mul_nonneg (hWp p) (hO0 p))
    _ = ρ * ∑ p : Fin h → Fin L, (Wt (h + n) L 1 h p * O p) *
          Wt (h + n) L (lastL 1 p) n (fun _ => z) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hR hρ

end Occ

section Final
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

theorem ratio_core (M : NominalMDP X A) (hM : M.IsNominal) (h n : ℕ) (hn1 : 1 ≤ n) (L : ℕ)
    (base : ℕ → DetPolicy X A) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L)
    (P : ℕ → Prop) [DecidablePred P] (hPℓ : P ℓ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hb : ∀ g, 1 ≤ g → g ≤ L → ∑ r : Fin n → Fin L, (if P (lastL g r) then Wt (h + n) L g n r else 0) ≤
      ρ * Wt (h + n) L g n (fun _ => (⟨ℓ - 1, by omega⟩ : Fin L))) (τ : ℕ) (x : X) (a : A) :
    ∑ s : Sched (h + n) L, (if P s.last then schedWeight s /
        (∑ s' : Sched (h + n) L, if P s'.last then schedWeight s' else 0) else 0) *
        occ M (h + n) (concat (schedPolicy base s) h (base ℓ)) τ x a ≤
      ρ * ∑ s : Sched (h + n) L, (if P s.last then schedWeight s /
        (∑ s' : Sched (h + n) L, if P s'.last then schedWeight s' else 0) else 0) *
        occ M (h + n) (schedPolicy base s) τ x a := by
  set Q := ∑ s' : Sched (h + n) L, if P s'.last then schedWeight s' else 0
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun s _ => by
    split_ifs; exacts [schedWeight_nonneg _ _ _, le_rfl]
  have e : ∀ F : Sched (h + n) L → ℝ,
      ∑ s : Sched (h + n) L, (if P s.last then schedWeight s / Q else 0) * F s =
        (∑ s : Sched (h + n) L, (if P s.last then schedWeight s else 0) * F s) / Q := by
    intro F
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro s _
    split_ifs <;> ring
  rw [e, e, mul_div_assoc']
  exact div_le_div_of_nonneg_right
    (assembly M hM h n hn1 L base ℓ hℓ1 hℓL P hPℓ ρ hρ hb τ x a) hQ

end Final

end CRRL_L410

open CRRL_L410 in
theorem solution
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (base : ℕ → DetPolicy X A) :
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      HasVisitRatio M H (masterEq H ℓmax base ℓ) (base ℓ) (4 * Real.exp 1 * H * ℓ)) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      HasVisitRatio M H (masterLe H ℓmax base ℓ) (base ℓ) (2 * 2 ^ ℓ * Real.exp 1 * H * ℓ)) ∧
    (∀ C : ℕ, 1 ≤ C → C ≤ 2 ^ ℓmax →
      HasVisitRatio M H (masterLe H ℓmax base (lstar C)) (base (lstar C))
        (4 * Real.exp 1 * C * H * Real.logb 2 (2 * C))) := by
  have he := e_ge_one
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have part1 : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      HasVisitRatio M H (masterEq H ℓmax base ℓ) (base ℓ) (4 * Real.exp 1 * H * ℓ) := by
    intro ℓ hℓ1 hℓL
    have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    refine ⟨by nlinarith [mul_le_mul he hH1 (by norm_num) (by linarith)], ?_⟩
    intro h τ x a hhτ hτ
    obtain ⟨n, rfl⟩ : ∃ n, H = h + n := ⟨H - h, by omega⟩
    exact ratio_core M hM h n (by omega) ℓmax base ℓ hℓ1 hℓL (fun m => m = ℓ) rfl _ (by positivity)
      (fun g hg1 hgL => prefix_eq (h + n) ℓmax hH n (by omega) (by omega) g ℓ hg1 hgL hℓ1 hℓL) τ x a
  have part2 : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      HasVisitRatio M H (masterLe H ℓmax base ℓ) (base ℓ) (2 * 2 ^ ℓ * Real.exp 1 * H * ℓ) := by
    intro ℓ hℓ1 hℓL
    have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    have h2l : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    refine ⟨?_, ?_⟩
    · have a1 : (1 : ℝ) ≤ Real.exp 1 * H := by nlinarith
      have a2 : (1 : ℝ) ≤ Real.exp 1 * H * ℓ := by nlinarith
      nlinarith
    intro h τ x a hhτ hτ
    obtain ⟨n, rfl⟩ : ∃ n, H = h + n := ⟨H - h, by omega⟩
    exact ratio_core M hM h n (by omega) ℓmax base ℓ hℓ1 hℓL (fun m => m ≤ ℓ) le_rfl _ (by positivity)
      (fun g hg1 hgL => prefix_le (h + n) ℓmax hH n (by omega) (by omega) g ℓ hg1 hgL hℓ1 hℓL) τ x a
  refine ⟨part1, part2, ?_⟩
  intro C hC hCℓ
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (2 * C) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    simp; linarith
  have hρ1 : (1 : ℝ) ≤ 4 * Real.exp 1 * C * H * Real.logb 2 (2 * C) := by
    have a1 : (1 : ℝ) ≤ Real.exp 1 * C := by nlinarith
    have a2 : (1 : ℝ) ≤ Real.exp 1 * C * H := by nlinarith
    have a3 : (1 : ℝ) ≤ Real.exp 1 * C * H * Real.logb 2 (2 * C) := by nlinarith
    nlinarith
  rcases Nat.eq_zero_or_pos ℓmax with h0 | hpos
  · subst h0
    refine ⟨hρ1, fun h τ x a _ hτ => ?_⟩
    have hz : ∀ (π : Mixture X A), π.ι = Sched H 0 → True := fun _ _ => trivial
    have empty : ∀ s : Sched H 0, False := fun s => (s ⟨0, by omega⟩).elim0
    have e1 : mixOcc M H (concatMix (masterLe H 0 base (lstar C)) h (base (lstar C))) τ x a = 0 :=
      Finset.sum_eq_zero fun s _ => (empty s).elim
    have e2 : mixOcc M H (masterLe H 0 base (lstar C)) τ x a = 0 :=
      Finset.sum_eq_zero fun s _ => (empty s).elim
    rw [e1, e2, mul_zero]
  · have hl1 : 1 ≤ lstar C := le_max_left _ _
    have hlm : lstar C ≤ ℓmax := max_le hpos (Nat.clog_le_of_le_pow hCℓ)
    obtain ⟨-, h2⟩ := part2 (lstar C) hl1 hlm
    refine ⟨hρ1, fun h τ x a hhτ hτ => le_trans (h2 h τ x a hhτ hτ) ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun s _ =>
      mul_nonneg (by
        show 0 ≤ (if s.last ≤ lstar C then schedWeight s / qLe H ℓmax (lstar C) else 0)
        split_ifs
        · exact div_nonneg (schedWeight_nonneg _ _ _)
            (Finset.sum_nonneg fun s _ => by split_ifs; exacts [schedWeight_nonneg _ _ _, le_rfl])
        · exact le_rfl) (occ_nonneg M hM _ _ τ x a))
    -- `2 · 2^{ℓ⋆} e H ℓ⋆ ≤ 4 e C H log₂(2C)`
    have hpN : 2 ^ (lstar C) ≤ 2 * C := by
      unfold lstar
      rcases le_or_gt (Nat.clog 2 C) 1 with h | h
      · rw [max_eq_left h]; omega
      · rw [max_eq_right h.le]
        have hC2 : 1 < C := by
          by_contra hc
          have : C = 1 := by omega
          subst this
          simp [Nat.clog_one_right] at h
        have := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hC2
        obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 C = k + 1 := ⟨Nat.clog 2 C - 1, by omega⟩
        rw [hk] at this ⊢
        simp only [Nat.pred_succ] at this
        rw [pow_succ]; omega
    have hp : (2 : ℝ) ^ (lstar C) ≤ 2 * C := by exact_mod_cast hpN
    have hl : ((lstar C : ℕ) : ℝ) ≤ Real.logb 2 (2 * C) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
      exact hp
    have hl0 : (0 : ℝ) ≤ (lstar C : ℕ) := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) ≤ 2 ^ (lstar C) := by positivity
    have heH : 0 ≤ Real.exp 1 * H := by positivity
    calc 2 * 2 ^ lstar C * Real.exp 1 * H * (lstar C : ℕ)
        = 2 * (Real.exp 1 * H) * (2 ^ lstar C * (lstar C : ℕ)) := by ring
      _ ≤ 2 * (Real.exp 1 * H) * ((2 * C) * Real.logb 2 (2 * C)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hp hl hl0 (by positivity)
      _ = _ := by ring
