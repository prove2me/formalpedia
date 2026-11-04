-- Prove2me | solution 1 for CorruptRobustRL.Supervised.lemma4_7_bellman_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:03:40.883441+00:00
-- url     : https://prove2.me/submissions/5dd3ac2b-3a3c-409d-b21d-ca0ae13082ed

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

open CorruptRobustRL.Supervised
open Finset QSupervisor

namespace CRRL_L47

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

theorem Vbar_eq (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (h : ℕ) (hh : h < H) (x : X) :
    Vbar H (ucbviSup H act gl sb sel) (h + 1) x = (ucbviVals H act gl sb sel (H - (h + 1))).1 x := by
  unfold Vbar
  split_ifs with h1
  · rw [show H - (h + 1) = (H - (h + 1 + 1)) + 1 by omega, ucbviVals]
    simp only [ucbviSup]
    rw [show H - (H - (h + 1 + 1) + 1) = h + 1 by omega]
  · rw [show H - (h + 1) = 0 by omega]; rfl

theorem Vlow_eq (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (h : ℕ) (hh : h < H) (x : X) :
    Vlow H (ucbviSup H act gl sb sel) (h + 1) x = (ucbviVals H act gl sb sel (H - (h + 1))).2 x := by
  unfold Vlow
  by_cases h1 : h + 1 < H
  · rw [if_pos h1]
    rw [show H - (h + 1) = (H - (h + 1 + 1)) + 1 by omega, ucbviVals]
    simp only [ucbviSup]
    rw [show H - (H - (h + 1 + 1) + 1) = h + 1 by omega]
    unfold CorruptRobustRL.Supervised.maxOn
    rfl
  · rw [if_neg h1, show H - (h + 1) = 0 by omega]; rfl

theorem one_model (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ)
    (m : ModelEst X A) (r b : X → A → ℝ) (V W Vs : X → ℝ) (x : X) (a : A)
    (Qb Ql : ℝ) (hQbH : Qb ≤ H) (hQb : Qb ≤ backup m V x a + m.b x a)
    (hQl0 : 0 ≤ Ql) (hQl : backup m W x a - m.b x a ≤ Ql)
    (hV0 : ∀ y, 0 ≤ V y) (hWH : ∀ y, W y ≤ H) (hdev : |m.dev M Vs x a| ≤ m.b x a) :
    max (Qb - (M.rstar x a + ∑ x', M.pstar x a x' * V x'))
        ((Qb - (M.rstar x a + ∑ x', M.pstar x a x' * V x')) -
          (Ql - (M.rstar x a + ∑ x', M.pstar x a x' * W x'))) ≤
      min (3 * (H : ℝ)) (2 * m.b x a +
        max (∑ x', (m.p x a x' - M.pstar x a x') * (V x' - Vs x'))
            (∑ x', (m.p x a x' - M.pstar x a x') * (V x' - W x'))) := by
  obtain ⟨-, hP, hR⟩ := hM
  obtain ⟨hp0, hp1⟩ := hP x a
  have hr0 := (hR x a).1
  have hPV : 0 ≤ ∑ x', M.pstar x a x' * V x' :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hp0 y) (hV0 y)
  have hPW : ∑ x', M.pstar x a x' * W x' ≤ H := by
    have : ∑ x', M.pstar x a x' * W x' ≤ ∑ x', M.pstar x a x' * (H : ℝ) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hWH y) (hp0 y)
    rwa [← Finset.sum_mul, hp1, one_mul] at this
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hd := (abs_le.mp hdev).2
  unfold ModelEst.dev at hd
  unfold backup at hQb hQl
  have e1 : ∑ x', (m.p x a x' - M.pstar x a x') * (V x' - Vs x') =
      ∑ x', m.p x a x' * V x' - ∑ x', M.pstar x a x' * V x' -
        ∑ x', (m.p x a x' - M.pstar x a x') * Vs x' := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e2 : ∑ x', (m.p x a x' - M.pstar x a x') * (V x' - W x') =
      ∑ x', m.p x a x' * V x' - ∑ x', M.pstar x a x' * V x' -
        (∑ x', m.p x a x' * W x' - ∑ x', M.pstar x a x' * W x') := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  refine le_min (max_le (by linarith) (by linarith)) (max_le ?_ ?_)
  · refine le_trans ?_ (add_le_add_right (le_max_left _ _) _)
    rw [e1]; linarith
  · refine le_trans ?_ (add_le_add_right (le_max_right _ _) _)
    rw [e2]; linarith

end CRRL_L47

open CRRL_L47 in
theorem solution
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (T : QSupervisor X A) (hTdef : T = ucbviSup H act gl sb sel)
    (hgl : gl.IsModelEst H) (hsb : sb.IsModelEst H)
    (hvgl : gl.IsValid M H T) (hvsb : sb.IsValid M H T) :
    ∀ h < H, ∀ x a,
      max (upperBell M H T h x a) (upperBell M H T h x a - lowerBell M H T h x a) ≤
          min (3 * (H : ℝ)) (2 * gl.b x a +
            max (∑ x', (gl.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vstar M H (h + 1) x'))
                (∑ x', (gl.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vlow H T (h + 1) x'))) ∧
      max (upperBell M H T h x a) (upperBell M H T h x a - lowerBell M H T h x a) ≤
          min (3 * (H : ℝ)) (2 * sb.b x a +
            max (∑ x', (sb.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vstar M H (h + 1) x'))
                (∑ x', (sb.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vlow H T (h + 1) x'))) := by
  intro h hh x a
  have dgl : |gl.dev M (Vstar M H (h + 1)) x a| ≤ gl.b x a := by
    rcases hvgl h hh x a with h1 | h1
    · exact h1.2
    · exact h1.1
  have dsb : |sb.dev M (Vstar M H (h + 1)) x a| ≤ sb.b x a := by
    rcases hvsb h hh x a with h1 | h1
    · exact h1.2
    · exact h1.1
  subst hTdef
  have hVb : ∀ y, Vbar H (ucbviSup H act gl sb sel) (h + 1) y =
      (ucbviVals H act gl sb sel (H - (h + 1))).1 y := fun y => Vbar_eq H act gl sb sel h hh y
  have hVl : ∀ y, Vlow H (ucbviSup H act gl sb sel) (h + 1) y =
      (ucbviVals H act gl sb sel (H - (h + 1))).2 y := fun y => Vlow_eq H act gl sb sel h hh y
  have hb := vals_bounds H act gl sb sel hgl hsb (H - (h + 1))
  simp only [upperBell, lowerBell, hVb, hVl]
  set V := (ucbviVals H act gl sb sel (H - (h + 1))).1
  set W := (ucbviVals H act gl sb sel (H - (h + 1))).2
  have hV0 : ∀ y, 0 ≤ V y := fun y => (hb y).1.1
  have hWH : ∀ y, W y ≤ H := fun y => le_trans (hb y).2.2 (by exact_mod_cast Nat.sub_le _ _)
  have hQbH : (ucbviSup H act gl sb sel).Qbar h x a ≤ H := min_le_left _ _
  have hQl0 : 0 ≤ (ucbviSup H act gl sb sel).Qlow h x a := le_max_left _ _
  have hQb1 : (ucbviSup H act gl sb sel).Qbar h x a ≤ backup gl V x a + gl.b x a :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hQb2 : (ucbviSup H act gl sb sel).Qbar h x a ≤ backup sb V x a + sb.b x a :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hQl1 : backup gl W x a - gl.b x a ≤ (ucbviSup H act gl sb sel).Qlow h x a :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hQl2 : backup sb W x a - sb.b x a ≤ (ucbviSup H act gl sb sel).Qlow h x a :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  exact ⟨one_model M hM H gl gl.r gl.b V W _ x a _ _ hQbH hQb1 hQl0 hQl1 hV0 hWH dgl,
    one_model M hM H sb sb.r sb.b V W _ x a _ _ hQbH hQb2 hQl0 hQl2 hV0 hWH dsb⟩
