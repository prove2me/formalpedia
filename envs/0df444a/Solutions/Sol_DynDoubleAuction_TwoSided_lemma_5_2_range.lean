-- Prove2me | solution 1 for DynDoubleAuction.TwoSided.lemma_5_2_range
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:22:08.058187+00:00
-- url     : https://prove2.me/submissions/f7910c64-ee45-4116-9d9c-b519fd99e6c1

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided
open MeasureTheory Filter Topology

lemma rule_u_med {n : ℕ} (M : Market n) (T t : ℕ) (w v : Fin (n + 1) → ℝ)
    (h : Medium M T t (w 0)) :
    (rule M T t w v).u = fun i => w i + max (maxBuyer v - v 0) 0 - wlow M := by
  simp [rule, h]

lemma rule_u_nmed {n : ℕ} (M : Market n) (T t : ℕ) (w v : Fin (n + 1) → ℝ)
    (h : ¬ Medium M T t (w 0)) :
    (rule M T t w v).u = fun i => max (w i - mu M) 0 := by
  simp [rule, h]

lemma maxBuyer_bounds {n : ℕ} (hn : 1 ≤ n) (vbar : ℝ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 vbar) : 0 ≤ maxBuyer v ∧ maxBuyer v ≤ vbar := by
  classical
  have hne : (Finset.univ.erase (0 : Fin (n + 1))).Nonempty :=
    ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  unfold maxBuyer
  simp only [hne, dite_true]
  constructor
  · obtain ⟨i, hi⟩ := hne
    exact le_trans (hv i).1 (Finset.le_sup' v hi)
  · exact Finset.sup'_le _ _ (fun i _ => (hv i).2)

end DynDoubleAuction.TwoSided

open DynDoubleAuction.TwoSided in
theorem solution {n : ℕ} (M : Market n) (hM : Standing M)
    (T : ℕ) (w1 : ℝ) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1)
    (vs : ℕ → Fin (n + 1) → ℝ)
    (hvs : ∀ k j, vs k j ∈ Set.Icc 0 M.vbar) :
    ∀ k ≤ T, ∀ j : Fin (n + 1),
      0 ≤ state M T w1 vs k j ∧
      state M T w1 vs k j ≤ wbar M T (k + 1) ∧
      state M T w1 vs k j = state M T w1 vs k 0 := by
  obtain ⟨hn, -, hvb, -, -, -, -, -, hmw, hmu⟩ := hM
  intro k
  induction k with
  | zero =>
    intro _ j
    simp only [state]
    exact ⟨hw1.1, by simpa using hw1.2, trivial⟩
  | succ k ih =>
    intro hk j
    have ih' := ih (by omega)
    have hwb : wbar M T (k + 1 + 1) = wbar M T (k + 1) - mu M := by
      simp only [wbar]; push_cast; ring
    have hwb0 : 0 ≤ wbar M T (k + 1 + 1) := by
      simp only [wbar]
      apply mul_nonneg _ hmu.le
      have : ((k:ℝ) + 1) ≤ T := by exact_mod_cast hk
      push_cast; linarith
    obtain ⟨hB0, hB1⟩ := maxBuyer_bounds hn M.vbar (vs k) (hvs k)
    have h00 := hvs k 0
    have hX0 : 0 ≤ max (maxBuyer (vs k) - vs k 0) 0 := le_max_right _ _
    have hX1 : max (maxBuyer (vs k) - vs k 0) 0 ≤ M.vbar :=
      max_le (by linarith [h00.1]) hvb.le
    show 0 ≤ (rule M T (k + 1) (state M T w1 vs k) (vs k)).u j ∧
      (rule M T (k + 1) (state M T w1 vs k) (vs k)).u j ≤ wbar M T (k + 1 + 1) ∧
      (rule M T (k + 1) (state M T w1 vs k) (vs k)).u j =
        (rule M T (k + 1) (state M T w1 vs k) (vs k)).u 0
    obtain ⟨a0, a1, a2⟩ := ih' j
    by_cases hmed : Medium M T (k + 1) (state M T w1 vs k 0)
    · rw [rule_u_med M T (k + 1) _ _ hmed]
      simp only
      obtain ⟨m1, m2⟩ := hmed
      rw [a2]
      refine ⟨by linarith, ?_, rfl⟩
      rw [hwb]; linarith
    · rw [rule_u_nmed M T (k + 1) _ _ hmed]
      simp only
      rw [a2]
      refine ⟨le_max_right _ _, ?_, rfl⟩
      rw [hwb]
      exact max_le (by linarith [(ih' 0).2.1]) (by linarith)
