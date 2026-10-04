-- Prove2me | solution 1 for BJNAdAuctions.Basic.primal_dual_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:43:11.460472+00:00
-- url     : https://prove2.me/submissions/9a1cb609-605f-4675-a62b-c7ad7f2ac11d

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

set_option autoImplicit false

namespace BJNAdAuctions.Basic.PDRatioAux

open BJNAdAuctions.Basic

theorem sum_mul_update {α : Type*} [Fintype α] [DecidableEq α] (w f : α → ℝ) (a : α) (v : ℝ) :
    ∑ i, w i * Function.update f a v i = ∑ i, w i * f i + w a * (v - f a) := by
  have h : ∀ i, w i * Function.update f a v i
      = w i * f i + (if i = a then w a * (v - f a) else 0) := by
    intro i
    by_cases hi : i = a
    · subst hi; simp; ring
    · simp [hi]
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_update {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (a : α) (v : ℝ) :
    ∑ i, Function.update f a v i = ∑ i, f i + (v - f a) := by
  have := sum_mul_update (fun _ => (1:ℝ)) f a v
  simpa using this

theorem sum_sum_update {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (b y : I → Fin m → ℝ) (i : I) (j : Fin m) :
    ∑ j', ∑ i', b i' j' * Function.update y i (Function.update (y i) j 1) i' j'
      = ∑ j', ∑ i', b i' j' * y i' j' + b i j * (1 - y i j) := by
  have h : ∀ j' i', b i' j' * Function.update y i (Function.update (y i) j 1) i' j'
      = b i' j' * y i' j' + (if j' = j then (if i' = i then b i j * (1 - y i j) else 0) else 0) := by
    intro j' i'
    by_cases hi : i' = i
    · subst hi
      by_cases hj : j' = j
      · subst hj; simp; ring
      · simp [hj]
    · simp [hi]
  simp_rw [h, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

open Classical in
theorem step_ratio {I : Type*} [Fintype I] {m : ℕ} (inst : Instance I m)
    (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I) (s : State I m) (j : Fin m)
    (hz : s.z j = 0) (hy : ∀ i, s.y i j = 0)
    (hinv : coveringValue inst s.x s.z = (1 + 1 / (c - 1)) * packingValue inst s.y) :
    coveringValue inst (step inst c sel s j).x (step inst c sel s j).z =
      (1 + 1 / (c - 1)) * packingValue inst (step inst c sel s j).y := by
  dsimp only [step]
  split_ifs with h
  · exact hinv
  · simp only [coveringValue, packingValue] at hinv ⊢
    rw [sum_mul_update, sum_update, sum_sum_update, hz, hy]
    have hB : inst.B (sel s.x j) ≠ 0 := (inst.B_pos _).ne'
    have hc1 : c - 1 ≠ 0 := by linarith
    have key : inst.B (sel s.x j) * (s.x (sel s.x j) * (1 + inst.b (sel s.x j) j / inst.B (sel s.x j))
        + inst.b (sel s.x j) j / ((c - 1) * inst.B (sel s.x j)) - s.x (sel s.x j))
        + (inst.b (sel s.x j) j * (1 - s.x (sel s.x j)) - 0)
        = (1 + 1 / (c - 1)) * (inst.b (sel s.x j) j * (1 - 0)) := by
      field_simp
      ring
    linear_combination hinv + key

open Classical in
theorem prefix_inv {I : Type*} [Fintype I] {m : ℕ} (inst : Instance I m)
    (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I) :
    ∀ k, k ≤ m →
      (∀ j : Fin m, k ≤ j.val → (runPrefix inst c sel k).z j = 0 ∧
          ∀ i, (runPrefix inst c sel k).y i j = 0) ∧
      coveringValue inst (runPrefix inst c sel k).x (runPrefix inst c sel k).z =
        (1 + 1 / (c - 1)) * packingValue inst (runPrefix inst c sel k).y := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun j _ => ⟨rfl, fun i => rfl⟩, ?_⟩
    simp [runPrefix, State.init, coveringValue, packingValue]
  | succ k ih =>
    intro hk
    have hkm : k < m := by omega
    obtain ⟨hcol, hinv⟩ := ih (by omega)
    have hrun : runPrefix inst c sel (k + 1) = step inst c sel (runPrefix inst c sel k) ⟨k, hkm⟩ := by
      rw [runPrefix, dif_pos hkm]
    rw [hrun]
    obtain ⟨hz, hy⟩ := hcol ⟨k, hkm⟩ le_rfl
    refine ⟨?_, step_ratio inst c hc sel _ _ hz hy hinv⟩
    intro j hj
    have hne : j ≠ ⟨k, hkm⟩ := by
      intro h; rw [h] at hj; simp at hj
    obtain ⟨hz', hy'⟩ := hcol j (by omega)
    dsimp only [step]
    split_ifs with h
    · exact ⟨hz', hy'⟩
    · refine ⟨?_, ?_⟩
      · simp [Function.update, hne, hz']
      · intro i
        by_cases hi : i = sel (runPrefix inst c sel k).x ⟨k, hkm⟩
        · subst hi; simp [Function.update, hne, hy']
        · simp [Function.update, hi, hy']

end BJNAdAuctions.Basic.PDRatioAux

open BJNAdAuctions.Basic in
theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I) :
    coveringValue inst (run inst c sel).x (run inst c sel).z =
      (1 + 1 / (c - 1)) * packingValue inst (run inst c sel).y := by
  exact (BJNAdAuctions.Basic.PDRatioAux.prefix_inv inst c hc sel m le_rfl).2
