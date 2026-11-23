-- Prove2me | solution 1 for DelaunayStretch.theorem_3_9_potential_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:43:43.332552+00:00
-- url     : https://prove2.me/submissions/2e61252b-5f6c-4225-83d3-9e60197baf0b

import Definitions.Def_DelaunayStretch_IsFeasiblePotential
import Theorems.Thm_DelaunayStretch_lemma_2_3_one_disk
import Theorems.Thm_DelaunayStretch_lemma_3_6_chains_are_moves


open DelaunayStretch

theorem telescope_Ico (f : ℕ → ℝ) (a b : ℕ) (h : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (f i - f (i + 1)) = f a - f b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ k hk ih => rw [Finset.sum_Ico_succ_top hk, ih]; ring

theorem solution (U : ℝ) (hU : Real.pi / 2 ≤ U)
    (hW : ∃ W : GateState → ℝ, IsFeasiblePotential U W) : ChainInequality U := by
  obtain ⟨W, hI, hS, hF⟩ := hW
  intro C hC
  rcases Nat.lt_or_ge C.n 2 with hn | hn
  · have h1 : C.n = 1 := by have := hC.1; omega
    exact (lemma_2_3_one_disk).2.2.2 U hU C hC h1
  · have L := lemma_3_6_chains_are_moves C hC hn
    simp only at L
    obtain ⟨⟨hgs, hip, hinit, hstep, -⟩, -, hsum⟩ := L
    set s : ℕ → GateState := fun i => ⟨C.O (i + 1), C.a i, C.b i, C.delta i⟩ with hs_def
    rw [← sub_nonpos, hsum U]
    have e1 := hI _ _ _ _ hip
    rw [hinit] at e1
    have eF := hF (s (C.n - 1)) (hgs (C.n - 1) (by omega) (by omega))
    have eS : ∀ i ∈ Finset.Ico 1 (C.n - 1),
        stepCost (s i) (C.a (i + 1)) (C.b (i + 1)) -
            U * stepProgress (s i) (C.a (i + 1)) (C.b (i + 1)) ≤ W (s i) - W (s (i + 1)) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      obtain ⟨hnd, hst⟩ := hstep i hi.1 (by omega)
      have := hS (s i) (hgs i hi.1 (by omega)) _ _ _ hnd
      rwa [hst] at this
    have hsumle := Finset.sum_le_sum eS
    have htel : ∑ i ∈ Finset.Ico 1 (C.n - 1), (W (s i) - W (s (i + 1))) =
        W (s 1) - W (s (C.n - 1)) := by
      exact telescope_Ico (fun i => W (s i)) 1 (C.n - 1) (by omega)
    linarith
