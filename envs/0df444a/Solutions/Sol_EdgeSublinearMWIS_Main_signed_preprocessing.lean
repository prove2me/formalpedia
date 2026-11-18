-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.signed_preprocessing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:09:27.445293+00:00
-- url     : https://prove2.me/submissions/e8e0d3c1-35cc-4ac6-8a2a-c3e17e922fe9

import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

open scoped BigOperators
open EdgeSublinearMWIS.Main

set_option autoImplicit false

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    weightedAlphaOn G (Finset.univ.filter (fun v => 0 ≤ w v)) w = weightedAlpha G w := by
  classical
  unfold weightedAlpha weightedAlphaOn
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨I, hI, hind, rfl⟩
    exact ⟨_, ⟨I, Finset.subset_univ _, hind, rfl⟩, le_rfl⟩
  · rintro y ⟨I, hI, hind, rfl⟩
    let J := I.filter (fun v => 0 ≤ w v)
    refine ⟨∑ v ∈ J, (w v : ℝ), ⟨J, ?_, ?_, rfl⟩, ?_⟩
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
    · exact hind.mono (by intro v hv; exact (Finset.mem_filter.mp hv).1)
    · change (∑ v ∈ I, (w v : ℝ)) ≤ ∑ v ∈ I.filter (fun v => 0 ≤ w v), (w v : ℝ)
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro v hv
      split_ifs with h
      · exact le_rfl
      · exact_mod_cast le_of_lt (lt_of_not_ge h)
