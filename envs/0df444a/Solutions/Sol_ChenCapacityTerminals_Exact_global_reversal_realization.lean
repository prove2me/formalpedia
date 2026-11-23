-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.global_reversal_realization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T06:12:21.476175+00:00
-- url     : https://prove2.me/submissions/d3f6211a-4986-42d3-b858-04227dae7484
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ChenCapacityTerminals_Exact_CandidateReduction
import Theorems.Thm_ChenCapacityTerminals_Exact_global_candidate_optimal
import Theorems.Thm_ChenCapacityTerminals_Exact_global_candidate_machine_realization

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution
    (P : WordProgram) (hP : RootedHeadlineReduction P) :
    ∃ Q : WordProgram, HeadlineReduction Q := by
  classical
  obtain ⟨Q, hQ⟩ := global_candidate_machine_realization P hP
  refine ⟨Q, hQ.1, ?_⟩
  intro p q
  obtain ⟨B, C, k, hB, hC, hQ⟩ := hQ.2 p q
  refine ⟨B, C, k, hB, hC, ?_⟩
  intro G mode hG hmode hpoly W hW O hO
  obtain ⟨time, trace, out, hrun, houtput, hvol, htime, hlen, hsize⟩ :=
    hQ G mode hG hmode hpoly W hW O hO
  have hn : 2 ≤ G.n := hG.1
  have hGV : G.network.Valid := by
    intro e he
    simp only [IntegerInput.network, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have h := hG.2 e0 he0
    exact ⟨by simpa only [IntegerInput.network, Finset.mem_range] using h.1,
      by simpa only [IntegerInput.network, Finset.mem_range] using h.2, by positivity⟩
  have hzero : (0 : ℕ) ∈ G.network.vertices := by
    simp only [IntegerInput.network, Finset.mem_range]
    omega
  have hWone : 1 ≤ W := by
    calc
      1 = 1 * 1 := by omega
      _ ≤ B * (Nat.log2 G.n + 1) := Nat.mul_le_mul hB (by omega)
      _ ≤ W := hW
  have hone : 1 < (2 : ℕ) ^ W := Nat.one_lt_two_pow (by omega)
  have hcorrect : WordOutput G mode out := by
    cases mode with
    | some r => exact houtput
    | none =>
        obtain ⟨X, Y, hX, hY, hm⟩ := houtput
        have hopt := global_candidate_optimal G.network 0 hzero hGV X Y hX hY
        let X' := if cut G.network X ≤ cut G.network (G.network.vertices \ Y)
          then X else G.network.vertices \ Y
        refine ⟨?_, ?_⟩
        · intro v hv
          rw [hm]
          by_cases h : v ∈ X' <;> simp [X', h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hone]
        · simp only [CorrectShore]
          have hshore : wordShore out ((inputWords G none).length) G.n = X' := by
            ext v
            simp only [wordShore, Finset.mem_filter, Finset.mem_range]
            by_cases hv : v < G.n
            · simp only [hv, true_and]
              rw [hm]
              by_cases h : v ∈ X' <;>
                simp [X', h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hone]
            · have hnot : v ∉ X' := by
                intro hmem
                have hsub : X' ⊆ G.network.vertices := by
                  dsimp [X']
                  split_ifs
                  · exact hX.1.1
                  · exact Finset.sdiff_subset
                have := hsub hmem
                simp only [IntegerInput.network, Finset.mem_range] at this
                omega
              simp [hv, hnot]
          rw [hshore]
          exact hopt
  exact ⟨time, trace, out, hrun, hcorrect, hvol, htime, hlen, hsize⟩
