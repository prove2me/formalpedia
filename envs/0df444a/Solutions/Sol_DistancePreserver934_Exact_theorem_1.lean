-- Prove2me | solution 1 for DistancePreserver934.Exact.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:52:40.425193+00:00
-- url     : https://prove2.me/submissions/24555fe5-1375-493f-948d-58363eea6ff4

import Theorems.Thm_DistancePreserver934_Exact_equation_26

open Classical
open DistancePreserver934.Exact

set_option autoImplicit false

private lemma minimal_exists {V : Type} [Fintype V] (G : SimpleGraph V)
    (R : Finset (Sym2 V)) : ∃ H, IsMinimalPreserver G H R := by
  obtain ⟨H, hH, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun H : SimpleGraph V => IsPreserver G H R) ⟨G, le_rfl, by simp⟩
  refine ⟨H, hH, ?_⟩
  intro e he hdel
  have heq : H = H.deleteEdges {e} := le_antisymm
    (hmin hdel (H.deleteEdges_le _)) (H.deleteEdges_le _)
  have : e ∈ (H.deleteEdges {e}).edgeSet := heq ▸ he
  simpa [SimpleGraph.edgeSet_deleteEdges] using this


theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (P : Finset (V × V)),
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2) ≤ (P.card : ℝ) → (P.card : ℝ) ≤ (Fintype.card V : ℝ) →
      ∃ H : SimpleGraph V, H ≤ G ∧ (∀ st ∈ P, H.edist st.1 st.2 = G.edist st.1 st.2) ∧
        (numEdges H : ℝ) ≤
          C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * (P.card : ℝ) ^ ((4 : ℝ) / 9) := by
  obtain ⟨C, hC, hbound⟩ := DistancePreserver934.Exact.equation_26
  refine ⟨C, hC, ?_⟩
  intro V inst G P hlo hhi
  classical
  let R := P.image (fun st => s(st.1, st.2))
  have hcard : R.card ≤ P.card := Finset.card_image_le
  have hpc : P.card ≤ Fintype.card V := by exact_mod_cast hhi
  have hsym : Fintype.card V ≤ Fintype.card (Sym2 V) :=
    Fintype.card_le_of_injective Sym2.diag Sym2.diag_injective
  obtain ⟨T, hRT, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ R) hcard (by simpa using hpc.trans hsym)
  obtain ⟨H, hH⟩ := minimal_exists G T
  refine ⟨H, hH.1.1, ?_, ?_⟩
  · intro st hst
    exact hH.1.2 st.1 st.2 (hRT (Finset.mem_image.mpr ⟨st, hst, rfl⟩))
  · have hquarter : (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ (P.card : ℝ) := by
      by_cases hz : Fintype.card V = 0
      · simp [hz, Real.zero_rpow] at *
      · exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz)
          (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2)).trans hlo
    simpa [hT] using hbound V G H T (by simpa [hT] using hquarter)
      (by simpa [hT] using hhi) hH
