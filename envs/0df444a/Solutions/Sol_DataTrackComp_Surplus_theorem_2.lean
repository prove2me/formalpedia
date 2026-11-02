-- Prove2me | solution 1 for DataTrackComp.Surplus.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:56:45.573551+00:00
-- url     : https://prove2.me/submissions/e71827d7-6e9f-4bce-a79f-dd0380b9e53b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame
import Theorems.Thm_DataTrackComp_Surplus_lemma_2
import Theorems.Thm_DataTrackComp_Surplus_lemma_3_part_1
import Theorems.Thm_DataTrackComp_Surplus_proposition_1
import Theorems.Thm_DataTrackComp_Surplus_proposition_2
import Theorems.Thm_DataTrackComp_Surplus_claim_20
import Theorems.Thm_DataTrackComp_Surplus_claim_23

open DataTrackComp.Surplus

theorem solution (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) (hmL : InInteriorRegime m) :
    (∃ E : Assessment, IsEquilibrium .forward ubar m E) ∧
    (∃ E : Assessment, IsEquilibrium .myopic ubar m E) ∧
    (∃ E : Assessment, IsEquilibrium .restricted ubar m E) ∧
    ∀ EF EM ER : Assessment, IsEquilibrium .forward ubar m EF → IsEquilibrium .myopic ubar m EM →
      IsEquilibrium .restricted ubar m ER →
      consumerSurplus .restricted ubar m ER < consumerSurplus .myopic ubar m EM ∧
      consumerSurplus .restricted ubar m ER < consumerSurplus .forward ubar m EF := by
  obtain ⟨⟨p, hp, -⟩, -⟩ := lemma_3_part_1 m hm hmL
  obtain ⟨EF0, hEF0, -, -⟩ := (lemma_2 ubar m p.1 p.2 hu hm).1 hp
  refine ⟨⟨EF0, hEF0⟩, (proposition_2 ubar m hu hm).1, (proposition_1 ubar m hu hm).1, ?_⟩
  intro EF EM ER hF hM hR
  have h1 := (claim_20 ubar m hu hm).2.2 hmL ER EM hR hM
  have h2 := claim_23 ubar m hu hm hmL EF EM hF hM
  exact ⟨h1, h1.trans h2⟩
