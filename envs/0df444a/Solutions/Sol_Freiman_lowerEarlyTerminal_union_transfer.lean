-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_union_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:51:48.087051+00:00
-- url     : https://prove2.me/submissions/a8817f24-660c-47d7-8def-568a25fb43bf

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.Linarith

open Freiman

lemma compl_of_not (b : CertBound) (r s q : ℝ) (h : ¬ certBoundHolds b r s q) :
    certBoundHolds (lowerHistoryComplement b) r s q := by
  obtain ⟨lo, st, t⟩ := b
  cases lo <;> cases st <;> simp [certBoundHolds, lowerHistoryComplement] at h ⊢ <;> linarith

theorem solution (he : LowerEarlyTerminalEndpointLaw) (hg : LowerEarlyTerminalGreaterLaw)
    (C : LowerEarlyTerminalCatalog) (p : LowerPair) (hm : lowerEarlyTerminalMatches p C)
    (h : ∀ b ∈ lowerEarlyTerminalUnionCases C, lowerEarlyTerminalAt p b.1 →
      section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) :
    lowerEarlyTerminalUnionHolds p := by
  obtain ⟨za, ca, hza, hca, hpa, hea⟩ :=
    he (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm ([2,1,1,2],[3,3]) true
  obtain ⟨zb, cb, hzb, hcb, hpb, heb⟩ :=
    he (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm ([2,1,1,3],[3,3]) false
  obtain ⟨zc, cc, hzc, hcc, hpc, hec⟩ :=
    he (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm ([2],[2]) false
  have hab := hg (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm za zb false hpa hpb
  have hac := hg (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm za zc false hpa hpc
  simp only [Bool.false_eq_true, ↓reduceIte] at hab hac
  have ea : lowerEarlyTerminalEndpoint p ([2,1,1,2],[3,3]) true =
      lowerHistoryValue (lowerNormalize p) (lowerEarlyTerminalContext C) za := hea
  have eb : lowerEarlyTerminalEndpoint p ([2,1,1,3],[3,3]) false =
      lowerHistoryValue (lowerNormalize p) (lowerEarlyTerminalContext C) zb := heb
  have ec : lowerEarlyTerminalEndpoint p ([2],[2]) false =
      lowerHistoryValue (lowerNormalize p) (lowerEarlyTerminalContext C) zc := hec
  unfold lowerEarlyTerminalUnionHolds
  rw [ea, eb, ec]
  have hh := h _ (by
    unfold lowerEarlyTerminalUnionCases
    exact List.mem_flatMap.2 ⟨(za, ca), hza, List.mem_flatMap.2 ⟨(zb, cb), hzb,
      List.mem_map.2 ⟨(zc, cc), hzc, rfl⟩⟩⟩)
  dsimp only at hh
  have hcs : lowerEarlyTerminalAt p (ca ++ cb ++ cc) := by
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact hca b hb
    · exact hcb b hb
    · exact hcc b hb
  rcases hga : lowerEarlyTerminalGreater za zb false with _ | _ | f <;>
  rcases hgc : lowerEarlyTerminalGreater za zc false with _ | _ | g <;>
  simp only [hga, hgc, section14ComparisonHolds, true_iff, false_iff] at hh hab hac
  · exact Or.inl hab
  · exact Or.inl hab
  · exact Or.inl hab
  · exact Or.inr hac
  · exact (hh hcs).elim
  · exact Or.inr (hac.1 (hh hcs))
  · exact Or.inr hac
  · exact Or.inl (hab.1 (hh hcs))
  · by_cases hf : certBoundHolds f (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)
    · exact Or.inl (hab.1 hf)
    · have hcs' : lowerEarlyTerminalAt p (lowerHistoryComplement f :: (ca ++ cb ++ cc)) := by
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact compl_of_not _ _ _ _ hf
        · exact hcs b hb
      exact Or.inr (hac.1 (hh hcs'))
