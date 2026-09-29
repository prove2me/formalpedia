-- Prove2me | solution 1 for Freiman.lowerHistory_row2_certificate_case_02
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:50:51.442032+00:00
-- url     : https://prove2.me/submissions/4e55d5ce-ec8c-4686-a579-809cd5869b41

import Theorems.Thm_Freiman_lowerHistory_row2_source_case_02
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_04
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem close_negative
    (B : ℕ → CertBound) (R : ℕ → CertRectangle)
    (paths : List LowerHistoryPath) (sources : List (List ℕ))
    (ris : List ℕ) (pairs : List (ℕ × ℕ × ℕ))
    (hrect : paths.map (fun p => p.rectangle) = ris.map R)
    (hsource : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ paths →
      LowerHistorySourceEvents base p →
      ∃ bs ∈ sources.map (fun cs => cs.map B), lowerHistoryAtBase base bs)
    (hex : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (R a.1) r s →
      ¬ (certBoundHolds (B a.2.1) r s q ∧ certBoundHolds (B a.2.2) r s q))
    (hcovered : ∀ ri ∈ ris, ∀ cs ∈ sources,
      ∃ a ∈ pairs, a.1 = ri ∧ a.2.1 ∈ cs ∧ a.2.2 ∈ cs) :
    ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ paths →
      LowerHistorySourceEvents base p →
      certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) → False := by
  intro base p hp he hr
  obtain ⟨bs,hbs,hs⟩ := hsource base p hp he
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hbs
  have hm : p.rectangle ∈ ris.map R := by
    rw [← hrect]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  obtain ⟨ri,hri,hR⟩ := List.mem_map.mp hm
  obtain ⟨a,ha,har,hlo,hhi⟩ := hcovered ri hri cs hcs
  apply hex a ha (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)
  · rw [har,hR]
    exact hr
  · exact ⟨hs (B a.2.1) (List.mem_map.mpr ⟨a.2.1,hlo,rfl⟩),
      hs (B a.2.2) (List.mem_map.mpr ⟨a.2.2,hhi,rfl⟩)⟩
private def rectangle (i : ℕ) : CertRectangle := lowerHistoryRectangles[i]?.getD ⟨0,1,0,1⟩
private def paths : List LowerHistoryPath := [lowerHistoryPathsR[1],lowerHistoryPathsR[16],lowerHistoryPathsR[31],lowerHistoryPathsR[46],lowerHistoryPathsR[61],lowerHistoryPathsR[76]]
private def codes : List (List ℕ) := [[275,442,371,843,260,440,856,817,250,817]]
private def ris : List ℕ := [5,4,1,6,2,7]
private def pairs : List (ℕ × ℕ × ℕ) := [(5,440,1149),(6,440,1149),(7,440,1149),(1,440,1153),(2,440,1153),(4,440,1153),(5,440,1153),(6,440,1153),(7,440,1153),(1,442,817),(2,442,817),(4,442,817),(5,442,817),(6,442,817),(7,442,817)]
private theorem rectangles : paths.map (fun p => p.rectangle) = ris.map rectangle := by rfl
private theorem coverage : ∀ ri ∈ ris, ∀ cs ∈ codes, ∃ a ∈ pairs, a.1=ri ∧ a.2.1∈cs ∧ a.2.2∈cs := by decide
private theorem excluded : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (rectangle a.1) r s → ¬(certBoundHolds (lowerHistoryBound a.2.1) r s q ∧ certBoundHolds (lowerHistoryBound a.2.2) r s q) := Freiman.lowerHistory_row2_exclusions_04
theorem solution : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[1],lowerHistoryPathsR[16],lowerHistoryPathsR[31],lowerHistoryPathsR[46],lowerHistoryPathsR[61],lowerHistoryPathsR[76]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  False := by
  exact close_negative lowerHistoryBound rectangle paths codes ris pairs rectangles
    Freiman.lowerHistory_row2_source_case_02 excluded coverage
#print axioms solution
