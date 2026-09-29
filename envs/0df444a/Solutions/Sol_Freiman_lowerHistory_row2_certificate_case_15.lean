-- Prove2me | solution 1 for Freiman.lowerHistory_row2_certificate_case_15
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:52:20.521913+00:00
-- url     : https://prove2.me/submissions/8964041e-2d56-40ea-9c1a-7c803f5b3742

import Theorems.Thm_Freiman_lowerHistory_row2_source_case_15
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_01
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
private def paths : List LowerHistoryPath := [lowerHistoryPathsR[14],lowerHistoryPathsR[29],lowerHistoryPathsR[44],lowerHistoryPathsR[59],lowerHistoryPathsR[74],lowerHistoryPathsR[89]]
private def codes : List (List ℕ) := [[371,843,260,440,293,867,851,274,851]]
private def ris : List ℕ := [5,4,1,6,2,7]
private def pairs : List (ℕ × ℕ × ℕ) := [(1,287,769),(2,287,769),(4,287,769),(5,287,769),(6,287,769),(7,287,769),(1,291,887),(2,291,887),(4,291,887),(5,291,887),(1,291,900),(2,291,900),(4,291,900),(5,291,900),(6,291,905),(7,291,905),(1,291,1167),(2,291,1167),(4,291,1167),(5,291,1167),(1,293,843),(2,293,843),(4,293,843),(5,293,843),(6,293,843),(7,293,843),(1,294,890),(2,294,890),(4,294,890),(5,294,890),(1,294,902),(2,294,902),(4,294,902),(5,294,902),(6,294,903),(7,294,903),(1,294,1166),(2,294,1166),(4,294,1166),(5,294,1166),(1,429,880),(2,429,880),(4,429,880),(5,429,880),(1,429,885),(2,429,885),(4,429,885),(5,429,885),(1,429,889),(2,429,889)]
private theorem rectangles : paths.map (fun p => p.rectangle) = ris.map rectangle := by rfl
private theorem coverage : ∀ ri ∈ ris, ∀ cs ∈ codes, ∃ a ∈ pairs, a.1=ri ∧ a.2.1∈cs ∧ a.2.2∈cs := by decide
private theorem excluded : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (rectangle a.1) r s → ¬(certBoundHolds (lowerHistoryBound a.2.1) r s q ∧ certBoundHolds (lowerHistoryBound a.2.2) r s q) := Freiman.lowerHistory_row2_exclusions_01
theorem solution : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[14],lowerHistoryPathsR[29],lowerHistoryPathsR[44],lowerHistoryPathsR[59],lowerHistoryPathsR[74],lowerHistoryPathsR[89]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  False := by
  exact close_negative lowerHistoryBound rectangle paths codes ris pairs rectangles
    Freiman.lowerHistory_row2_source_case_15 excluded coverage
#print axioms solution
