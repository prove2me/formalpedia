-- Prove2me | solution 1 for Freiman.lowerHistory_row2_certificate_case_19
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:52:56.068113+00:00
-- url     : https://prove2.me/submissions/c7559fa0-d16f-49b4-b858-ce876a1252f4

import Theorems.Thm_Freiman_lowerHistory_row2_source_case_19
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_02
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
private def paths : List LowerHistoryPath := [lowerHistoryPathsH[39]]
private def codes : List (List ℕ) := [[799,1140,1115,1108,371,843,433,1162,839,434,832,830,150,830]]
private def ris : List ℕ := [3]
private def pairs : List (ℕ × ℕ × ℕ) := [(4,429,889),(5,429,889),(1,429,1149),(2,429,1149),(4,429,1149),(5,429,1149),(0,433,447),(3,433,447),(0,433,449),(3,433,449),(0,433,450),(3,433,450),(0,433,455),(3,433,455),(0,433,456),(3,433,456),(3,433,830),(0,433,839),(3,433,839),(1,436,836),(2,436,836),(4,436,836),(5,436,836),(1,436,884),(2,436,884),(4,436,884),(5,436,884),(1,436,895),(2,436,895),(4,436,895),(5,436,895),(6,436,1119),(7,436,1119),(1,440,665),(2,440,665),(4,440,665),(5,440,665),(6,440,665),(7,440,665),(1,440,711),(2,440,711),(4,440,711),(5,440,711),(6,440,711),(7,440,711),(1,440,732),(2,440,732),(4,440,732),(5,440,732),(6,440,732)]
private theorem rectangles : paths.map (fun p => p.rectangle) = ris.map rectangle := by rfl
private theorem coverage : ∀ ri ∈ ris, ∀ cs ∈ codes, ∃ a ∈ pairs, a.1=ri ∧ a.2.1∈cs ∧ a.2.2∈cs := by decide
private theorem excluded : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (rectangle a.1) r s → ¬(certBoundHolds (lowerHistoryBound a.2.1) r s q ∧ certBoundHolds (lowerHistoryBound a.2.2) r s q) := Freiman.lowerHistory_row2_exclusions_02
theorem solution : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsH[39]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  False := by
  exact close_negative lowerHistoryBound rectangle paths codes ris pairs rectangles
    Freiman.lowerHistory_row2_source_case_19 excluded coverage
#print axioms solution
