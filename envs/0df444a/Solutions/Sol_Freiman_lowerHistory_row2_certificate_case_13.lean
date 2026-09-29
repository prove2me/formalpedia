-- Prove2me | solution 1 for Freiman.lowerHistory_row2_certificate_case_13
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:52:01.010918+00:00
-- url     : https://prove2.me/submissions/618c9be5-49d6-44e5-b1b7-48f68e64a54e

import Theorems.Thm_Freiman_lowerHistory_row2_source_case_13
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_02
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_03
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
private def paths : List LowerHistoryPath := [lowerHistoryPathsR[12],lowerHistoryPathsR[27],lowerHistoryPathsR[42],lowerHistoryPathsR[57],lowerHistoryPathsR[72],lowerHistoryPathsR[87]]
private def codes : List (List ℕ) := [[824,1150,371,843,260,440,856,833,415,774,732,195,732]]
private def ris : List ℕ := [5,4,1,6,2,7]
private def pairs : List (ℕ × ℕ × ℕ) := [(4,429,889),(5,429,889),(1,429,1149),(2,429,1149),(4,429,1149),(5,429,1149),(0,433,447),(3,433,447),(0,433,449),(3,433,449),(0,433,450),(3,433,450),(0,433,455),(3,433,455),(0,433,456),(3,433,456),(3,433,830),(0,433,839),(3,433,839),(1,436,836),(2,436,836),(4,436,836),(5,436,836),(1,436,884),(2,436,884),(4,436,884),(5,436,884),(1,436,895),(2,436,895),(4,436,895),(5,436,895),(6,436,1119),(7,436,1119),(1,440,665),(2,440,665),(4,440,665),(5,440,665),(6,440,665),(7,440,665),(1,440,711),(2,440,711),(4,440,711),(5,440,711),(6,440,711),(7,440,711),(1,440,732),(2,440,732),(4,440,732),(5,440,732),(6,440,732)] ++ [(7,440,732),(1,440,769),(2,440,769),(4,440,769),(5,440,769),(6,440,769),(7,440,769),(1,440,795),(2,440,795),(4,440,795),(5,440,795),(6,440,795),(7,440,795),(1,440,814),(2,440,814),(4,440,814),(5,440,814),(6,440,814),(7,440,814),(1,440,833),(2,440,833),(4,440,833),(5,440,833),(6,440,833),(7,440,833),(1,440,836),(2,440,836),(4,440,836),(5,440,836),(1,440,893),(2,440,893),(4,440,893),(5,440,893),(1,440,896),(2,440,896),(4,440,896),(5,440,896),(1,440,901),(2,440,901),(4,440,901),(5,440,901),(6,440,904),(7,440,904),(6,440,1116),(7,440,1116),(6,440,1121),(7,440,1121),(1,440,1149),(2,440,1149),(4,440,1149)]
private theorem rectangles : paths.map (fun p => p.rectangle) = ris.map rectangle := by rfl
private theorem coverage : ∀ ri ∈ ris, ∀ cs ∈ codes, ∃ a ∈ pairs, a.1=ri ∧ a.2.1∈cs ∧ a.2.2∈cs := by decide
private theorem excluded : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (rectangle a.1) r s → ¬(certBoundHolds (lowerHistoryBound a.2.1) r s q ∧ certBoundHolds (lowerHistoryBound a.2.2) r s q) := List.forall_mem_append.mpr ⟨Freiman.lowerHistory_row2_exclusions_02,Freiman.lowerHistory_row2_exclusions_03⟩
theorem solution : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[12],lowerHistoryPathsR[27],lowerHistoryPathsR[42],lowerHistoryPathsR[57],lowerHistoryPathsR[72],lowerHistoryPathsR[87]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  False := by
  exact close_negative lowerHistoryBound rectangle paths codes ris pairs rectangles
    Freiman.lowerHistory_row2_source_case_13 excluded coverage
#print axioms solution
