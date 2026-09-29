-- Prove2me | solution 1 for Freiman.lowerHistory_row2_certificate_case_08
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:51:41.113584+00:00
-- url     : https://prove2.me/submissions/7eee4901-369e-4b13-91be-f7b6237000b8

import Theorems.Thm_Freiman_lowerHistory_complement
import Theorems.Thm_Freiman_lowerHistory_row2_endpoints_02
import Theorems.Thm_Freiman_lowerHistory_row2_endpoints_04
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_01
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_02
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_03
import Theorems.Thm_Freiman_lowerHistory_row2_source_case_08
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem close_positive
    (B : ℕ → CertBound) (R : ℕ → CertRectangle)
    (paths : List LowerHistoryPath) (sources : List (List ℕ))
    (entries : List (LowerHistoryPath × ℕ × List (List ℕ × ℕ)))
    (pairs : List (ℕ × ℕ × ℕ))
    (hpaths : entries.map Prod.fst = paths)
    (hproperties : ∀ e ∈ entries, e.1.catalog ≠ .initial ∧ e.1.row ≠ 4 ∧
      e.1.rectangle = R e.2.1)
    (hsource : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ paths →
      LowerHistorySourceEvents base p →
      ∃ bs ∈ sources.map (fun cs => cs.map B), lowerHistoryAtBase base bs)
    (hendpoints : ∀ e ∈ entries, lowerHistoryEndpointComparisons e.1 =
      e.2.2.map (fun cg => (cg.1.map B,LowerHistoryComparison.bound
        (lowerHistoryComplement (B cg.2)))))
    (hcomplement : ∀ b r s q, certBoundHolds (lowerHistoryComplement b) r s q ↔
      ¬ certBoundHolds b r s q)
    (hex : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (R a.1) r s →
      ¬ (certBoundHolds (B a.2.1) r s q ∧ certBoundHolds (B a.2.2) r s q))
    (hcovered : ∀ e ∈ entries, ∀ cs ∈ sources, ∀ cg ∈ e.2.2,
      ∃ a ∈ pairs, a.1 = e.2.1 ∧ a.2.1 ∈ (cs ++ cg.1) ++ [cg.2] ∧
        a.2.2 ∈ (cs ++ cg.1) ++ [cg.2]) :
    ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ paths →
      LowerHistorySourceEvents base p →
      certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
      p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
  intro base p hp hevents hr
  obtain ⟨bs,hbs,hs⟩ := hsource base p hp hevents
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hbs
  have hm : p ∈ entries.map Prod.fst := by rw [hpaths]; exact hp
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hm
  obtain ⟨hi,h4,hrect⟩ := hproperties e he
  refine ⟨hi,h4,?_⟩
  intro cg hcg hc
  rw [hendpoints e he] at hcg
  obtain ⟨ec,hec,rfl⟩ := List.mem_map.mp hcg
  change certBoundHolds (lowerHistoryComplement (B ec.2))
    (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)
  apply (hcomplement (B ec.2) (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)).2
  intro hg
  have holds : ∀ i ∈ (cs ++ ec.1) ++ [ec.2],
      certBoundHolds (B i) (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact hs (B i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
      · exact hc (B i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
    · have heq := List.mem_singleton.mp hi
      subst i
      exact hg
  obtain ⟨a,ha,har,hlo,hhi⟩ := hcovered e he cs hcs ec hec
  apply hex a ha (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)
  · rw [har,← hrect]
    exact hr
  · exact ⟨holds _ hlo,holds _ hhi⟩
private def rectangle (i : ℕ) : CertRectangle := lowerHistoryRectangles[i]?.getD ⟨0,1,0,1⟩
private def paths : List LowerHistoryPath := [lowerHistoryPathsR[7],lowerHistoryPathsR[22],lowerHistoryPathsR[37],lowerHistoryPathsR[52],lowerHistoryPathsR[67],lowerHistoryPathsR[82]]
private def codes : List (List ℕ) := [[371,843,260,440,856,282,851,274,851]]
private def entries : List (LowerHistoryPath × ℕ × List (List ℕ × ℕ)) := [(lowerHistoryPathsR[7],5,[([836,1139,858,1174],889),([836,1139,858,291],887),([836,1139,294,441],889),([836,1139,294,865],890),([836,259,858,1174],1169),([836,259,858,291],1167),([836,259,294,441],1169),([836,259,294,865],1166),([284,429,858,1174],889),([284,429,858,291],887),([284,429,294,441],889),([284,429,294,865],890),([284,819,858,1174],901),([284,819,858,291],900),([284,819,294,441],901),([284,819,294,865],902)]),(lowerHistoryPathsR[22],4,[([836,1139,858,1174],889),([836,1139,858,291],887),([836,1139,294,441],889),([836,1139,294,865],890),([836,259,858,1174],1169),([836,259,858,291],1167),([836,259,294,441],1169),([836,259,294,865],1166),([284,429,858,1174],889),([284,429,858,291],887),([284,429,294,441],889),([284,429,294,865],890),([284,819,858,1174],901),([284,819,858,291],900),([284,819,294,441],901),([284,819,294,865],902)]),(lowerHistoryPathsR[37],1,[([836,1139,858,1174],889),([836,1139,858,291],887),([836,1139,294,441],889),([836,1139,294,865],890),([836,259,858,1174],1169),([836,259,858,291],1167),([836,259,294,441],1169),([836,259,294,865],1166),([284,429,858,1174],889),([284,429,858,291],887),([284,429,294,441],889),([284,429,294,865],890),([284,819,858,1174],901),([284,819,858,291],900),([284,819,294,441],901),([284,819,294,865],902)]),(lowerHistoryPathsR[52],6,[([858,1174],904),([858,291],905),([294,441],904),([294,865],903)]),(lowerHistoryPathsR[67],2,[([836,1139,858,1174],889),([836,1139,858,291],887),([836,1139,294,441],889),([836,1139,294,865],890),([836,259,858,1174],1169),([836,259,858,291],1167),([836,259,294,441],1169),([836,259,294,865],1166),([284,429,858,1174],889),([284,429,858,291],887),([284,429,294,441],889),([284,429,294,865],890),([284,819,858,1174],901),([284,819,858,291],900),([284,819,294,441],901),([284,819,294,865],902)]),(lowerHistoryPathsR[82],7,[([858,1174],904),([858,291],905),([294,441],904),([294,865],903)])]
private def pairs : List (ℕ × ℕ × ℕ) := [(1,287,769),(2,287,769),(4,287,769),(5,287,769),(6,287,769),(7,287,769),(1,291,887),(2,291,887),(4,291,887),(5,291,887),(1,291,900),(2,291,900),(4,291,900),(5,291,900),(6,291,905),(7,291,905),(1,291,1167),(2,291,1167),(4,291,1167),(5,291,1167),(1,293,843),(2,293,843),(4,293,843),(5,293,843),(6,293,843),(7,293,843),(1,294,890),(2,294,890),(4,294,890),(5,294,890),(1,294,902),(2,294,902),(4,294,902),(5,294,902),(6,294,903),(7,294,903),(1,294,1166),(2,294,1166),(4,294,1166),(5,294,1166),(1,429,880),(2,429,880),(4,429,880),(5,429,880),(1,429,885),(2,429,885),(4,429,885),(5,429,885),(1,429,889),(2,429,889)] ++ [(4,429,889),(5,429,889),(1,429,1149),(2,429,1149),(4,429,1149),(5,429,1149),(0,433,447),(3,433,447),(0,433,449),(3,433,449),(0,433,450),(3,433,450),(0,433,455),(3,433,455),(0,433,456),(3,433,456),(3,433,830),(0,433,839),(3,433,839),(1,436,836),(2,436,836),(4,436,836),(5,436,836),(1,436,884),(2,436,884),(4,436,884),(5,436,884),(1,436,895),(2,436,895),(4,436,895),(5,436,895),(6,436,1119),(7,436,1119),(1,440,665),(2,440,665),(4,440,665),(5,440,665),(6,440,665),(7,440,665),(1,440,711),(2,440,711),(4,440,711),(5,440,711),(6,440,711),(7,440,711),(1,440,732),(2,440,732),(4,440,732),(5,440,732),(6,440,732)] ++ [(7,440,732),(1,440,769),(2,440,769),(4,440,769),(5,440,769),(6,440,769),(7,440,769),(1,440,795),(2,440,795),(4,440,795),(5,440,795),(6,440,795),(7,440,795),(1,440,814),(2,440,814),(4,440,814),(5,440,814),(6,440,814),(7,440,814),(1,440,833),(2,440,833),(4,440,833),(5,440,833),(6,440,833),(7,440,833),(1,440,836),(2,440,836),(4,440,836),(5,440,836),(1,440,893),(2,440,893),(4,440,893),(5,440,893),(1,440,896),(2,440,896),(4,440,896),(5,440,896),(1,440,901),(2,440,901),(4,440,901),(5,440,901),(6,440,904),(7,440,904),(6,440,1116),(7,440,1116),(6,440,1121),(7,440,1121),(1,440,1149),(2,440,1149),(4,440,1149)]
private theorem path_projection : entries.map Prod.fst = paths := by rfl
private theorem properties : ∀ e ∈ entries, e.1.catalog ≠ .initial ∧ e.1.row ≠ 4 ∧ e.1.rectangle = rectangle e.2.1 := by
  intro e he
  simp only [entries,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by decide,by decide,rfl⟩
private theorem coverage : ∀ e ∈ entries, ∀ cs ∈ codes, ∀ cg ∈ e.2.2, ∃ a ∈ pairs, a.1=e.2.1 ∧ a.2.1∈(cs ++ cg.1) ++ [cg.2] ∧ a.2.2∈(cs ++ cg.1) ++ [cg.2] := by decide
private theorem endpoint_projection : ∀ e ∈ entries, lowerHistoryEndpointComparisons e.1 = e.2.2.map (fun cg => (cg.1.map lowerHistoryBound,LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound cg.2)))) := by
  intro e he
  simp only [entries,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Freiman.lowerHistory_row2_endpoints_02 lowerHistoryPathsR[7] (List.mem_cons_self)
  · exact Freiman.lowerHistory_row2_endpoints_02 lowerHistoryPathsR[22] (List.mem_cons_of_mem _ (List.mem_cons_self))
  · exact Freiman.lowerHistory_row2_endpoints_02 lowerHistoryPathsR[37] (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  · exact Freiman.lowerHistory_row2_endpoints_04 lowerHistoryPathsR[52] (List.mem_cons_self)
  · exact Freiman.lowerHistory_row2_endpoints_02 lowerHistoryPathsR[67] (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  · exact Freiman.lowerHistory_row2_endpoints_04 lowerHistoryPathsR[82] (List.mem_cons_of_mem _ (List.mem_cons_self))
private theorem excluded : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (rectangle a.1) r s → ¬(certBoundHolds (lowerHistoryBound a.2.1) r s q ∧ certBoundHolds (lowerHistoryBound a.2.2) r s q) := List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨Freiman.lowerHistory_row2_exclusions_01,Freiman.lowerHistory_row2_exclusions_02⟩,Freiman.lowerHistory_row2_exclusions_03⟩
theorem solution : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[7],lowerHistoryPathsR[22],lowerHistoryPathsR[37],lowerHistoryPathsR[52],lowerHistoryPathsR[67],lowerHistoryPathsR[82]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
  exact close_positive lowerHistoryBound rectangle paths codes entries pairs path_projection properties
    Freiman.lowerHistory_row2_source_case_08 endpoint_projection lowerHistory_complement excluded coverage
#print axioms solution
