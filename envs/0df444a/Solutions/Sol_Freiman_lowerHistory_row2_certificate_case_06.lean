-- Prove2me | solution 1 for Freiman.lowerHistory_row2_certificate_case_06
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:51:10.904062+00:00
-- url     : https://prove2.me/submissions/2262abf7-b7e2-49bd-a816-2b9d395da7bc

import Theorems.Thm_Freiman_lowerHistory_complement
import Theorems.Thm_Freiman_lowerHistory_row2_endpoints_01
import Theorems.Thm_Freiman_lowerHistory_row2_endpoints_03
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_01
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_02
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_03
import Theorems.Thm_Freiman_lowerHistory_row2_exclusions_04
import Theorems.Thm_Freiman_lowerHistory_row2_source_case_06
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
private def paths : List LowerHistoryPath := [lowerHistoryPathsR[5],lowerHistoryPathsR[20],lowerHistoryPathsR[35],lowerHistoryPathsR[50],lowerHistoryPathsR[65],lowerHistoryPathsR[80]]
private def codes : List (List ℕ) := [[1153,371,843,260,440,856,420,817,250,817],[275,876,371,843,260,440,856,420,817,250,817]]
private def entries : List (LowerHistoryPath × ℕ × List (List ℕ × ℕ)) := [(lowerHistoryPathsR[5],5,[([836,1139,834,1149],884),([836,1139,834,271],880),([836,1139,283,436],884),([836,1139,283,841],885),([836,259,834,1149],1179),([836,259,834,271],1175),([836,259,283,436],1179),([836,259,283,841],1177),([284,429,834,1149],884),([284,429,834,271],880),([284,429,283,436],884),([284,429,283,841],885),([284,819,834,1149],895),([284,819,834,271],893),([284,819,283,436],895),([284,819,283,841],896)]),(lowerHistoryPathsR[20],4,[([836,1139,834,1149],884),([836,1139,834,271],880),([836,1139,283,436],884),([836,1139,283,841],885),([836,259,834,1149],1179),([836,259,834,271],1175),([836,259,283,436],1179),([836,259,283,841],1177),([284,429,834,1149],884),([284,429,834,271],880),([284,429,283,436],884),([284,429,283,841],885),([284,819,834,1149],895),([284,819,834,271],893),([284,819,283,436],895),([284,819,283,841],896)]),(lowerHistoryPathsR[35],1,[([836,1139,834,1149],884),([836,1139,834,271],880),([836,1139,283,436],884),([836,1139,283,841],885),([836,259,834,1149],1179),([836,259,834,271],1175),([836,259,283,436],1179),([836,259,283,841],1177),([284,429,834,1149],884),([284,429,834,271],880),([284,429,283,436],884),([284,429,283,841],885),([284,819,834,1149],895),([284,819,834,271],893),([284,819,283,436],895),([284,819,283,841],896)]),(lowerHistoryPathsR[50],6,[([834,1149],1119),([834,271],1121),([283,436],1119),([283,841],1116)]),(lowerHistoryPathsR[65],2,[([836,1139,834,1149],884),([836,1139,834,271],880),([836,1139,283,436],884),([836,1139,283,841],885),([836,259,834,1149],1179),([836,259,834,271],1175),([836,259,283,436],1179),([836,259,283,841],1177),([284,429,834,1149],884),([284,429,834,271],880),([284,429,283,436],884),([284,429,283,841],885),([284,819,834,1149],895),([284,819,834,271],893),([284,819,283,436],895),([284,819,283,841],896)]),(lowerHistoryPathsR[80],7,[([834,1149],1119),([834,271],1121),([283,436],1119),([283,841],1116)])]
private def pairs : List (ℕ × ℕ × ℕ) := [(1,287,769),(2,287,769),(4,287,769),(5,287,769),(6,287,769),(7,287,769),(1,291,887),(2,291,887),(4,291,887),(5,291,887),(1,291,900),(2,291,900),(4,291,900),(5,291,900),(6,291,905),(7,291,905),(1,291,1167),(2,291,1167),(4,291,1167),(5,291,1167),(1,293,843),(2,293,843),(4,293,843),(5,293,843),(6,293,843),(7,293,843),(1,294,890),(2,294,890),(4,294,890),(5,294,890),(1,294,902),(2,294,902),(4,294,902),(5,294,902),(6,294,903),(7,294,903),(1,294,1166),(2,294,1166),(4,294,1166),(5,294,1166),(1,429,880),(2,429,880),(4,429,880),(5,429,880),(1,429,885),(2,429,885),(4,429,885),(5,429,885),(1,429,889),(2,429,889)] ++ [(4,429,889),(5,429,889),(1,429,1149),(2,429,1149),(4,429,1149),(5,429,1149),(0,433,447),(3,433,447),(0,433,449),(3,433,449),(0,433,450),(3,433,450),(0,433,455),(3,433,455),(0,433,456),(3,433,456),(3,433,830),(0,433,839),(3,433,839),(1,436,836),(2,436,836),(4,436,836),(5,436,836),(1,436,884),(2,436,884),(4,436,884),(5,436,884),(1,436,895),(2,436,895),(4,436,895),(5,436,895),(6,436,1119),(7,436,1119),(1,440,665),(2,440,665),(4,440,665),(5,440,665),(6,440,665),(7,440,665),(1,440,711),(2,440,711),(4,440,711),(5,440,711),(6,440,711),(7,440,711),(1,440,732),(2,440,732),(4,440,732),(5,440,732),(6,440,732)] ++ [(7,440,732),(1,440,769),(2,440,769),(4,440,769),(5,440,769),(6,440,769),(7,440,769),(1,440,795),(2,440,795),(4,440,795),(5,440,795),(6,440,795),(7,440,795),(1,440,814),(2,440,814),(4,440,814),(5,440,814),(6,440,814),(7,440,814),(1,440,833),(2,440,833),(4,440,833),(5,440,833),(6,440,833),(7,440,833),(1,440,836),(2,440,836),(4,440,836),(5,440,836),(1,440,893),(2,440,893),(4,440,893),(5,440,893),(1,440,896),(2,440,896),(4,440,896),(5,440,896),(1,440,901),(2,440,901),(4,440,901),(5,440,901),(6,440,904),(7,440,904),(6,440,1116),(7,440,1116),(6,440,1121),(7,440,1121),(1,440,1149),(2,440,1149),(4,440,1149)] ++ [(5,440,1149),(6,440,1149),(7,440,1149),(1,440,1153),(2,440,1153),(4,440,1153),(5,440,1153),(6,440,1153),(7,440,1153),(1,442,817),(2,442,817),(4,442,817),(5,442,817),(6,442,817),(7,442,817)]
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
  · exact Freiman.lowerHistory_row2_endpoints_01 lowerHistoryPathsR[5] (List.mem_cons_self)
  · exact Freiman.lowerHistory_row2_endpoints_01 lowerHistoryPathsR[20] (List.mem_cons_of_mem _ (List.mem_cons_self))
  · exact Freiman.lowerHistory_row2_endpoints_01 lowerHistoryPathsR[35] (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  · exact Freiman.lowerHistory_row2_endpoints_03 lowerHistoryPathsR[50] (List.mem_cons_self)
  · exact Freiman.lowerHistory_row2_endpoints_01 lowerHistoryPathsR[65] (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  · exact Freiman.lowerHistory_row2_endpoints_03 lowerHistoryPathsR[80] (List.mem_cons_of_mem _ (List.mem_cons_self))
private theorem excluded : ∀ a ∈ pairs, ∀ r s q : ℝ, certRectangleMem (rectangle a.1) r s → ¬(certBoundHolds (lowerHistoryBound a.2.1) r s q ∧ certBoundHolds (lowerHistoryBound a.2.2) r s q) := List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨Freiman.lowerHistory_row2_exclusions_01,Freiman.lowerHistory_row2_exclusions_02⟩,Freiman.lowerHistory_row2_exclusions_03⟩,Freiman.lowerHistory_row2_exclusions_04⟩
theorem solution : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[5],lowerHistoryPathsR[20],lowerHistoryPathsR[35],lowerHistoryPathsR[50],lowerHistoryPathsR[65],lowerHistoryPathsR[80]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
  exact close_positive lowerHistoryBound rectangle paths codes entries pairs path_projection properties
    Freiman.lowerHistory_row2_source_case_06 endpoint_projection lowerHistory_complement excluded coverage
#print axioms solution
