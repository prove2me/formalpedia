-- Prove2me | solution 1 for Freiman.section14_s0008_records_2304_2336
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:58:41.357482+00:00
-- url     : https://prove2.me/submissions/8553450f-233a-412b-8951-470ca3662470

import Definitions.Def_Freiman_section14Data
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

open Freiman
set_option synthInstance.maxSize 100000
set_option maxRecDepth 100000
namespace M7Section14Sep18
instance (r : CertRectangle) : Decidable (certRectangleValid r) := by
  unfold certRectangleValid
  infer_instance
instance (t : CertThreshold) : Decidable (certThresholdDataValid t) := by
  unfold certThresholdDataValid
  infer_instance
instance (z : CertField) (q : ℚ) : Decidable (certCoefficientBoundValid z q) := by
  unfold certCoefficientBoundValid
  infer_instance
instance (w : CertWitness) : Decidable (certWitnessValid w) := by
  unfold certWitnessValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (caseId : ℕ)
    (gs : ℕ × Section14Spec) : Decidable (section14SpecValid C S caseId gs) := by
  unfold section14SpecValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (p : Section14Plan) :
    Decidable (section14PlanValid C S p) := by
  unfold section14PlanValid
  infer_instance
instance (outer inner : CertRectangle) : Decidable (section14RectangleContains outer inner) := by
  unfold section14RectangleContains
  infer_instance
instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (section14RecordValid C si r) := by
  unfold section14RecordValid
  infer_instance
instance (C : Section14Catalog) (si parent goal : ℕ) (branch : ℤ) :
    Decidable (section14Recorded C si parent goal branch) := by
  unfold section14Recorded
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14Coverage C si) := by
  unfold section14Coverage
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14StateValid C si) := by
  unfold section14StateValid
  infer_instance
end M7Section14Sep18

open Freiman
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
set_option Elab.async false
namespace M7Section14Sep18

def RecordDataValid (C : Section14Catalog) (si : ℕ) (r : Section14Record) : Prop :=
  let S := section14State C si
  let p := section14Proof C r.proofId
  0 < r.goal ∧ r.goal ≤ C.goals.length ∧ 0 < r.proofId ∧ r.proofId ≤ C.proofs.length ∧
  (section14Branch C (section14Goal C r.goal) r.branch).2 ≠ .automatic ∧
  (∀ b ∈ section14Parents C S, b.branch ∈ r.parents →
    section14Bound C p.lowerBound ∈ section14RecordConditions C r b ∧
    section14Bound C p.upperBound ∈ section14RecordConditions C r b) ∧
  ∃ a ∈ C.assignments, a.proofId = r.proofId ∧ si ∈ a.states ∧
    0 < a.witnessId ∧ a.witnessId ≤ C.witnesses.length ∧
    let w := section14Witness C a.witnessId
    w.firstThreshold = p.lowerBound.threshold ∧ w.secondThreshold = p.upperBound.threshold ∧
    section14RectangleContains w.rectangle S.rectangle

instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (RecordDataValid C si r) := by
  unfold RecordDataValid
  infer_instance

theorem recordValid_of_data (C : Section14Catalog) (si : ℕ) (r : Section14Record)
    (hnum : ∀ a ∈ C.assignments, certWitnessValid
      (section14PairWitness C (section14Proof C a.proofId) (section14Witness C a.witnessId)))
    (h : RecordDataValid C si r) : section14RecordValid C si r := by
  rcases h with ⟨hg0,hg1,hp0,hp1,hbranch,hconditions,a,ha,hp,hs,hw0,hw1,hl,hu,hrect⟩
  have hv := hnum a ha
  rw [hp] at hv
  exact ⟨hg0,hg1,hp0,hp1,hbranch,hconditions,a,ha,hp,hs,hw0,hw1,hl,hu,hrect,hv⟩

theorem recordValid_all_of_data (C : Section14Catalog) (si : ℕ)
    (hnum : ∀ a ∈ C.assignments, certWitnessValid
      (section14PairWitness C (section14Proof C a.proofId) (section14Witness C a.witnessId)))
    (h : ∀ r ∈ C.records, si ∈ r.states → RecordDataValid C si r) :
    ∀ r ∈ C.records, si ∈ r.states → section14RecordValid C si r := by
  intro r hr hs
  exact recordValid_of_data C si r hnum (h r hr hs)
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_8_2304_2336
private theorem valid2304 : RecordDataValid section14Catalog 8 (⟨309,(1),[8,12],[10],1189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1189,[3,5,7,8,9,11,12,15],1193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2305 : RecordDataValid section14Catalog 8 (⟨309,(2),[8,12],[10],1190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1190,[3,5,7,8,9,11,12,15],1194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2306 : RecordDataValid section14Catalog 8 (⟨309,(3),[8,12],[10],1191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1191,[3,5,7,8,9,11,12,15],1195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2307 : RecordDataValid section14Catalog 8 (⟨309,(4),[8,12],[10],1192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1192,[3,7,8,11,12,15],1196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2308 : RecordDataValid section14Catalog 8 (⟨311,(0),[8,12],[10],1478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1478,[5,8,9,12],1483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2309 : RecordDataValid section14Catalog 8 (⟨311,(1),[8,12],[10],1479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1479,[5,8,9,12],1484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2310 : RecordDataValid section14Catalog 8 (⟨311,(2),[8,12],[10],1480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1480,[5,8,9,12],1485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2311 : RecordDataValid section14Catalog 8 (⟨311,(3),[8,12],[10],1481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1481,[5,8,9,12],1486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2312 : RecordDataValid section14Catalog 8 (⟨312,(0),[8,12],[10],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2313 : RecordDataValid section14Catalog 8 (⟨312,(1),[8,12],[10],1483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1483,[5,8,9,12],1488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2314 : RecordDataValid section14Catalog 8 (⟨312,(2),[8,12],[10],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2315 : RecordDataValid section14Catalog 8 (⟨312,(3),[8,12],[10],1484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1484,[5,8,9,12],1489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2316 : RecordDataValid section14Catalog 8 (⟨313,(0),[8,12],[10],1200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1200,[3,5,7,8,9,11,12,15],1204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2317 : RecordDataValid section14Catalog 8 (⟨313,(1),[8,12],[10],1201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1201,[3,5,7,8,9,11,12,15],1205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2318 : RecordDataValid section14Catalog 8 (⟨313,(2),[8,12],[10],1202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1202,[3,5,7,8,9,11,12,15],1206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2319 : RecordDataValid section14Catalog 8 (⟨313,(3),[8],[10],1203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1203,[3,5,7,8,9,11,15],1207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2320 : RecordDataValid section14Catalog 8 (⟨315,(0),[8,12],[10],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2321 : RecordDataValid section14Catalog 8 (⟨315,(1),[8,12],[10],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2322 : RecordDataValid section14Catalog 8 (⟨315,(2),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2323 : RecordDataValid section14Catalog 8 (⟨315,(3),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2324 : RecordDataValid section14Catalog 8 (⟨315,(4),[8,12],[10],1489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1489,[5,8,9,12],1494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2325 : RecordDataValid section14Catalog 8 (⟨315,(5),[8,12],[10],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2326 : RecordDataValid section14Catalog 8 (⟨315,(6),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2327 : RecordDataValid section14Catalog 8 (⟨315,(7),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2328 : RecordDataValid section14Catalog 8 (⟨315,(8),[8,12],[10],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2329 : RecordDataValid section14Catalog 8 (⟨315,(9),[8,12],[10],1490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1490,[5,8,9,12],1495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2330 : RecordDataValid section14Catalog 8 (⟨315,(10),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2331 : RecordDataValid section14Catalog 8 (⟨315,(11),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2332 : RecordDataValid section14Catalog 8 (⟨315,(12),[8,12],[10],1491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1491,[5,8,9,12],1496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2333 : RecordDataValid section14Catalog 8 (⟨315,(13),[8,12],[10],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2334 : RecordDataValid section14Catalog 8 (⟨315,(14),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2335 : RecordDataValid section14Catalog 8 (⟨315,(15),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2304).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2304).take 32 = [⟨309,(1),[8,12],[10],1189⟩,⟨309,(2),[8,12],[10],1190⟩,⟨309,(3),[8,12],[10],1191⟩,⟨309,(4),[8,12],[10],1192⟩,⟨311,(0),[8,12],[10],1478⟩,⟨311,(1),[8,12],[10],1479⟩,⟨311,(2),[8,12],[10],1480⟩,⟨311,(3),[8,12],[10],1481⟩,⟨312,(0),[8,12],[10],1482⟩,⟨312,(1),[8,12],[10],1483⟩,⟨312,(2),[8,12],[10],1482⟩,⟨312,(3),[8,12],[10],1484⟩,⟨313,(0),[8,12],[10],1200⟩,⟨313,(1),[8,12],[10],1201⟩,⟨313,(2),[8,12],[10],1202⟩,⟨313,(3),[8],[10],1203⟩,⟨315,(0),[8,12],[10],1485⟩,⟨315,(1),[8,12],[10],1486⟩,⟨315,(2),[8,12],[10],1487⟩,⟨315,(3),[8,12],[10],1488⟩,⟨315,(4),[8,12],[10],1489⟩,⟨315,(5),[8,12],[10],1486⟩,⟨315,(6),[8,12],[10],1487⟩,⟨315,(7),[8,12],[10],1488⟩,⟨315,(8),[8,12],[10],1485⟩,⟨315,(9),[8,12],[10],1490⟩,⟨315,(10),[8,12],[10],1487⟩,⟨315,(11),[8,12],[10],1488⟩,⟨315,(12),[8,12],[10],1491⟩,⟨315,(13),[8,12],[10],1486⟩,⟨315,(14),[8,12],[10],1487⟩,⟨315,(15),[8,12],[10],1488⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2304
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2305
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2306
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2307
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2308
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2309
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2310
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2311
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2312
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2313
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2314
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2315
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2316
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2317
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2318
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2319
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2320
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2321
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2322
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2323
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2324
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2325
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2326
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2327
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2328
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2329
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2330
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2331
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2332
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2333
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2334
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2335
end Section14Records_8_2304_2336

#print axioms solution
