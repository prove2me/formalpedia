-- Prove2me | solution 1 for Freiman.section14_s0016_records_1408_1440
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:31:08.631005+00:00
-- url     : https://prove2.me/submissions/897647c0-fed3-4e00-b684-df1361892fa5

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
namespace Section14Records_16_1408_1440
private theorem valid1408 : RecordDataValid section14Catalog 16 (⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1409 : RecordDataValid section14Catalog 16 (⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1410 : RecordDataValid section14Catalog 16 (⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1411 : RecordDataValid section14Catalog 16 (⟨225,(7),[4,8,12,16],[10],1368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1368,[4,8,9,12,16],1372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1412 : RecordDataValid section14Catalog 16 (⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1413 : RecordDataValid section14Catalog 16 (⟨225,(9),[4,8,12,16],[10],1368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1368,[4,8,9,12,16],1372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1414 : RecordDataValid section14Catalog 16 (⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1415 : RecordDataValid section14Catalog 16 (⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1416 : RecordDataValid section14Catalog 16 (⟨225,(12),[4,8,12,16],[10],1369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1369,[4,8,9,12,16],1373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1417 : RecordDataValid section14Catalog 16 (⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1418 : RecordDataValid section14Catalog 16 (⟨225,(14),[4,8,12,16],[10],1369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1369,[4,8,9,12,16],1373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1419 : RecordDataValid section14Catalog 16 (⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1420 : RecordDataValid section14Catalog 16 (⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1421 : RecordDataValid section14Catalog 16 (⟨225,(17),[4,8,12,16],[10],1370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1370,[4,8,9,12,16],1374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1422 : RecordDataValid section14Catalog 16 (⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1423 : RecordDataValid section14Catalog 16 (⟨225,(19),[4,8,12,16],[10],1370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1370,[4,8,9,12,16],1374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1424 : RecordDataValid section14Catalog 16 (⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1425 : RecordDataValid section14Catalog 16 (⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1426 : RecordDataValid section14Catalog 16 (⟨225,(22),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1427 : RecordDataValid section14Catalog 16 (⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1428 : RecordDataValid section14Catalog 16 (⟨225,(24),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1429 : RecordDataValid section14Catalog 16 (⟨226,(0),[3,4,8,12,15,16],[10],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1430 : RecordDataValid section14Catalog 16 (⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1431 : RecordDataValid section14Catalog 16 (⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1432 : RecordDataValid section14Catalog 16 (⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1433 : RecordDataValid section14Catalog 16 (⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1434 : RecordDataValid section14Catalog 16 (⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1435 : RecordDataValid section14Catalog 16 (⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1436 : RecordDataValid section14Catalog 16 (⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1437 : RecordDataValid section14Catalog 16 (⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1438 : RecordDataValid section14Catalog 16 (⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1439 : RecordDataValid section14Catalog 16 (⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1408).take 32 = [⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩,⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩,⟨225,(7),[4,8,12,16],[10],1368⟩,⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩,⟨225,(9),[4,8,12,16],[10],1368⟩,⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩,⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩,⟨225,(12),[4,8,12,16],[10],1369⟩,⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩,⟨225,(14),[4,8,12,16],[10],1369⟩,⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩,⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩,⟨225,(17),[4,8,12,16],[10],1370⟩,⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩,⟨225,(19),[4,8,12,16],[10],1370⟩,⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩,⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩,⟨225,(22),[4,8,12,16],[10],1367⟩,⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩,⟨225,(24),[4,8,12,16],[10],1367⟩,⟨226,(0),[3,4,8,12,15,16],[10],766⟩,⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩,⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩,⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩,⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩,⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩,⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩,⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩,⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1408
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1409
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1410
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1411
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1412
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1413
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1414
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1415
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1416
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1417
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1418
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1419
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1420
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1421
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1422
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1423
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1424
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1425
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1426
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1427
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1428
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1429
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1430
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1431
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1432
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1433
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1434
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1435
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1436
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1437
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1438
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1439
end Section14Records_16_1408_1440

#print axioms solution
