-- Prove2me | solution 1 for Freiman.section14_s0016_records_1536_1568
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:37:36.451609+00:00
-- url     : https://prove2.me/submissions/f43d5352-af35-42e2-949a-63e26552271f

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
namespace Section14Records_16_1536_1568
private theorem valid1536 : RecordDataValid section14Catalog 16 (⟨232,(2),[3,4,7,8,12,15,16],[10],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1537 : RecordDataValid section14Catalog 16 (⟨232,(3),[3,4,7,8,12,15,16],[10],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1538 : RecordDataValid section14Catalog 16 (⟨232,(4),[4,8,12,16],[10],848⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1539 : RecordDataValid section14Catalog 16 (⟨232,(5),[3,4,7,8,12,15,16],[10],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1540 : RecordDataValid section14Catalog 16 (⟨232,(6),[3,4,7,8,12,15,16],[10],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1541 : RecordDataValid section14Catalog 16 (⟨232,(7),[3,4,7,8,12,15,16],[10],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1542 : RecordDataValid section14Catalog 16 (⟨232,(8),[3,4,7,8,12,15,16],[10],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1543 : RecordDataValid section14Catalog 16 (⟨232,(9),[4,8,12,16],[10],1378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1378,[4,8,9,12,16],1382⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1544 : RecordDataValid section14Catalog 16 (⟨232,(10),[3,4,7,8,12,15,16],[10],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1545 : RecordDataValid section14Catalog 16 (⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1546 : RecordDataValid section14Catalog 16 (⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1547 : RecordDataValid section14Catalog 16 (⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1548 : RecordDataValid section14Catalog 16 (⟨232,(14),[4,8,12,16],[10],1379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1379,[4,8,9,12,16],1383⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1549 : RecordDataValid section14Catalog 16 (⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1550 : RecordDataValid section14Catalog 16 (⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1551 : RecordDataValid section14Catalog 16 (⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1552 : RecordDataValid section14Catalog 16 (⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1553 : RecordDataValid section14Catalog 16 (⟨232,(19),[4,8,12,16],[10],1380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1380,[4,8,9,12,16],1384⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1554 : RecordDataValid section14Catalog 16 (⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1555 : RecordDataValid section14Catalog 16 (⟨234,(1),[4,8,12,16],[10],1381⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1381,[4,8,9,12,16],1385⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1556 : RecordDataValid section14Catalog 16 (⟨234,(2),[4,8,12,16],[10],1382⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1382,[4,8,9,12,16],1386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1557 : RecordDataValid section14Catalog 16 (⟨234,(3),[4,8,12,16],[10],1383⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1383,[4,8,9,12,16],1387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1558 : RecordDataValid section14Catalog 16 (⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1559 : RecordDataValid section14Catalog 16 (⟨234,(5),[4,8,12,16],[10],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1560 : RecordDataValid section14Catalog 16 (⟨234,(6),[4,8,12,16],[10],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1561 : RecordDataValid section14Catalog 16 (⟨234,(7),[4,8,12,16],[10],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1562 : RecordDataValid section14Catalog 16 (⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1563 : RecordDataValid section14Catalog 16 (⟨234,(9),[4,8,12,16],[10],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1564 : RecordDataValid section14Catalog 16 (⟨234,(10),[4,8,12,16],[10],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1565 : RecordDataValid section14Catalog 16 (⟨234,(11),[4,8,12,16],[10],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1566 : RecordDataValid section14Catalog 16 (⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1567 : RecordDataValid section14Catalog 16 (⟨234,(13),[4,8,12,16],[10],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1536).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1536).take 32 = [⟨232,(2),[3,4,7,8,12,15,16],[10],846⟩,⟨232,(3),[3,4,7,8,12,15,16],[10],847⟩,⟨232,(4),[4,8,12,16],[10],848⟩,⟨232,(5),[3,4,7,8,12,15,16],[10],849⟩,⟨232,(6),[3,4,7,8,12,15,16],[10],850⟩,⟨232,(7),[3,4,7,8,12,15,16],[10],851⟩,⟨232,(8),[3,4,7,8,12,15,16],[10],852⟩,⟨232,(9),[4,8,12,16],[10],1378⟩,⟨232,(10),[3,4,7,8,12,15,16],[10],844⟩,⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩,⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩,⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩,⟨232,(14),[4,8,12,16],[10],1379⟩,⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩,⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩,⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩,⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩,⟨232,(19),[4,8,12,16],[10],1380⟩,⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩,⟨234,(1),[4,8,12,16],[10],1381⟩,⟨234,(2),[4,8,12,16],[10],1382⟩,⟨234,(3),[4,8,12,16],[10],1383⟩,⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩,⟨234,(5),[4,8,12,16],[10],1384⟩,⟨234,(6),[4,8,12,16],[10],1384⟩,⟨234,(7),[4,8,12,16],[10],1384⟩,⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩,⟨234,(9),[4,8,12,16],[10],1385⟩,⟨234,(10),[4,8,12,16],[10],1385⟩,⟨234,(11),[4,8,12,16],[10],1385⟩,⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩,⟨234,(13),[4,8,12,16],[10],1386⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1536
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1537
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1538
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1539
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1540
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1541
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1542
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1543
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1544
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1545
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1546
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1547
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1548
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1549
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1550
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1551
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1552
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1553
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1554
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1555
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1556
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1557
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1558
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1559
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1560
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1561
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1562
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1563
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1564
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1565
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1566
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1567
end Section14Records_16_1536_1568

#print axioms solution
