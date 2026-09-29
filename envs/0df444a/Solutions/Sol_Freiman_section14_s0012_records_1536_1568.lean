-- Prove2me | solution 1 for Freiman.section14_s0012_records_1536_1568
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:00:39.826984+00:00
-- url     : https://prove2.me/submissions/32ba8f31-f386-4e25-9a56-f9db460ae004

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
namespace Section14Records_12_1536_1568
private theorem valid1536 : RecordDataValid section14Catalog 12 (⟨226,(0),[3,4,8,12,15,16],[10],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1537 : RecordDataValid section14Catalog 12 (⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1538 : RecordDataValid section14Catalog 12 (⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1539 : RecordDataValid section14Catalog 12 (⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1540 : RecordDataValid section14Catalog 12 (⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1541 : RecordDataValid section14Catalog 12 (⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1542 : RecordDataValid section14Catalog 12 (⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1543 : RecordDataValid section14Catalog 12 (⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1544 : RecordDataValid section14Catalog 12 (⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1545 : RecordDataValid section14Catalog 12 (⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1546 : RecordDataValid section14Catalog 12 (⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1547 : RecordDataValid section14Catalog 12 (⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1548 : RecordDataValid section14Catalog 12 (⟨227,(2),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1549 : RecordDataValid section14Catalog 12 (⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1550 : RecordDataValid section14Catalog 12 (⟨227,(4),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1551 : RecordDataValid section14Catalog 12 (⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1552 : RecordDataValid section14Catalog 12 (⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1553 : RecordDataValid section14Catalog 12 (⟨227,(7),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1554 : RecordDataValid section14Catalog 12 (⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1555 : RecordDataValid section14Catalog 12 (⟨227,(9),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1556 : RecordDataValid section14Catalog 12 (⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1557 : RecordDataValid section14Catalog 12 (⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1558 : RecordDataValid section14Catalog 12 (⟨227,(12),[4,8,12,16],[10],1372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1372,[4,8,9,12,16],1376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1559 : RecordDataValid section14Catalog 12 (⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1560 : RecordDataValid section14Catalog 12 (⟨227,(14),[4,8,12,16],[10],1372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1372,[4,8,9,12,16],1376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1561 : RecordDataValid section14Catalog 12 (⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1562 : RecordDataValid section14Catalog 12 (⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1563 : RecordDataValid section14Catalog 12 (⟨227,(17),[4,8,12,16],[10],1373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1373,[4,8,9,12,16],1377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1564 : RecordDataValid section14Catalog 12 (⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1565 : RecordDataValid section14Catalog 12 (⟨227,(19),[4,8,12,16],[10],1373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1373,[4,8,9,12,16],1377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1566 : RecordDataValid section14Catalog 12 (⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1567 : RecordDataValid section14Catalog 12 (⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1536).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1536).take 32 = [⟨226,(0),[3,4,8,12,15,16],[10],766⟩,⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩,⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩,⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩,⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩,⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩,⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩,⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩,⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩,⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩,⟨227,(2),[4,8,12,16],[10],1371⟩,⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩,⟨227,(4),[4,8,12,16],[10],1371⟩,⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩,⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩,⟨227,(7),[4,8,12,16],[10],1371⟩,⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩,⟨227,(9),[4,8,12,16],[10],1371⟩,⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩,⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩,⟨227,(12),[4,8,12,16],[10],1372⟩,⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩,⟨227,(14),[4,8,12,16],[10],1372⟩,⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩,⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩,⟨227,(17),[4,8,12,16],[10],1373⟩,⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩,⟨227,(19),[4,8,12,16],[10],1373⟩,⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩,⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1536
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1537
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1538
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1539
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1540
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1541
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1542
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1543
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1544
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1545
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1546
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1547
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1548
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1549
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1550
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1551
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1552
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1553
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1554
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1555
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1556
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1557
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1558
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1559
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1560
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1561
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1562
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1563
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1564
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1565
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1566
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1567
end Section14Records_12_1536_1568

#print axioms solution
