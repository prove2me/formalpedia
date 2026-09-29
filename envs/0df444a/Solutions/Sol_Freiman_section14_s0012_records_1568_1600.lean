-- Prove2me | solution 1 for Freiman.section14_s0012_records_1568_1600
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:02:26.252232+00:00
-- url     : https://prove2.me/submissions/34b1deef-a18d-480d-bbf1-70f95889e979

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
namespace Section14Records_12_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 12 (⟨227,(22),[4,8,12,16],[10],1374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1374,[4,8,9,12,16],1378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 12 (⟨227,(23),[3,4,7,8,12,15,16],[10],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 12 (⟨227,(24),[4,8,12,16],[10],1374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1374,[4,8,9,12,16],1378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 12 (⟨228,(0),[3,4,8,12,15,16],[10],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 12 (⟨228,(1),[3,4,8,12,15,16],[10],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 12 (⟨228,(2),[4,8,12,16],[10],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 12 (⟨228,(3),[3,4,8,12,15,16],[10],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 12 (⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 12 (⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 12 (⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 12 (⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 12 (⟨228,(8),[3,4,7,8,12,15,16],[10],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 12 (⟨228,(9),[8,12],[10],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 12 (⟨228,(10),[3,4,7,8,12,15,16],[10],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 12 (⟨228,(11),[3,4,7,8,12,15,16],[10],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 12 (⟨228,(12),[3,4,7,8,12,15,16],[10],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 12 (⟨228,(13),[3,4,7,8,12,15,16],[10],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 12 (⟨228,(14),[3,4,7,8,12,15,16],[10],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 12 (⟨228,(15),[3,4,7,8,12,15,16],[10],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 12 (⟨228,(16),[3,4,7,8,12,15,16],[10],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 12 (⟨228,(17),[3,4,7,8,12,15,16],[10],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 12 (⟨228,(18),[3,4,7,8,12,15,16],[10],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 12 (⟨228,(19),[3,4,7,8,12,15,16],[10],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 12 (⟨228,(20),[3,4,7,8,12,15,16],[10],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 12 (⟨228,(21),[3,4,7,8,12,15,16],[10],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 12 (⟨228,(22),[3,4,7,8,12,15,16],[10],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 12 (⟨228,(23),[3,4,7,8,12,15,16],[10],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 12 (⟨228,(24),[3,4,7,8,12,15,16],[10],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 12 (⟨230,(0),[3,4,7,8,12,15,16],[10],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 12 (⟨230,(1),[12],[10],1715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1715,[12],1720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 12 (⟨230,(2),[3,4,7,8,12,15,16],[10],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 12 (⟨230,(3),[3,4,7,8,12,15,16],[10],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1568).take 32 = [⟨227,(22),[4,8,12,16],[10],1374⟩,⟨227,(23),[3,4,7,8,12,15,16],[10],788⟩,⟨227,(24),[4,8,12,16],[10],1374⟩,⟨228,(0),[3,4,8,12,15,16],[10],789⟩,⟨228,(1),[3,4,8,12,15,16],[10],790⟩,⟨228,(2),[4,8,12,16],[10],791⟩,⟨228,(3),[3,4,8,12,15,16],[10],792⟩,⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩,⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩,⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩,⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩,⟨228,(8),[3,4,7,8,12,15,16],[10],797⟩,⟨228,(9),[8,12],[10],793⟩,⟨228,(10),[3,4,7,8,12,15,16],[10],798⟩,⟨228,(11),[3,4,7,8,12,15,16],[10],799⟩,⟨228,(12),[3,4,7,8,12,15,16],[10],800⟩,⟨228,(13),[3,4,7,8,12,15,16],[10],801⟩,⟨228,(14),[3,4,7,8,12,15,16],[10],800⟩,⟨228,(15),[3,4,7,8,12,15,16],[10],802⟩,⟨228,(16),[3,4,7,8,12,15,16],[10],803⟩,⟨228,(17),[3,4,7,8,12,15,16],[10],804⟩,⟨228,(18),[3,4,7,8,12,15,16],[10],805⟩,⟨228,(19),[3,4,7,8,12,15,16],[10],804⟩,⟨228,(20),[3,4,7,8,12,15,16],[10],806⟩,⟨228,(21),[3,4,7,8,12,15,16],[10],807⟩,⟨228,(22),[3,4,7,8,12,15,16],[10],808⟩,⟨228,(23),[3,4,7,8,12,15,16],[10],809⟩,⟨228,(24),[3,4,7,8,12,15,16],[10],808⟩,⟨230,(0),[3,4,7,8,12,15,16],[10],810⟩,⟨230,(1),[12],[10],1715⟩,⟨230,(2),[3,4,7,8,12,15,16],[10],812⟩,⟨230,(3),[3,4,7,8,12,15,16],[10],813⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1599
end Section14Records_12_1568_1600

#print axioms solution
