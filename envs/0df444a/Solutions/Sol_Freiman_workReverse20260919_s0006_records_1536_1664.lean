-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_1536_1664
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:50:09.786084+00:00
-- url     : https://prove2.me/submissions/4f818634-83be-4819-95c6-2f6d766ac37c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1536_1568
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1536_1568
private theorem valid1536 : RecordDataValid section14Catalog 6 (⟨79,(4),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1537 : RecordDataValid section14Catalog 6 (⟨79,(5),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1538 : RecordDataValid section14Catalog 6 (⟨79,(6),[1,2,5,6],[150],365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨365,[1,2,4,5,6,8,9,10,12],366⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1539 : RecordDataValid section14Catalog 6 (⟨79,(6),[5,6],[190],1406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1406,[5,6,8,9,10,12],1411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1540 : RecordDataValid section14Catalog 6 (⟨79,(7),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1541 : RecordDataValid section14Catalog 6 (⟨79,(8),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1542 : RecordDataValid section14Catalog 6 (⟨79,(9),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1543 : RecordDataValid section14Catalog 6 (⟨79,(10),[1,2,5,6],[150,190],339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨339,[1,2,4,5,6,8,9,10,12],340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1544 : RecordDataValid section14Catalog 6 (⟨79,(11),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1545 : RecordDataValid section14Catalog 6 (⟨79,(12),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1546 : RecordDataValid section14Catalog 6 (⟨79,(13),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1547 : RecordDataValid section14Catalog 6 (⟨79,(14),[1,2,5,6],[150,190],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1548 : RecordDataValid section14Catalog 6 (⟨79,(15),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1549 : RecordDataValid section14Catalog 6 (⟨79,(16),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1550 : RecordDataValid section14Catalog 6 (⟨79,(17),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1551 : RecordDataValid section14Catalog 6 (⟨79,(18),[1,2,5,6],[150,190],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1552 : RecordDataValid section14Catalog 6 (⟨79,(19),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1553 : RecordDataValid section14Catalog 6 (⟨80,(5),[1,2,5,6],[150],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1554 : RecordDataValid section14Catalog 6 (⟨80,(5),[1,2,5,6,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1555 : RecordDataValid section14Catalog 6 (⟨80,(7),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1556 : RecordDataValid section14Catalog 6 (⟨80,(7),[1,2,6,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1557 : RecordDataValid section14Catalog 6 (⟨80,(8),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1558 : RecordDataValid section14Catalog 6 (⟨80,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1559 : RecordDataValid section14Catalog 6 (⟨80,(9),[1,2,5,6],[150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1560 : RecordDataValid section14Catalog 6 (⟨80,(9),[5,6,13,14],[190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1561 : RecordDataValid section14Catalog 6 (⟨80,(15),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1562 : RecordDataValid section14Catalog 6 (⟨80,(15),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1563 : RecordDataValid section14Catalog 6 (⟨80,(16),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1564 : RecordDataValid section14Catalog 6 (⟨80,(16),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1565 : RecordDataValid section14Catalog 6 (⟨80,(17),[1,2,5,6,13,14],[190],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1566 : RecordDataValid section14Catalog 6 (⟨80,(17),[1,2,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1567 : RecordDataValid section14Catalog 6 (⟨80,(19),[1,2,5,6,13,14],[190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1536_1568 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1536).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1536).take 32 = [⟨79,(4),[1,2,5,6],[150,190],2⟩,⟨79,(5),[1,2,5,6],[150,190],2⟩,⟨79,(6),[1,2,5,6],[150],365⟩,⟨79,(6),[5,6],[190],1406⟩,⟨79,(7),[1,2,5,6],[150,190],101⟩,⟨79,(8),[1,2,5,6],[150,190],2⟩,⟨79,(9),[1,2,5,6],[150,190],2⟩,⟨79,(10),[1,2,5,6],[150,190],339⟩,⟨79,(11),[1,2,5,6],[150,190],101⟩,⟨79,(12),[1,2,5,6],[150,190],2⟩,⟨79,(13),[1,2,5,6],[150,190],2⟩,⟨79,(14),[1,2,5,6],[150,190],286⟩,⟨79,(15),[1,2,5,6],[150,190],101⟩,⟨79,(16),[1,2,5,6],[150,190],2⟩,⟨79,(17),[1,2,5,6],[150,190],2⟩,⟨79,(18),[1,2,5,6],[150,190],287⟩,⟨79,(19),[1,2,5,6],[150,190],101⟩,⟨80,(5),[1,2,5,6],[150],105⟩,⟨80,(5),[1,2,5,6,14],[190],3⟩,⟨80,(7),[1,2,5,6],[150],3⟩,⟨80,(7),[1,2,6,14],[190],3⟩,⟨80,(8),[1,2,5,6],[150],3⟩,⟨80,(8),[1,2,5,6,13,14],[190],3⟩,⟨80,(9),[1,2,5,6],[150],143⟩,⟨80,(9),[5,6,13,14],[190],143⟩,⟨80,(15),[1,2,5,6],[150],3⟩,⟨80,(15),[1,2,5,6,13,14],[190],3⟩,⟨80,(16),[1,2,5,6],[150],3⟩,⟨80,(16),[1,2,5,6,13,14],[190],3⟩,⟨80,(17),[1,2,5,6,13,14],[190],48⟩,⟨80,(17),[1,2,6],[150],3⟩,⟨80,(19),[1,2,5,6,13,14],[190],143⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1536
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1537
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1538
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1539
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1540
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1541
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1542
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1543
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1544
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1545
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1546
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1547
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1548
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1549
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1550
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1551
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1552
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1553
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1554
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1555
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1556
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1557
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1558
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1559
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1560
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1561
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1562
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1563
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1564
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1565
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1566
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1567
end Section14Records_6_1536_1568

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1536_1568


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1568_1600
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 6 (⟨80,(19),[5,6],[150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,9,10,13,14],[5],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[130,134],389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[146],390⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨390,[1,2,3,5,6,7,13,14,15],391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[150],392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨392,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[174],628⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨628,[1,2,3,5,6,7,13,14,15],629⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[186],629⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨629,[1,2,4,5,6,8,9,10,12,13,14,16],630⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 6 (⟨82,(-1),[1,5,6,13],[194,198],630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 6 (⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 6 (⟨82,(-1),[2,6,9,10,14],[16,20],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 6 (⟨82,(-1),[2,6,14],[40,44,56,60],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 6 (⟨82,(-1),[2,6,14],[211,215,235,239,251,255],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 6 (⟨82,(-1),[2,6,14],[190],629⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨629,[1,2,4,5,6,8,9,10,12,13,14,16],630⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 6 (⟨82,(-1),[5,6],[131,135],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 6 (⟨82,(-1),[6],[195,199],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 6 (⟨84,(0),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 6 (⟨84,(1),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 6 (⟨84,(2),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 6 (⟨84,(3),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 6 (⟨84,(4),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 6 (⟨84,(5),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 6 (⟨84,(6),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1568_1600 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1568).take 32 = [⟨80,(19),[5,6],[150],143⟩,⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩,⟨82,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨82,(-1),[1,2,5,6,9,10,13,14],[5],386⟩,⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨82,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨82,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],386⟩,⟨82,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],387⟩,⟨82,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],388⟩,⟨82,(-1),[1,2,5,6,13,14],[130,134],389⟩,⟨82,(-1),[1,2,5,6,13,14],[146],390⟩,⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩,⟨82,(-1),[1,2,5,6,13,14],[150],392⟩,⟨82,(-1),[1,2,5,6,13,14],[174],628⟩,⟨82,(-1),[1,2,5,6,13,14],[186],629⟩,⟨82,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],630⟩,⟨82,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨82,(-1),[1,5,6,13],[194,198],630⟩,⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩,⟨82,(-1),[2,6,9,10,14],[16,20],387⟩,⟨82,(-1),[2,6,14],[40,44,56,60],387⟩,⟨82,(-1),[2,6,14],[211,215,235,239,251,255],391⟩,⟨82,(-1),[2,6,14],[190],629⟩,⟨82,(-1),[5,6],[131,135],391⟩,⟨82,(-1),[6],[195,199],391⟩,⟨84,(0),[1,5,6,13],[170],3⟩,⟨84,(1),[1,5,6,13],[170],3⟩,⟨84,(2),[1,5,6,13],[170],3⟩,⟨84,(3),[1,5,6,13],[170],3⟩,⟨84,(4),[1,5,6,13],[170],3⟩,⟨84,(5),[1,5,6,13],[170],3⟩,⟨84,(6),[1,5,6,13],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1599
end Section14Records_6_1568_1600

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1568_1600


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1600_1632
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1600_1632
private theorem valid1600 : RecordDataValid section14Catalog 6 (⟨84,(7),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1601 : RecordDataValid section14Catalog 6 (⟨84,(8),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1602 : RecordDataValid section14Catalog 6 (⟨84,(9),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1603 : RecordDataValid section14Catalog 6 (⟨84,(10),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1604 : RecordDataValid section14Catalog 6 (⟨84,(11),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1605 : RecordDataValid section14Catalog 6 (⟨84,(12),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1606 : RecordDataValid section14Catalog 6 (⟨84,(13),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1607 : RecordDataValid section14Catalog 6 (⟨84,(14),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1608 : RecordDataValid section14Catalog 6 (⟨84,(15),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1609 : RecordDataValid section14Catalog 6 (⟨84,(16),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1610 : RecordDataValid section14Catalog 6 (⟨84,(17),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1611 : RecordDataValid section14Catalog 6 (⟨84,(18),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1612 : RecordDataValid section14Catalog 6 (⟨84,(19),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1613 : RecordDataValid section14Catalog 6 (⟨84,(20),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1614 : RecordDataValid section14Catalog 6 (⟨84,(21),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1615 : RecordDataValid section14Catalog 6 (⟨84,(22),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1616 : RecordDataValid section14Catalog 6 (⟨84,(23),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1617 : RecordDataValid section14Catalog 6 (⟨84,(24),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1618 : RecordDataValid section14Catalog 6 (⟨86,(0),[1,5,6,13],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1619 : RecordDataValid section14Catalog 6 (⟨86,(1),[1,5,6,13],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1620 : RecordDataValid section14Catalog 6 (⟨86,(2),[1,5,6,13],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1621 : RecordDataValid section14Catalog 6 (⟨86,(3),[1,5,6,13],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1622 : RecordDataValid section14Catalog 6 (⟨86,(4),[1,5,6,13],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1623 : RecordDataValid section14Catalog 6 (⟨86,(5),[1,5,6,13],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1624 : RecordDataValid section14Catalog 6 (⟨86,(6),[1,5,6,13],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1625 : RecordDataValid section14Catalog 6 (⟨86,(7),[1,5,6,13],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1626 : RecordDataValid section14Catalog 6 (⟨86,(8),[1,5,6,13],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1627 : RecordDataValid section14Catalog 6 (⟨86,(9),[1,5,6,13],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1628 : RecordDataValid section14Catalog 6 (⟨86,(10),[1,5,6,13],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1629 : RecordDataValid section14Catalog 6 (⟨86,(11),[1,5,6,13],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1630 : RecordDataValid section14Catalog 6 (⟨86,(12),[1,5,6,13],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1631 : RecordDataValid section14Catalog 6 (⟨86,(13),[1,5,6,13],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1600_1632 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1600).take 32 = [⟨84,(7),[1,5,6,13],[170],3⟩,⟨84,(8),[1,5,6,13],[170],3⟩,⟨84,(9),[1,5,6,13],[170],3⟩,⟨84,(10),[1,5,6,13],[170],3⟩,⟨84,(11),[1,5,6,13],[170],3⟩,⟨84,(12),[1,5,6,13],[170],3⟩,⟨84,(13),[1,5,6,13],[170],3⟩,⟨84,(14),[1,5,6,13],[170],3⟩,⟨84,(15),[1,5,6,13],[170],3⟩,⟨84,(16),[1,5,6,13],[170],3⟩,⟨84,(17),[1,5,6,13],[170],3⟩,⟨84,(18),[1,5,6,13],[170],3⟩,⟨84,(19),[1,5,6,13],[170],3⟩,⟨84,(20),[1,5,6,13],[170],3⟩,⟨84,(21),[1,5,6,13],[170],3⟩,⟨84,(22),[1,5,6,13],[170],3⟩,⟨84,(23),[1,5,6,13],[170],3⟩,⟨84,(24),[1,5,6,13],[170],3⟩,⟨86,(0),[1,5,6,13],[170],10⟩,⟨86,(1),[1,5,6,13],[170],393⟩,⟨86,(2),[1,5,6,13],[170],394⟩,⟨86,(3),[1,5,6,13],[170],395⟩,⟨86,(4),[1,5,6,13],[170],396⟩,⟨86,(5),[1,5,6,13],[170],10⟩,⟨86,(6),[1,5,6,13],[170],393⟩,⟨86,(7),[1,5,6,13],[170],394⟩,⟨86,(8),[1,5,6,13],[170],395⟩,⟨86,(9),[1,5,6,13],[170],396⟩,⟨86,(10),[1,5,6,13],[170],18⟩,⟨86,(11),[1,5,6,13],[170],397⟩,⟨86,(12),[1,5,6,13],[170],397⟩,⟨86,(13),[1,5,6,13],[170],397⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1600
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1601
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1602
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1603
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1604
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1605
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1606
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1607
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1608
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1609
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1610
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1611
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1612
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1613
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1614
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1615
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1616
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1617
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1618
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1619
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1620
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1621
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1622
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1623
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1624
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1625
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1626
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1627
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1628
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1629
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1630
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1631
end Section14Records_6_1600_1632

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1600_1632


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1632_1664
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1632_1664
private theorem valid1632 : RecordDataValid section14Catalog 6 (⟨86,(14),[1,5,6,13],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1633 : RecordDataValid section14Catalog 6 (⟨86,(15),[1,5,6,13],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1634 : RecordDataValid section14Catalog 6 (⟨86,(16),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1635 : RecordDataValid section14Catalog 6 (⟨86,(17),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1636 : RecordDataValid section14Catalog 6 (⟨86,(18),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1637 : RecordDataValid section14Catalog 6 (⟨86,(19),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1638 : RecordDataValid section14Catalog 6 (⟨86,(20),[1,5,6,13],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1639 : RecordDataValid section14Catalog 6 (⟨86,(21),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1640 : RecordDataValid section14Catalog 6 (⟨86,(22),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1641 : RecordDataValid section14Catalog 6 (⟨86,(23),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1642 : RecordDataValid section14Catalog 6 (⟨86,(24),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1643 : RecordDataValid section14Catalog 6 (⟨89,(0),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1644 : RecordDataValid section14Catalog 6 (⟨89,(1),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1645 : RecordDataValid section14Catalog 6 (⟨89,(2),[1,5,6,13],[170],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1646 : RecordDataValid section14Catalog 6 (⟨89,(3),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1647 : RecordDataValid section14Catalog 6 (⟨89,(4),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1648 : RecordDataValid section14Catalog 6 (⟨89,(5),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1649 : RecordDataValid section14Catalog 6 (⟨89,(6),[1,5,6,13],[170],404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨404,[1,4,5,6,8,9,10,12,13,16],405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1650 : RecordDataValid section14Catalog 6 (⟨89,(7),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1651 : RecordDataValid section14Catalog 6 (⟨89,(8),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1652 : RecordDataValid section14Catalog 6 (⟨89,(9),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1653 : RecordDataValid section14Catalog 6 (⟨89,(10),[1,5,6,13],[170],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1654 : RecordDataValid section14Catalog 6 (⟨89,(11),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1655 : RecordDataValid section14Catalog 6 (⟨89,(12),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1656 : RecordDataValid section14Catalog 6 (⟨89,(13),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1657 : RecordDataValid section14Catalog 6 (⟨89,(14),[1,5,6,13],[170],405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨405,[1,4,5,6,8,9,10,12,13,16],406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1658 : RecordDataValid section14Catalog 6 (⟨89,(15),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1659 : RecordDataValid section14Catalog 6 (⟨92,(0),[1,5,6,13],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1660 : RecordDataValid section14Catalog 6 (⟨92,(1),[1,5,6,13],[170],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1661 : RecordDataValid section14Catalog 6 (⟨92,(2),[1,5,6,13],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1662 : RecordDataValid section14Catalog 6 (⟨92,(3),[1,5,6,13],[170],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1663 : RecordDataValid section14Catalog 6 (⟨92,(4),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1632_1664 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1632).take 32 = [⟨86,(14),[1,5,6,13],[170],396⟩,⟨86,(15),[1,5,6,13],[170],21⟩,⟨86,(16),[1,5,6,13],[170],398⟩,⟨86,(17),[1,5,6,13],[170],398⟩,⟨86,(18),[1,5,6,13],[170],398⟩,⟨86,(19),[1,5,6,13],[170],398⟩,⟨86,(20),[1,5,6,13],[170],24⟩,⟨86,(21),[1,5,6,13],[170],399⟩,⟨86,(22),[1,5,6,13],[170],399⟩,⟨86,(23),[1,5,6,13],[170],399⟩,⟨86,(24),[1,5,6,13],[170],399⟩,⟨89,(0),[1,5,6,13],[170],400⟩,⟨89,(1),[1,5,6,13],[170],401⟩,⟨89,(2),[1,5,6,13],[170],402⟩,⟨89,(3),[1,5,6,13],[170],403⟩,⟨89,(4),[1,5,6,13],[170],400⟩,⟨89,(5),[1,5,6,13],[170],401⟩,⟨89,(6),[1,5,6,13],[170],404⟩,⟨89,(7),[1,5,6,13],[170],403⟩,⟨89,(8),[1,5,6,13],[170],400⟩,⟨89,(9),[1,5,6,13],[170],401⟩,⟨89,(10),[1,5,6,13],[170],402⟩,⟨89,(11),[1,5,6,13],[170],403⟩,⟨89,(12),[1,5,6,13],[170],400⟩,⟨89,(13),[1,5,6,13],[170],401⟩,⟨89,(14),[1,5,6,13],[170],405⟩,⟨89,(15),[1,5,6,13],[170],403⟩,⟨92,(0),[1,5,6,13],[170],406⟩,⟨92,(1),[1,5,6,13],[170],407⟩,⟨92,(2),[1,5,6,13],[170],406⟩,⟨92,(3),[1,5,6,13],[170],408⟩,⟨92,(4),[1,5,6,13],[170],409⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1632
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1633
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1634
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1635
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1636
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1637
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1638
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1639
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1640
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1641
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1642
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1643
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1644
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1645
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1646
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1647
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1648
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1649
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1650
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1651
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1652
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1653
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1654
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1655
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1656
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1657
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1658
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1659
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1660
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1661
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1662
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1663
end Section14Records_6_1632_1664

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1632_1664

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1536).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 1536 1600 1664 (by decide) (by decide) (all_of_interval_split P xs 1536 1568 1600 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1536_1568 hnum) (Freiman.workReverse20260919_s0006_records_1568_1600 hnum)) (all_of_interval_split P xs 1600 1632 1664 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1600_1632 hnum) (Freiman.workReverse20260919_s0006_records_1632_1664 hnum)))

#print axioms solution
