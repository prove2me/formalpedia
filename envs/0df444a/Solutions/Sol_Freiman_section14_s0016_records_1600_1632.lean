-- Prove2me | solution 1 for Freiman.section14_s0016_records_1600_1632
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:40:28.336761+00:00
-- url     : https://prove2.me/submissions/b2aafb3c-fa78-4ee6-9426-97d9d639b704

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
namespace Section14Records_16_1600_1632
private theorem valid1600 : RecordDataValid section14Catalog 16 (⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1601 : RecordDataValid section14Catalog 16 (⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1602 : RecordDataValid section14Catalog 16 (⟨237,(12),[3,4,8,12,15,16],[10],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1603 : RecordDataValid section14Catalog 16 (⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1604 : RecordDataValid section14Catalog 16 (⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1605 : RecordDataValid section14Catalog 16 (⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1606 : RecordDataValid section14Catalog 16 (⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1607 : RecordDataValid section14Catalog 16 (⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1608 : RecordDataValid section14Catalog 16 (⟨238,(2),[4,8,12,16],[10],1390⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1390,[4,8,12,16],1394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1609 : RecordDataValid section14Catalog 16 (⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1610 : RecordDataValid section14Catalog 16 (⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1611 : RecordDataValid section14Catalog 16 (⟨238,(5),[3,4,7,8,12,15,16],[10],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1612 : RecordDataValid section14Catalog 16 (⟨238,(6),[4,8,12,16],[10],1391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1391,[4,8,9,12,16],1396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1613 : RecordDataValid section14Catalog 16 (⟨238,(7),[3,4,7,8,12,15,16],[10],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1614 : RecordDataValid section14Catalog 16 (⟨238,(8),[3,4,7,8,12,15,16],[10],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1615 : RecordDataValid section14Catalog 16 (⟨238,(9),[3,4,7,8,12,15,16],[10],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1616 : RecordDataValid section14Catalog 16 (⟨238,(10),[4,8,12,16],[10],1392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1392,[4,8,9,12,16],1397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1617 : RecordDataValid section14Catalog 16 (⟨238,(11),[3,4,7,8,12,15,16],[10],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1618 : RecordDataValid section14Catalog 16 (⟨238,(12),[3,4,7,8,12,15,16],[10],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1619 : RecordDataValid section14Catalog 16 (⟨238,(13),[3,4,7,8,12,15,16],[10],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1620 : RecordDataValid section14Catalog 16 (⟨238,(14),[4,8,12,16],[10],1393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1393,[4,8,9,12,16],1398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1621 : RecordDataValid section14Catalog 16 (⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1622 : RecordDataValid section14Catalog 16 (⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1623 : RecordDataValid section14Catalog 16 (⟨245,(-1),[4,8,10,16],[8,12],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1624 : RecordDataValid section14Catalog 16 (⟨245,(-1),[4,8,16],[1,5,9,13],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1625 : RecordDataValid section14Catalog 16 (⟨245,(-1),[4,8,16],[2],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1626 : RecordDataValid section14Catalog 16 (⟨245,(-1),[4,8,16],[7,11,15],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1627 : RecordDataValid section14Catalog 16 (⟨245,(-1),[4,8,16],[6],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1628 : RecordDataValid section14Catalog 16 (⟨245,(-1),[4,16],[3],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1629 : RecordDataValid section14Catalog 16 (⟨245,(-1),[4,16],[14],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1630 : RecordDataValid section14Catalog 16 (⟨249,(0),[4,8,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1631 : RecordDataValid section14Catalog 16 (⟨249,(1),[4,8,16],[10],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1600).take 32 = [⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩,⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩,⟨237,(12),[3,4,8,12,15,16],[10],868⟩,⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩,⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩,⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩,⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩,⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩,⟨238,(2),[4,8,12,16],[10],1390⟩,⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩,⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩,⟨238,(5),[3,4,7,8,12,15,16],[10],610⟩,⟨238,(6),[4,8,12,16],[10],1391⟩,⟨238,(7),[3,4,7,8,12,15,16],[10],612⟩,⟨238,(8),[3,4,7,8,12,15,16],[10],613⟩,⟨238,(9),[3,4,7,8,12,15,16],[10],614⟩,⟨238,(10),[4,8,12,16],[10],1392⟩,⟨238,(11),[3,4,7,8,12,15,16],[10],616⟩,⟨238,(12),[3,4,7,8,12,15,16],[10],617⟩,⟨238,(13),[3,4,7,8,12,15,16],[10],618⟩,⟨238,(14),[4,8,12,16],[10],1393⟩,⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩,⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩,⟨245,(-1),[4,8,10,16],[8,12],882⟩,⟨245,(-1),[4,8,16],[1,5,9,13],883⟩,⟨245,(-1),[4,8,16],[2],884⟩,⟨245,(-1),[4,8,16],[7,11,15],886⟩,⟨245,(-1),[4,8,16],[6],887⟩,⟨245,(-1),[4,16],[3],884⟩,⟨245,(-1),[4,16],[14],909⟩,⟨249,(0),[4,8,16],[10],10⟩,⟨249,(1),[4,8,16],[10],11⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1600
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1601
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1602
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1603
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1604
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1605
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1606
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1607
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1608
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1609
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1610
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1611
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1612
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1613
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1614
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1615
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1616
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1617
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1618
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1619
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1620
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1621
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1622
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1623
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1624
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1625
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1626
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1627
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1628
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1629
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1630
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1631
end Section14Records_16_1600_1632

#print axioms solution
