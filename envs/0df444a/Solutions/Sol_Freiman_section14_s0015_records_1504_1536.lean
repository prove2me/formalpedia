-- Prove2me | solution 1 for Freiman.section14_s0015_records_1504_1536
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:26:26.015611+00:00
-- url     : https://prove2.me/submissions/a18fa7e4-2705-4be1-b18a-e5bb89888a0f

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
namespace Section14Records_15_1504_1536
private theorem valid1504 : RecordDataValid section14Catalog 15 (⟨446,(24),[3,7,15],[10],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1505 : RecordDataValid section14Catalog 15 (⟨448,(0),[3,7,15],[10],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1506 : RecordDataValid section14Catalog 15 (⟨448,(1),[3,7,15],[10],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1507 : RecordDataValid section14Catalog 15 (⟨448,(2),[3,7,15],[10],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1508 : RecordDataValid section14Catalog 15 (⟨448,(3),[3,7,15],[10],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1509 : RecordDataValid section14Catalog 15 (⟨448,(4),[3,7,15],[10],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1510 : RecordDataValid section14Catalog 15 (⟨448,(5),[3,7,15],[10],1163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1163,[3,7,11,15],1167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1511 : RecordDataValid section14Catalog 15 (⟨448,(6),[3,7,15],[10],1163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1163,[3,7,11,15],1167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1512 : RecordDataValid section14Catalog 15 (⟨448,(7),[3,7,15],[10],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1513 : RecordDataValid section14Catalog 15 (⟨448,(8),[3,7,15],[10],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1514 : RecordDataValid section14Catalog 15 (⟨448,(9),[3,7,15],[10],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1515 : RecordDataValid section14Catalog 15 (⟨448,(10),[3,7,15],[10],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1516 : RecordDataValid section14Catalog 15 (⟨448,(11),[3,7,15],[10],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1517 : RecordDataValid section14Catalog 15 (⟨448,(12),[3,7,15],[10],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1518 : RecordDataValid section14Catalog 15 (⟨448,(13),[3,7,15],[10],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1519 : RecordDataValid section14Catalog 15 (⟨448,(14),[3,7,15],[10],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1520 : RecordDataValid section14Catalog 15 (⟨448,(15),[3,7,15],[10],1164⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1164,[3,7,11,15],1168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1521 : RecordDataValid section14Catalog 15 (⟨448,(16),[3,7,15],[10],1164⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1164,[3,7,11,15],1168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1522 : RecordDataValid section14Catalog 15 (⟨448,(17),[3,7,15],[10],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1523 : RecordDataValid section14Catalog 15 (⟨448,(18),[3,7,15],[10],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1524 : RecordDataValid section14Catalog 15 (⟨448,(19),[3,7,15],[10],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1525 : RecordDataValid section14Catalog 15 (⟨448,(20),[3,7,15],[10],1165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1165,[3,7,11,15],1169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1526 : RecordDataValid section14Catalog 15 (⟨448,(21),[3,7,15],[10],1165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1165,[3,7,11,15],1169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1527 : RecordDataValid section14Catalog 15 (⟨448,(22),[3,7,15],[10],1165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1165,[3,7,11,15],1169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1528 : RecordDataValid section14Catalog 15 (⟨448,(23),[3,7,15],[10],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1529 : RecordDataValid section14Catalog 15 (⟨448,(24),[3,7,15],[10],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1530 : RecordDataValid section14Catalog 15 (⟨450,(0),[3,7,15],[10],1166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1166,[3,7,11,15],1170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1531 : RecordDataValid section14Catalog 15 (⟨450,(1),[3,7,15],[10],1167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1167,[3,7,11,15],1171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1532 : RecordDataValid section14Catalog 15 (⟨450,(2),[3,7,15],[10],1168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1168,[3,7,11,15],1172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1533 : RecordDataValid section14Catalog 15 (⟨450,(3),[3,7,15],[10],1169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1169,[3,7,11,15],1173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1534 : RecordDataValid section14Catalog 15 (⟨453,(0),[3,7,15],[10],1170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1170,[3,7,11,15],1174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1535 : RecordDataValid section14Catalog 15 (⟨453,(1),[3,7,15],[10],1171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1171,[3,7,11,15],1175⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1504).take 32 = [⟨446,(24),[3,7,15],[10],1158⟩,⟨448,(0),[3,7,15],[10],1159⟩,⟨448,(1),[3,7,15],[10],1159⟩,⟨448,(2),[3,7,15],[10],1160⟩,⟨448,(3),[3,7,15],[10],1161⟩,⟨448,(4),[3,7,15],[10],1162⟩,⟨448,(5),[3,7,15],[10],1163⟩,⟨448,(6),[3,7,15],[10],1163⟩,⟨448,(7),[3,7,15],[10],1160⟩,⟨448,(8),[3,7,15],[10],1161⟩,⟨448,(9),[3,7,15],[10],1162⟩,⟨448,(10),[3,7,15],[10],1159⟩,⟨448,(11),[3,7,15],[10],1159⟩,⟨448,(12),[3,7,15],[10],1160⟩,⟨448,(13),[3,7,15],[10],1161⟩,⟨448,(14),[3,7,15],[10],1162⟩,⟨448,(15),[3,7,15],[10],1164⟩,⟨448,(16),[3,7,15],[10],1164⟩,⟨448,(17),[3,7,15],[10],1160⟩,⟨448,(18),[3,7,15],[10],1161⟩,⟨448,(19),[3,7,15],[10],1162⟩,⟨448,(20),[3,7,15],[10],1165⟩,⟨448,(21),[3,7,15],[10],1165⟩,⟨448,(22),[3,7,15],[10],1165⟩,⟨448,(23),[3,7,15],[10],1161⟩,⟨448,(24),[3,7,15],[10],1162⟩,⟨450,(0),[3,7,15],[10],1166⟩,⟨450,(1),[3,7,15],[10],1167⟩,⟨450,(2),[3,7,15],[10],1168⟩,⟨450,(3),[3,7,15],[10],1169⟩,⟨453,(0),[3,7,15],[10],1170⟩,⟨453,(1),[3,7,15],[10],1171⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1504
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1505
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1506
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1507
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1508
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1509
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1510
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1511
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1512
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1513
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1514
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1515
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1516
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1517
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1518
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1519
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1520
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1521
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1522
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1523
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1524
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1525
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1526
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1527
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1528
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1529
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1530
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1531
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1532
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1533
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1534
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1535
end Section14Records_15_1504_1536

#print axioms solution
