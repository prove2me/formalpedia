-- Prove2me | solution 1 for Freiman.section14_s0016_records_1504_1536
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:34:38.914569+00:00
-- url     : https://prove2.me/submissions/2d85ee20-ec16-4f4a-b3be-2893f3ddbd08

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
namespace Section14Records_16_1504_1536
private theorem valid1504 : RecordDataValid section14Catalog 16 (⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1505 : RecordDataValid section14Catalog 16 (⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1506 : RecordDataValid section14Catalog 16 (⟨230,(17),[4,8,12,16],[10],1376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1376,[4,8,9,12,16],1380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1507 : RecordDataValid section14Catalog 16 (⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1508 : RecordDataValid section14Catalog 16 (⟨230,(19),[4,8,12,16],[10],1376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1376,[4,8,9,12,16],1380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1509 : RecordDataValid section14Catalog 16 (⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1510 : RecordDataValid section14Catalog 16 (⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1511 : RecordDataValid section14Catalog 16 (⟨230,(22),[4,8,12,16],[10],1377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1377,[4,8,9,12,16],1381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1512 : RecordDataValid section14Catalog 16 (⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1513 : RecordDataValid section14Catalog 16 (⟨230,(24),[4,8,12,16],[10],1377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1377,[4,8,9,12,16],1381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1514 : RecordDataValid section14Catalog 16 (⟨231,(0),[3,4,8,12,15,16],[10],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1515 : RecordDataValid section14Catalog 16 (⟨231,(1),[3,4,7,15,16],[10],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1516 : RecordDataValid section14Catalog 16 (⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1517 : RecordDataValid section14Catalog 16 (⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1518 : RecordDataValid section14Catalog 16 (⟨231,(4),[3,4,8,12,15,16],[10],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1519 : RecordDataValid section14Catalog 16 (⟨231,(5),[3,4,7,15,16],[10],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1520 : RecordDataValid section14Catalog 16 (⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1521 : RecordDataValid section14Catalog 16 (⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1522 : RecordDataValid section14Catalog 16 (⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1523 : RecordDataValid section14Catalog 16 (⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1524 : RecordDataValid section14Catalog 16 (⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1525 : RecordDataValid section14Catalog 16 (⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1526 : RecordDataValid section14Catalog 16 (⟨231,(12),[3,4,7,8,12,15,16],[10],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1527 : RecordDataValid section14Catalog 16 (⟨231,(13),[3,4,7,8,12,15,16],[10],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1528 : RecordDataValid section14Catalog 16 (⟨231,(14),[3,4,7,8,12,15,16],[10],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1529 : RecordDataValid section14Catalog 16 (⟨231,(15),[3,4,7,8,12,15,16],[10],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1530 : RecordDataValid section14Catalog 16 (⟨231,(16),[3,4,7,8,12,15,16],[10],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1531 : RecordDataValid section14Catalog 16 (⟨231,(17),[3,4,7,8,12,15,16],[10],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1532 : RecordDataValid section14Catalog 16 (⟨231,(18),[3,4,7,8,12,15,16],[10],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1533 : RecordDataValid section14Catalog 16 (⟨231,(19),[3,4,7,8,12,15,16],[10],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1534 : RecordDataValid section14Catalog 16 (⟨232,(0),[3,4,7,8,12,15,16],[10],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1535 : RecordDataValid section14Catalog 16 (⟨232,(1),[3,4,7,8,12,15,16],[10],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1504).take 32 = [⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩,⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩,⟨230,(17),[4,8,12,16],[10],1376⟩,⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩,⟨230,(19),[4,8,12,16],[10],1376⟩,⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩,⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩,⟨230,(22),[4,8,12,16],[10],1377⟩,⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩,⟨230,(24),[4,8,12,16],[10],1377⟩,⟨231,(0),[3,4,8,12,15,16],[10],830⟩,⟨231,(1),[3,4,7,15,16],[10],831⟩,⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩,⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩,⟨231,(4),[3,4,8,12,15,16],[10],830⟩,⟨231,(5),[3,4,7,15,16],[10],831⟩,⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩,⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩,⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩,⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩,⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩,⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩,⟨231,(12),[3,4,7,8,12,15,16],[10],838⟩,⟨231,(13),[3,4,7,8,12,15,16],[10],839⟩,⟨231,(14),[3,4,7,8,12,15,16],[10],838⟩,⟨231,(15),[3,4,7,8,12,15,16],[10],840⟩,⟨231,(16),[3,4,7,8,12,15,16],[10],841⟩,⟨231,(17),[3,4,7,8,12,15,16],[10],842⟩,⟨231,(18),[3,4,7,8,12,15,16],[10],841⟩,⟨231,(19),[3,4,7,8,12,15,16],[10],843⟩,⟨232,(0),[3,4,7,8,12,15,16],[10],844⟩,⟨232,(1),[3,4,7,8,12,15,16],[10],845⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1504
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1505
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1506
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1507
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1508
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1509
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1510
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1511
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1512
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1513
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1514
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1515
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1516
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1517
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1518
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1519
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1520
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1521
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1522
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1523
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1524
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1525
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1526
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1527
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1528
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1529
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1530
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1531
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1532
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1533
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1534
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1535
end Section14Records_16_1504_1536

#print axioms solution
