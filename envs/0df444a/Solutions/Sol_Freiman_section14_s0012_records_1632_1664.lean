-- Prove2me | solution 1 for Freiman.section14_s0012_records_1632_1664
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:03:41.696024+00:00
-- url     : https://prove2.me/submissions/69baf9ae-f044-45a8-a387-f79a82353991

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
namespace Section14Records_12_1632_1664
private theorem valid1632 : RecordDataValid section14Catalog 12 (⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1633 : RecordDataValid section14Catalog 12 (⟨231,(12),[3,4,7,8,12,15,16],[10],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1634 : RecordDataValid section14Catalog 12 (⟨231,(13),[3,4,7,8,12,15,16],[10],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1635 : RecordDataValid section14Catalog 12 (⟨231,(14),[3,4,7,8,12,15,16],[10],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1636 : RecordDataValid section14Catalog 12 (⟨231,(15),[3,4,7,8,12,15,16],[10],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1637 : RecordDataValid section14Catalog 12 (⟨231,(16),[3,4,7,8,12,15,16],[10],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1638 : RecordDataValid section14Catalog 12 (⟨231,(17),[3,4,7,8,12,15,16],[10],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1639 : RecordDataValid section14Catalog 12 (⟨231,(18),[3,4,7,8,12,15,16],[10],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1640 : RecordDataValid section14Catalog 12 (⟨231,(19),[3,4,7,8,12,15,16],[10],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1641 : RecordDataValid section14Catalog 12 (⟨232,(0),[3,4,7,8,12,15,16],[10],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1642 : RecordDataValid section14Catalog 12 (⟨232,(1),[3,4,7,8,12,15,16],[10],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1643 : RecordDataValid section14Catalog 12 (⟨232,(2),[3,4,7,8,12,15,16],[10],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1644 : RecordDataValid section14Catalog 12 (⟨232,(3),[3,4,7,8,12,15,16],[10],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1645 : RecordDataValid section14Catalog 12 (⟨232,(4),[4,8,12,16],[10],848⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1646 : RecordDataValid section14Catalog 12 (⟨232,(5),[3,4,7,8,12,15,16],[10],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1647 : RecordDataValid section14Catalog 12 (⟨232,(6),[3,4,7,8,12,15,16],[10],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1648 : RecordDataValid section14Catalog 12 (⟨232,(7),[3,4,7,8,12,15,16],[10],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1649 : RecordDataValid section14Catalog 12 (⟨232,(8),[3,4,7,8,12,15,16],[10],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1650 : RecordDataValid section14Catalog 12 (⟨232,(9),[4,8,12,16],[10],1378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1378,[4,8,9,12,16],1382⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1651 : RecordDataValid section14Catalog 12 (⟨232,(10),[3,4,7,8,12,15,16],[10],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1652 : RecordDataValid section14Catalog 12 (⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1653 : RecordDataValid section14Catalog 12 (⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1654 : RecordDataValid section14Catalog 12 (⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1655 : RecordDataValid section14Catalog 12 (⟨232,(14),[4,8,12,16],[10],1379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1379,[4,8,9,12,16],1383⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1656 : RecordDataValid section14Catalog 12 (⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1657 : RecordDataValid section14Catalog 12 (⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1658 : RecordDataValid section14Catalog 12 (⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1659 : RecordDataValid section14Catalog 12 (⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1660 : RecordDataValid section14Catalog 12 (⟨232,(19),[4,8,12,16],[10],1380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1380,[4,8,9,12,16],1384⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1661 : RecordDataValid section14Catalog 12 (⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1662 : RecordDataValid section14Catalog 12 (⟨234,(1),[4,8,12,16],[10],1381⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1381,[4,8,9,12,16],1385⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1663 : RecordDataValid section14Catalog 12 (⟨234,(2),[4,8,12,16],[10],1382⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1382,[4,8,9,12,16],1386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1632).take 32 = [⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩,⟨231,(12),[3,4,7,8,12,15,16],[10],838⟩,⟨231,(13),[3,4,7,8,12,15,16],[10],839⟩,⟨231,(14),[3,4,7,8,12,15,16],[10],838⟩,⟨231,(15),[3,4,7,8,12,15,16],[10],840⟩,⟨231,(16),[3,4,7,8,12,15,16],[10],841⟩,⟨231,(17),[3,4,7,8,12,15,16],[10],842⟩,⟨231,(18),[3,4,7,8,12,15,16],[10],841⟩,⟨231,(19),[3,4,7,8,12,15,16],[10],843⟩,⟨232,(0),[3,4,7,8,12,15,16],[10],844⟩,⟨232,(1),[3,4,7,8,12,15,16],[10],845⟩,⟨232,(2),[3,4,7,8,12,15,16],[10],846⟩,⟨232,(3),[3,4,7,8,12,15,16],[10],847⟩,⟨232,(4),[4,8,12,16],[10],848⟩,⟨232,(5),[3,4,7,8,12,15,16],[10],849⟩,⟨232,(6),[3,4,7,8,12,15,16],[10],850⟩,⟨232,(7),[3,4,7,8,12,15,16],[10],851⟩,⟨232,(8),[3,4,7,8,12,15,16],[10],852⟩,⟨232,(9),[4,8,12,16],[10],1378⟩,⟨232,(10),[3,4,7,8,12,15,16],[10],844⟩,⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩,⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩,⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩,⟨232,(14),[4,8,12,16],[10],1379⟩,⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩,⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩,⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩,⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩,⟨232,(19),[4,8,12,16],[10],1380⟩,⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩,⟨234,(1),[4,8,12,16],[10],1381⟩,⟨234,(2),[4,8,12,16],[10],1382⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1632
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1633
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1634
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1635
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1636
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1637
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1638
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1639
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1640
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1641
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1642
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1643
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1644
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1645
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1646
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1647
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1648
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1649
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1650
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1651
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1652
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1653
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1654
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1655
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1656
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1657
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1658
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1659
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1660
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1661
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1662
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1663
end Section14Records_12_1632_1664

#print axioms solution
