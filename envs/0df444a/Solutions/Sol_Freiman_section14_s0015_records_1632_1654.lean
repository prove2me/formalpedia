-- Prove2me | solution 1 for Freiman.section14_s0015_records_1632_1654
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:31:45.302991+00:00
-- url     : https://prove2.me/submissions/79071acf-a95c-4e0f-ac3f-3c04c46a32d5

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
namespace Section14Records_15_1632_1654
private theorem valid1632 : RecordDataValid section14Catalog 15 (⟨472,(16),[3,7,15],[10],1242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1242,[3,5,7,8,9,11,12,15],1246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1633 : RecordDataValid section14Catalog 15 (⟨472,(17),[3,7,15],[10],1243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1243,[3,5,7,8,9,11,12,15],1247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1634 : RecordDataValid section14Catalog 15 (⟨472,(18),[3,7,15],[10],1244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1244,[3,7,11,15],1248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1635 : RecordDataValid section14Catalog 15 (⟨472,(19),[3,7,15],[10],1244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1244,[3,7,11,15],1248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1636 : RecordDataValid section14Catalog 15 (⟨475,(5),[7,15],[10],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1637 : RecordDataValid section14Catalog 15 (⟨475,(7),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1638 : RecordDataValid section14Catalog 15 (⟨475,(8),[3,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1639 : RecordDataValid section14Catalog 15 (⟨475,(9),[7,15],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1640 : RecordDataValid section14Catalog 15 (⟨475,(15),[3,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1641 : RecordDataValid section14Catalog 15 (⟨475,(16),[3,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1642 : RecordDataValid section14Catalog 15 (⟨475,(17),[3,7,15],[10],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1643 : RecordDataValid section14Catalog 15 (⟨475,(19),[15],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1644 : RecordDataValid section14Catalog 15 (⟨636,(0),[15,16],[10],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1645 : RecordDataValid section14Catalog 15 (⟨636,(1),[15,16],[10],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1646 : RecordDataValid section14Catalog 15 (⟨636,(2),[15,16],[10],1725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1725,[13,14,15,16],1730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1647 : RecordDataValid section14Catalog 15 (⟨636,(3),[15,16],[10],1725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1725,[13,14,15,16],1730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1648 : RecordDataValid section14Catalog 15 (⟨636,(4),[15,16],[10],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1649 : RecordDataValid section14Catalog 15 (⟨636,(5),[15,16],[10],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1650 : RecordDataValid section14Catalog 15 (⟨636,(6),[15,16],[10],1726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1726,[13,14,15,16],1731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1651 : RecordDataValid section14Catalog 15 (⟨636,(7),[15,16],[10],1726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1726,[13,14,15,16],1731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1652 : RecordDataValid section14Catalog 15 (⟨636,(8),[15,16],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1653 : RecordDataValid section14Catalog 15 (⟨636,(9),[15,16],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1632).take 22, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1632).take 22 = [⟨472,(16),[3,7,15],[10],1242⟩,⟨472,(17),[3,7,15],[10],1243⟩,⟨472,(18),[3,7,15],[10],1244⟩,⟨472,(19),[3,7,15],[10],1244⟩,⟨475,(5),[7,15],[10],105⟩,⟨475,(7),[3,7,15],[10],3⟩,⟨475,(8),[3,15],[10],3⟩,⟨475,(9),[7,15],[10],143⟩,⟨475,(15),[3,15],[10],3⟩,⟨475,(16),[3,15],[10],3⟩,⟨475,(17),[3,7,15],[10],48⟩,⟨475,(19),[15],[10],143⟩,⟨636,(0),[15,16],[10],1724⟩,⟨636,(1),[15,16],[10],1724⟩,⟨636,(2),[15,16],[10],1725⟩,⟨636,(3),[15,16],[10],1725⟩,⟨636,(4),[15,16],[10],1724⟩,⟨636,(5),[15,16],[10],1724⟩,⟨636,(6),[15,16],[10],1726⟩,⟨636,(7),[15,16],[10],1726⟩,⟨636,(8),[15,16],[10],47⟩,⟨636,(9),[15,16],[10],47⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1632
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1633
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1634
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1635
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1636
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1637
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1638
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1639
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1640
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1641
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1642
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1643
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1644
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1645
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1646
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1647
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1648
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1649
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1650
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1651
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1652
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1653
end Section14Records_15_1632_1654

#print axioms solution
