-- Prove2me | solution 1 for Freiman.section14_s0009_records_1792_1824
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:01:07.346985+00:00
-- url     : https://prove2.me/submissions/7110d065-00f1-4168-99b2-d93b5a49fdaa

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
namespace Section14Records_9_1792_1824
private theorem valid1792 : RecordDataValid section14Catalog 9 (⟨192,(12),[9],[42],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1793 : RecordDataValid section14Catalog 9 (⟨192,(13),[9],[42],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1794 : RecordDataValid section14Catalog 9 (⟨192,(14),[9],[42],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1795 : RecordDataValid section14Catalog 9 (⟨192,(15),[9],[42],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1796 : RecordDataValid section14Catalog 9 (⟨192,(16),[9],[42],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1797 : RecordDataValid section14Catalog 9 (⟨192,(17),[9],[42],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1798 : RecordDataValid section14Catalog 9 (⟨192,(18),[9],[42],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1799 : RecordDataValid section14Catalog 9 (⟨192,(19),[9],[42],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1800 : RecordDataValid section14Catalog 9 (⟨192,(20),[9],[42],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1801 : RecordDataValid section14Catalog 9 (⟨192,(21),[9],[42],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1802 : RecordDataValid section14Catalog 9 (⟨192,(22),[9],[42],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1803 : RecordDataValid section14Catalog 9 (⟨192,(23),[9],[42],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1804 : RecordDataValid section14Catalog 9 (⟨192,(24),[9],[42],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1805 : RecordDataValid section14Catalog 9 (⟨195,(0),[9,10],[42],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1806 : RecordDataValid section14Catalog 9 (⟨195,(1),[9,10],[42],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1807 : RecordDataValid section14Catalog 9 (⟨195,(2),[9,10],[42],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1808 : RecordDataValid section14Catalog 9 (⟨195,(3),[9,10],[42],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1809 : RecordDataValid section14Catalog 9 (⟨195,(4),[9,10],[42],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1810 : RecordDataValid section14Catalog 9 (⟨195,(5),[9,10],[42],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1811 : RecordDataValid section14Catalog 9 (⟨195,(6),[9,10],[42],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1812 : RecordDataValid section14Catalog 9 (⟨195,(7),[9,10],[42],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1813 : RecordDataValid section14Catalog 9 (⟨195,(8),[9,10],[42],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1814 : RecordDataValid section14Catalog 9 (⟨195,(9),[9,10],[42],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1815 : RecordDataValid section14Catalog 9 (⟨197,(0),[9],[42],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1816 : RecordDataValid section14Catalog 9 (⟨197,(1),[9],[42],1323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1323,[4,8,9,12,16],1327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1817 : RecordDataValid section14Catalog 9 (⟨197,(2),[9],[42],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1818 : RecordDataValid section14Catalog 9 (⟨197,(3),[9],[42],1324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1324,[4,8,9,12,16],1328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1819 : RecordDataValid section14Catalog 9 (⟨197,(4),[9],[42],1325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1325,[4,8,9,12,16],1329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1820 : RecordDataValid section14Catalog 9 (⟨197,(5),[9],[42],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1821 : RecordDataValid section14Catalog 9 (⟨197,(6),[9],[42],1323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1323,[4,8,9,12,16],1327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1822 : RecordDataValid section14Catalog 9 (⟨197,(7),[9],[42],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1823 : RecordDataValid section14Catalog 9 (⟨197,(8),[9],[42],1324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1324,[4,8,9,12,16],1328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1792).take 32 = [⟨192,(12),[9],[42],1319⟩,⟨192,(13),[9],[42],1319⟩,⟨192,(14),[9],[42],1318⟩,⟨192,(15),[9],[42],1320⟩,⟨192,(16),[9],[42],1320⟩,⟨192,(17),[9],[42],1320⟩,⟨192,(18),[9],[42],1320⟩,⟨192,(19),[9],[42],1320⟩,⟨192,(20),[9],[42],1321⟩,⟨192,(21),[9],[42],1321⟩,⟨192,(22),[9],[42],1321⟩,⟨192,(23),[9],[42],1321⟩,⟨192,(24),[9],[42],1321⟩,⟨195,(0),[9,10],[42],697⟩,⟨195,(1),[9,10],[42],697⟩,⟨195,(2),[9,10],[42],698⟩,⟨195,(3),[9,10],[42],698⟩,⟨195,(4),[9,10],[42],699⟩,⟨195,(5),[9,10],[42],700⟩,⟨195,(6),[9,10],[42],699⟩,⟨195,(7),[9,10],[42],701⟩,⟨195,(8),[9,10],[42],702⟩,⟨195,(9),[9,10],[42],703⟩,⟨197,(0),[9],[42],1322⟩,⟨197,(1),[9],[42],1323⟩,⟨197,(2),[9],[42],1322⟩,⟨197,(3),[9],[42],1324⟩,⟨197,(4),[9],[42],1325⟩,⟨197,(5),[9],[42],1322⟩,⟨197,(6),[9],[42],1323⟩,⟨197,(7),[9],[42],1322⟩,⟨197,(8),[9],[42],1324⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1792
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1793
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1794
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1795
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1796
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1797
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1798
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1799
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1800
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1801
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1802
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1803
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1804
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1805
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1806
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1807
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1808
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1809
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1810
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1811
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1812
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1813
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1814
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1815
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1816
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1817
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1818
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1819
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1820
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1821
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1822
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1823
end Section14Records_9_1792_1824

#print axioms solution
