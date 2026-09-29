-- Prove2me | solution 1 for Freiman.section14_s0004_records_1760_1792
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:53:43.265243+00:00
-- url     : https://prove2.me/submissions/218ebe82-f8ee-4299-81b2-330f1d5f74e5

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
namespace Section14Records_4_1760_1792
private theorem valid1760 : RecordDataValid section14Catalog 4 (⟨228,(3),[3,4,8,12,15,16],[10],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1761 : RecordDataValid section14Catalog 4 (⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1762 : RecordDataValid section14Catalog 4 (⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1763 : RecordDataValid section14Catalog 4 (⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1764 : RecordDataValid section14Catalog 4 (⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1765 : RecordDataValid section14Catalog 4 (⟨228,(8),[3,4,7,8,12,15,16],[10],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1766 : RecordDataValid section14Catalog 4 (⟨228,(9),[3,4,7,15,16],[10],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1767 : RecordDataValid section14Catalog 4 (⟨228,(10),[3,4,7,8,12,15,16],[10],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1768 : RecordDataValid section14Catalog 4 (⟨228,(11),[3,4,7,8,12,15,16],[10],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1769 : RecordDataValid section14Catalog 4 (⟨228,(12),[3,4,7,8,12,15,16],[10],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1770 : RecordDataValid section14Catalog 4 (⟨228,(13),[3,4,7,8,12,15,16],[10],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1771 : RecordDataValid section14Catalog 4 (⟨228,(14),[3,4,7,8,12,15,16],[10],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1772 : RecordDataValid section14Catalog 4 (⟨228,(15),[3,4,7,8,12,15,16],[10],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1773 : RecordDataValid section14Catalog 4 (⟨228,(16),[3,4,7,8,12,15,16],[10],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1774 : RecordDataValid section14Catalog 4 (⟨228,(17),[3,4,7,8,12,15,16],[10],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1775 : RecordDataValid section14Catalog 4 (⟨228,(18),[3,4,7,8,12,15,16],[10],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1776 : RecordDataValid section14Catalog 4 (⟨228,(19),[3,4,7,8,12,15,16],[10],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1777 : RecordDataValid section14Catalog 4 (⟨228,(20),[3,4,7,8,12,15,16],[10],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1778 : RecordDataValid section14Catalog 4 (⟨228,(21),[3,4,7,8,12,15,16],[10],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1779 : RecordDataValid section14Catalog 4 (⟨228,(22),[3,4,7,8,12,15,16],[10],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1780 : RecordDataValid section14Catalog 4 (⟨228,(23),[3,4,7,8,12,15,16],[10],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1781 : RecordDataValid section14Catalog 4 (⟨228,(24),[3,4,7,8,12,15,16],[10],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1782 : RecordDataValid section14Catalog 4 (⟨230,(0),[3,4,7,8,12,15,16],[10],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1783 : RecordDataValid section14Catalog 4 (⟨230,(1),[3,4,7,8,15,16],[10],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1784 : RecordDataValid section14Catalog 4 (⟨230,(2),[3,4,7,8,12,15,16],[10],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1785 : RecordDataValid section14Catalog 4 (⟨230,(3),[3,4,7,8,12,15,16],[10],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1786 : RecordDataValid section14Catalog 4 (⟨230,(4),[3,4,7,8,12,15,16],[10],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1787 : RecordDataValid section14Catalog 4 (⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1788 : RecordDataValid section14Catalog 4 (⟨230,(6),[3,4,7,8,15,16],[10],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1789 : RecordDataValid section14Catalog 4 (⟨230,(7),[4,8,12,16],[10],815⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨815,[1,4,5,6,8,9,10,12,13,16],816⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1790 : RecordDataValid section14Catalog 4 (⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1791 : RecordDataValid section14Catalog 4 (⟨230,(9),[4,8,12,16],[10],1375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1375,[4,5,8,9,12,16],1379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1760).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1760).take 32 = [⟨228,(3),[3,4,8,12,15,16],[10],792⟩,⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩,⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩,⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩,⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩,⟨228,(8),[3,4,7,8,12,15,16],[10],797⟩,⟨228,(9),[3,4,7,15,16],[10],796⟩,⟨228,(10),[3,4,7,8,12,15,16],[10],798⟩,⟨228,(11),[3,4,7,8,12,15,16],[10],799⟩,⟨228,(12),[3,4,7,8,12,15,16],[10],800⟩,⟨228,(13),[3,4,7,8,12,15,16],[10],801⟩,⟨228,(14),[3,4,7,8,12,15,16],[10],800⟩,⟨228,(15),[3,4,7,8,12,15,16],[10],802⟩,⟨228,(16),[3,4,7,8,12,15,16],[10],803⟩,⟨228,(17),[3,4,7,8,12,15,16],[10],804⟩,⟨228,(18),[3,4,7,8,12,15,16],[10],805⟩,⟨228,(19),[3,4,7,8,12,15,16],[10],804⟩,⟨228,(20),[3,4,7,8,12,15,16],[10],806⟩,⟨228,(21),[3,4,7,8,12,15,16],[10],807⟩,⟨228,(22),[3,4,7,8,12,15,16],[10],808⟩,⟨228,(23),[3,4,7,8,12,15,16],[10],809⟩,⟨228,(24),[3,4,7,8,12,15,16],[10],808⟩,⟨230,(0),[3,4,7,8,12,15,16],[10],810⟩,⟨230,(1),[3,4,7,8,15,16],[10],811⟩,⟨230,(2),[3,4,7,8,12,15,16],[10],812⟩,⟨230,(3),[3,4,7,8,12,15,16],[10],813⟩,⟨230,(4),[3,4,7,8,12,15,16],[10],814⟩,⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩,⟨230,(6),[3,4,7,8,15,16],[10],811⟩,⟨230,(7),[4,8,12,16],[10],815⟩,⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩,⟨230,(9),[4,8,12,16],[10],1375⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1760
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1761
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1762
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1763
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1764
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1765
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1766
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1767
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1768
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1769
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1770
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1771
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1772
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1773
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1774
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1775
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1776
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1777
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1778
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1779
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1780
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1781
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1782
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1783
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1784
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1785
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1786
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1787
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1788
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1789
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1790
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1791
end Section14Records_4_1760_1792

#print axioms solution
