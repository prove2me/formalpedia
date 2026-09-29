-- Prove2me | solution 1 for Freiman.section14_s0012_records_0000_0032
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:11:55.271742+00:00
-- url     : https://prove2.me/submissions/e141571d-ae00-448b-b898-2905bec506d9

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
namespace Section14Records_12_0_32
private theorem valid0 : RecordDataValid section14Catalog 12 (⟨1,(-1),[2,4,6,8,10,12,14,16],[0,4],4⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨4,[1,2,4,5,6,8,9,10,12,13,14,16],4⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1 : RecordDataValid section14Catalog 12 (⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2 : RecordDataValid section14Catalog 12 (⟨1,(-1),[4,8,10,12,16],[8,12],4⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨4,[1,2,4,5,6,8,9,10,12,13,14,16],4⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3 : RecordDataValid section14Catalog 12 (⟨1,(-1),[4,8,11,12,16],[1],5⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4 : RecordDataValid section14Catalog 12 (⟨1,(-1),[4,8,12,16],[9,13],5⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid5 : RecordDataValid section14Catalog 12 (⟨1,(-1),[4,8,12,16],[2],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid6 : RecordDataValid section14Catalog 12 (⟨1,(-1),[4,8,12,16],[7,11,15],8⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨8,[1,2,4,5,6,8,9,10,12,13,14,16],8⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid7 : RecordDataValid section14Catalog 12 (⟨1,(-1),[4,8,12,16],[6],9⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨9,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],9⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid8 : RecordDataValid section14Catalog 12 (⟨1,(-1),[4,8,12,16],[14],55⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨55,[1,2,4,5,6,8,9,10,12,13,14,16],55⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid9 : RecordDataValid section14Catalog 12 (⟨1,(-1),[8,12],[3],8⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨8,[1,2,4,5,6,8,9,10,12,13,14,16],8⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid10 : RecordDataValid section14Catalog 12 (⟨9,(0),[4,8,12,16],[10],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid11 : RecordDataValid section14Catalog 12 (⟨9,(1),[4,8,12,16],[10],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid12 : RecordDataValid section14Catalog 12 (⟨9,(2),[4,8,12,16],[10],28⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨28,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],28⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid13 : RecordDataValid section14Catalog 12 (⟨9,(3),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid14 : RecordDataValid section14Catalog 12 (⟨9,(4),[4,8,12,16],[10],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid15 : RecordDataValid section14Catalog 12 (⟨9,(5),[4,8,12,16],[10],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid16 : RecordDataValid section14Catalog 12 (⟨9,(6),[4,8,12,16],[10],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid17 : RecordDataValid section14Catalog 12 (⟨9,(7),[4,8,12,16],[10],31⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨31,[1,2,4,5,6,8,9,10,12,13,14,16],31⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid18 : RecordDataValid section14Catalog 12 (⟨9,(8),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid19 : RecordDataValid section14Catalog 12 (⟨9,(9),[4,8,12,16],[10],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid20 : RecordDataValid section14Catalog 12 (⟨9,(10),[4,8,12,16],[10],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid21 : RecordDataValid section14Catalog 12 (⟨9,(11),[4,8,12,16],[10],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid22 : RecordDataValid section14Catalog 12 (⟨9,(12),[4,8,12,16],[10],33⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨33,[1,2,4,5,6,8,9,10,12,13,14,16],33⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid23 : RecordDataValid section14Catalog 12 (⟨9,(13),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid24 : RecordDataValid section14Catalog 12 (⟨9,(14),[4,8,12,16],[10],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid25 : RecordDataValid section14Catalog 12 (⟨9,(15),[4,8,12,16],[10],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid26 : RecordDataValid section14Catalog 12 (⟨9,(16),[4,8,12,16],[10],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid27 : RecordDataValid section14Catalog 12 (⟨9,(17),[4,8,12,16],[10],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid28 : RecordDataValid section14Catalog 12 (⟨9,(18),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid29 : RecordDataValid section14Catalog 12 (⟨9,(19),[4,8,12,16],[10],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid30 : RecordDataValid section14Catalog 12 (⟨9,(20),[4,8,12,16],[10],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid31 : RecordDataValid section14Catalog 12 (⟨9,(21),[4,8,12,16],[10],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 0).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 0).take 32 = [⟨1,(-1),[2,4,6,8,10,12,14,16],[0,4],4⟩,⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩,⟨1,(-1),[4,8,10,12,16],[8,12],4⟩,⟨1,(-1),[4,8,11,12,16],[1],5⟩,⟨1,(-1),[4,8,12,16],[9,13],5⟩,⟨1,(-1),[4,8,12,16],[2],6⟩,⟨1,(-1),[4,8,12,16],[7,11,15],8⟩,⟨1,(-1),[4,8,12,16],[6],9⟩,⟨1,(-1),[4,8,12,16],[14],55⟩,⟨1,(-1),[8,12],[3],8⟩,⟨9,(0),[4,8,12,16],[10],6⟩,⟨9,(1),[4,8,12,16],[10],27⟩,⟨9,(2),[4,8,12,16],[10],28⟩,⟨9,(3),[4,8,12,16],[10],29⟩,⟨9,(4),[4,8,12,16],[10],30⟩,⟨9,(5),[4,8,12,16],[10],6⟩,⟨9,(6),[4,8,12,16],[10],27⟩,⟨9,(7),[4,8,12,16],[10],31⟩,⟨9,(8),[4,8,12,16],[10],29⟩,⟨9,(9),[4,8,12,16],[10],32⟩,⟨9,(10),[4,8,12,16],[10],6⟩,⟨9,(11),[4,8,12,16],[10],27⟩,⟨9,(12),[4,8,12,16],[10],33⟩,⟨9,(13),[4,8,12,16],[10],29⟩,⟨9,(14),[4,8,12,16],[10],34⟩,⟨9,(15),[4,8,12,16],[10],35⟩,⟨9,(16),[4,8,12,16],[10],36⟩,⟨9,(17),[4,8,12,16],[10],37⟩,⟨9,(18),[4,8,12,16],[10],29⟩,⟨9,(19),[4,8,12,16],[10],37⟩,⟨9,(20),[4,8,12,16],[10],38⟩,⟨9,(21),[4,8,12,16],[10],39⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid0
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2
  · exact recordValid_of_data section14Catalog 12 _ hnum valid3
  · exact recordValid_of_data section14Catalog 12 _ hnum valid4
  · exact recordValid_of_data section14Catalog 12 _ hnum valid5
  · exact recordValid_of_data section14Catalog 12 _ hnum valid6
  · exact recordValid_of_data section14Catalog 12 _ hnum valid7
  · exact recordValid_of_data section14Catalog 12 _ hnum valid8
  · exact recordValid_of_data section14Catalog 12 _ hnum valid9
  · exact recordValid_of_data section14Catalog 12 _ hnum valid10
  · exact recordValid_of_data section14Catalog 12 _ hnum valid11
  · exact recordValid_of_data section14Catalog 12 _ hnum valid12
  · exact recordValid_of_data section14Catalog 12 _ hnum valid13
  · exact recordValid_of_data section14Catalog 12 _ hnum valid14
  · exact recordValid_of_data section14Catalog 12 _ hnum valid15
  · exact recordValid_of_data section14Catalog 12 _ hnum valid16
  · exact recordValid_of_data section14Catalog 12 _ hnum valid17
  · exact recordValid_of_data section14Catalog 12 _ hnum valid18
  · exact recordValid_of_data section14Catalog 12 _ hnum valid19
  · exact recordValid_of_data section14Catalog 12 _ hnum valid20
  · exact recordValid_of_data section14Catalog 12 _ hnum valid21
  · exact recordValid_of_data section14Catalog 12 _ hnum valid22
  · exact recordValid_of_data section14Catalog 12 _ hnum valid23
  · exact recordValid_of_data section14Catalog 12 _ hnum valid24
  · exact recordValid_of_data section14Catalog 12 _ hnum valid25
  · exact recordValid_of_data section14Catalog 12 _ hnum valid26
  · exact recordValid_of_data section14Catalog 12 _ hnum valid27
  · exact recordValid_of_data section14Catalog 12 _ hnum valid28
  · exact recordValid_of_data section14Catalog 12 _ hnum valid29
  · exact recordValid_of_data section14Catalog 12 _ hnum valid30
  · exact recordValid_of_data section14Catalog 12 _ hnum valid31
end Section14Records_12_0_32

#print axioms solution
