-- Prove2me | solution 1 for Freiman.section14_s0010_records_0032_0064
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:30:03.086986+00:00
-- url     : https://prove2.me/submissions/72253084-0964-41f3-906d-194b2dbee670

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
namespace Section14Records_10_32_64
private theorem valid32 : RecordDataValid section14Catalog 10 (⟨3,(15),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid33 : RecordDataValid section14Catalog 10 (⟨3,(16),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid34 : RecordDataValid section14Catalog 10 (⟨3,(17),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid35 : RecordDataValid section14Catalog 10 (⟨3,(18),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid36 : RecordDataValid section14Catalog 10 (⟨3,(19),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid37 : RecordDataValid section14Catalog 10 (⟨3,(20),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid38 : RecordDataValid section14Catalog 10 (⟨3,(21),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid39 : RecordDataValid section14Catalog 10 (⟨3,(22),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid40 : RecordDataValid section14Catalog 10 (⟨3,(23),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid41 : RecordDataValid section14Catalog 10 (⟨3,(24),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid42 : RecordDataValid section14Catalog 10 (⟨9,(0),[9,10],[42],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid43 : RecordDataValid section14Catalog 10 (⟨9,(1),[9,10],[42],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid44 : RecordDataValid section14Catalog 10 (⟨9,(2),[9,10],[42],28⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨28,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],28⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid45 : RecordDataValid section14Catalog 10 (⟨9,(3),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid46 : RecordDataValid section14Catalog 10 (⟨9,(4),[9,10],[42],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid47 : RecordDataValid section14Catalog 10 (⟨9,(5),[9,10],[42],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid48 : RecordDataValid section14Catalog 10 (⟨9,(6),[9,10],[42],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid49 : RecordDataValid section14Catalog 10 (⟨9,(7),[9,10],[42],31⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨31,[1,2,4,5,6,8,9,10,12,13,14,16],31⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid50 : RecordDataValid section14Catalog 10 (⟨9,(8),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid51 : RecordDataValid section14Catalog 10 (⟨9,(9),[9,10],[42],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid52 : RecordDataValid section14Catalog 10 (⟨9,(10),[9,10],[42],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid53 : RecordDataValid section14Catalog 10 (⟨9,(11),[9,10],[42],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid54 : RecordDataValid section14Catalog 10 (⟨9,(12),[9,10],[42],33⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨33,[1,2,4,5,6,8,9,10,12,13,14,16],33⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid55 : RecordDataValid section14Catalog 10 (⟨9,(13),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid56 : RecordDataValid section14Catalog 10 (⟨9,(14),[9,10],[42],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid57 : RecordDataValid section14Catalog 10 (⟨9,(15),[9,10],[42],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid58 : RecordDataValid section14Catalog 10 (⟨9,(16),[9,10],[42],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid59 : RecordDataValid section14Catalog 10 (⟨9,(17),[9,10],[42],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid60 : RecordDataValid section14Catalog 10 (⟨9,(18),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid61 : RecordDataValid section14Catalog 10 (⟨9,(19),[9,10],[42],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid62 : RecordDataValid section14Catalog 10 (⟨9,(20),[9,10],[42],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid63 : RecordDataValid section14Catalog 10 (⟨9,(21),[9,10],[42],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 32).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 32).take 32 = [⟨3,(15),[9,10],[42],3⟩,⟨3,(16),[9,10],[42],3⟩,⟨3,(17),[9,10],[42],3⟩,⟨3,(18),[9,10],[42],3⟩,⟨3,(19),[9,10],[42],3⟩,⟨3,(20),[9,10],[42],3⟩,⟨3,(21),[9,10],[42],3⟩,⟨3,(22),[9,10],[42],3⟩,⟨3,(23),[9,10],[42],3⟩,⟨3,(24),[9,10],[42],3⟩,⟨9,(0),[9,10],[42],6⟩,⟨9,(1),[9,10],[42],27⟩,⟨9,(2),[9,10],[42],28⟩,⟨9,(3),[9,10],[42],29⟩,⟨9,(4),[9,10],[42],30⟩,⟨9,(5),[9,10],[42],6⟩,⟨9,(6),[9,10],[42],27⟩,⟨9,(7),[9,10],[42],31⟩,⟨9,(8),[9,10],[42],29⟩,⟨9,(9),[9,10],[42],32⟩,⟨9,(10),[9,10],[42],6⟩,⟨9,(11),[9,10],[42],27⟩,⟨9,(12),[9,10],[42],33⟩,⟨9,(13),[9,10],[42],29⟩,⟨9,(14),[9,10],[42],34⟩,⟨9,(15),[9,10],[42],35⟩,⟨9,(16),[9,10],[42],36⟩,⟨9,(17),[9,10],[42],37⟩,⟨9,(18),[9,10],[42],29⟩,⟨9,(19),[9,10],[42],37⟩,⟨9,(20),[9,10],[42],38⟩,⟨9,(21),[9,10],[42],39⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid32
  · exact recordValid_of_data section14Catalog 10 _ hnum valid33
  · exact recordValid_of_data section14Catalog 10 _ hnum valid34
  · exact recordValid_of_data section14Catalog 10 _ hnum valid35
  · exact recordValid_of_data section14Catalog 10 _ hnum valid36
  · exact recordValid_of_data section14Catalog 10 _ hnum valid37
  · exact recordValid_of_data section14Catalog 10 _ hnum valid38
  · exact recordValid_of_data section14Catalog 10 _ hnum valid39
  · exact recordValid_of_data section14Catalog 10 _ hnum valid40
  · exact recordValid_of_data section14Catalog 10 _ hnum valid41
  · exact recordValid_of_data section14Catalog 10 _ hnum valid42
  · exact recordValid_of_data section14Catalog 10 _ hnum valid43
  · exact recordValid_of_data section14Catalog 10 _ hnum valid44
  · exact recordValid_of_data section14Catalog 10 _ hnum valid45
  · exact recordValid_of_data section14Catalog 10 _ hnum valid46
  · exact recordValid_of_data section14Catalog 10 _ hnum valid47
  · exact recordValid_of_data section14Catalog 10 _ hnum valid48
  · exact recordValid_of_data section14Catalog 10 _ hnum valid49
  · exact recordValid_of_data section14Catalog 10 _ hnum valid50
  · exact recordValid_of_data section14Catalog 10 _ hnum valid51
  · exact recordValid_of_data section14Catalog 10 _ hnum valid52
  · exact recordValid_of_data section14Catalog 10 _ hnum valid53
  · exact recordValid_of_data section14Catalog 10 _ hnum valid54
  · exact recordValid_of_data section14Catalog 10 _ hnum valid55
  · exact recordValid_of_data section14Catalog 10 _ hnum valid56
  · exact recordValid_of_data section14Catalog 10 _ hnum valid57
  · exact recordValid_of_data section14Catalog 10 _ hnum valid58
  · exact recordValid_of_data section14Catalog 10 _ hnum valid59
  · exact recordValid_of_data section14Catalog 10 _ hnum valid60
  · exact recordValid_of_data section14Catalog 10 _ hnum valid61
  · exact recordValid_of_data section14Catalog 10 _ hnum valid62
  · exact recordValid_of_data section14Catalog 10 _ hnum valid63
end Section14Records_10_32_64

#print axioms solution
