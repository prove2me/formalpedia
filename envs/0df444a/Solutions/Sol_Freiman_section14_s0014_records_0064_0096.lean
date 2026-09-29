-- Prove2me | solution 1 for Freiman.section14_s0014_records_0064_0096
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:19:02.089048+00:00
-- url     : https://prove2.me/submissions/8a3bc3ba-4abe-4f03-8863-c085b0d8ecf1

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
namespace Section14Records_14_64_96
private theorem valid64 : RecordDataValid section14Catalog 14 (⟨5,(17),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid65 : RecordDataValid section14Catalog 14 (⟨5,(18),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid66 : RecordDataValid section14Catalog 14 (⟨5,(19),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid67 : RecordDataValid section14Catalog 14 (⟨5,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid68 : RecordDataValid section14Catalog 14 (⟨5,(21),[1,2,5,6,13,14],[170],25⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨25,[1,2,3,4,5,6,7,8,13,14,15,16],25⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid69 : RecordDataValid section14Catalog 14 (⟨5,(22),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid70 : RecordDataValid section14Catalog 14 (⟨5,(23),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid71 : RecordDataValid section14Catalog 14 (⟨5,(24),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid72 : RecordDataValid section14Catalog 14 (⟨9,(0),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid73 : RecordDataValid section14Catalog 14 (⟨9,(1),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid74 : RecordDataValid section14Catalog 14 (⟨9,(2),[1,2,5,6,13,14],[170],28⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨28,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],28⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid75 : RecordDataValid section14Catalog 14 (⟨9,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid76 : RecordDataValid section14Catalog 14 (⟨9,(4),[1,2,5,6,13,14],[170],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid77 : RecordDataValid section14Catalog 14 (⟨9,(5),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid78 : RecordDataValid section14Catalog 14 (⟨9,(6),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid79 : RecordDataValid section14Catalog 14 (⟨9,(7),[1,2,5,6,13,14],[170],31⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨31,[1,2,4,5,6,8,9,10,12,13,14,16],31⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid80 : RecordDataValid section14Catalog 14 (⟨9,(8),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid81 : RecordDataValid section14Catalog 14 (⟨9,(9),[1,2,5,6,13,14],[170],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid82 : RecordDataValid section14Catalog 14 (⟨9,(10),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid83 : RecordDataValid section14Catalog 14 (⟨9,(11),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid84 : RecordDataValid section14Catalog 14 (⟨9,(12),[1,2,5,6,13,14],[170],33⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨33,[1,2,4,5,6,8,9,10,12,13,14,16],33⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid85 : RecordDataValid section14Catalog 14 (⟨9,(13),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid86 : RecordDataValid section14Catalog 14 (⟨9,(14),[1,2,5,6,13,14],[170],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid87 : RecordDataValid section14Catalog 14 (⟨9,(15),[1,2,5,6,13,14],[170],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid88 : RecordDataValid section14Catalog 14 (⟨9,(16),[1,2,5,6,13,14],[170],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid89 : RecordDataValid section14Catalog 14 (⟨9,(17),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid90 : RecordDataValid section14Catalog 14 (⟨9,(18),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid91 : RecordDataValid section14Catalog 14 (⟨9,(19),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid92 : RecordDataValid section14Catalog 14 (⟨9,(20),[1,2,5,6,13,14],[170],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid93 : RecordDataValid section14Catalog 14 (⟨9,(21),[1,2,5,6,13,14],[170],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid94 : RecordDataValid section14Catalog 14 (⟨9,(22),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid95 : RecordDataValid section14Catalog 14 (⟨9,(23),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 14 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 64).take 32 = [⟨5,(17),[1,2,5,6,13,14],[170],23⟩,⟨5,(18),[1,2,5,6,13,14],[170],23⟩,⟨5,(19),[1,2,5,6,13,14],[170],23⟩,⟨5,(20),[1,2,5,6,13,14],[170],24⟩,⟨5,(21),[1,2,5,6,13,14],[170],25⟩,⟨5,(22),[1,2,5,6,13,14],[170],26⟩,⟨5,(23),[1,2,5,6,13,14],[170],26⟩,⟨5,(24),[1,2,5,6,13,14],[170],26⟩,⟨9,(0),[1,2,5,6,13,14],[170],6⟩,⟨9,(1),[1,2,5,6,13,14],[170],27⟩,⟨9,(2),[1,2,5,6,13,14],[170],28⟩,⟨9,(3),[1,2,5,6,13,14],[170],29⟩,⟨9,(4),[1,2,5,6,13,14],[170],30⟩,⟨9,(5),[1,2,5,6,13,14],[170],6⟩,⟨9,(6),[1,2,5,6,13,14],[170],27⟩,⟨9,(7),[1,2,5,6,13,14],[170],31⟩,⟨9,(8),[1,2,5,6,13,14],[170],29⟩,⟨9,(9),[1,2,5,6,13,14],[170],32⟩,⟨9,(10),[1,2,5,6,13,14],[170],6⟩,⟨9,(11),[1,2,5,6,13,14],[170],27⟩,⟨9,(12),[1,2,5,6,13,14],[170],33⟩,⟨9,(13),[1,2,5,6,13,14],[170],29⟩,⟨9,(14),[1,2,5,6,13,14],[170],34⟩,⟨9,(15),[1,2,5,6,13,14],[170],35⟩,⟨9,(16),[1,2,5,6,13,14],[170],36⟩,⟨9,(17),[1,2,5,6,13,14],[170],37⟩,⟨9,(18),[1,2,5,6,13,14],[170],29⟩,⟨9,(19),[1,2,5,6,13,14],[170],37⟩,⟨9,(20),[1,2,5,6,13,14],[170],38⟩,⟨9,(21),[1,2,5,6,13,14],[170],39⟩,⟨9,(22),[1,2,5,6,13,14],[170],40⟩,⟨9,(23),[1,2,5,6,13,14],[170],29⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 14 _ hnum valid64
  · exact recordValid_of_data section14Catalog 14 _ hnum valid65
  · exact recordValid_of_data section14Catalog 14 _ hnum valid66
  · exact recordValid_of_data section14Catalog 14 _ hnum valid67
  · exact recordValid_of_data section14Catalog 14 _ hnum valid68
  · exact recordValid_of_data section14Catalog 14 _ hnum valid69
  · exact recordValid_of_data section14Catalog 14 _ hnum valid70
  · exact recordValid_of_data section14Catalog 14 _ hnum valid71
  · exact recordValid_of_data section14Catalog 14 _ hnum valid72
  · exact recordValid_of_data section14Catalog 14 _ hnum valid73
  · exact recordValid_of_data section14Catalog 14 _ hnum valid74
  · exact recordValid_of_data section14Catalog 14 _ hnum valid75
  · exact recordValid_of_data section14Catalog 14 _ hnum valid76
  · exact recordValid_of_data section14Catalog 14 _ hnum valid77
  · exact recordValid_of_data section14Catalog 14 _ hnum valid78
  · exact recordValid_of_data section14Catalog 14 _ hnum valid79
  · exact recordValid_of_data section14Catalog 14 _ hnum valid80
  · exact recordValid_of_data section14Catalog 14 _ hnum valid81
  · exact recordValid_of_data section14Catalog 14 _ hnum valid82
  · exact recordValid_of_data section14Catalog 14 _ hnum valid83
  · exact recordValid_of_data section14Catalog 14 _ hnum valid84
  · exact recordValid_of_data section14Catalog 14 _ hnum valid85
  · exact recordValid_of_data section14Catalog 14 _ hnum valid86
  · exact recordValid_of_data section14Catalog 14 _ hnum valid87
  · exact recordValid_of_data section14Catalog 14 _ hnum valid88
  · exact recordValid_of_data section14Catalog 14 _ hnum valid89
  · exact recordValid_of_data section14Catalog 14 _ hnum valid90
  · exact recordValid_of_data section14Catalog 14 _ hnum valid91
  · exact recordValid_of_data section14Catalog 14 _ hnum valid92
  · exact recordValid_of_data section14Catalog 14 _ hnum valid93
  · exact recordValid_of_data section14Catalog 14 _ hnum valid94
  · exact recordValid_of_data section14Catalog 14 _ hnum valid95
end Section14Records_14_64_96

#print axioms solution
