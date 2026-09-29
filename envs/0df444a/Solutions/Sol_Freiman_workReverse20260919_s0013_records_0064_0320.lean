-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_0064_0320
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:49:32.832649+00:00
-- url     : https://prove2.me/submissions/fcd4d76c-9b37-412e-9de7-a3558fd177f4

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0064_0096
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_64_96
private theorem valid64 : RecordDataValid section14Catalog 13 (⟨5,(16),[1,2,5,6,13,14],[170],22⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨22,[1,2,3,4,5,6,7,8,13,14,15,16],22⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid65 : RecordDataValid section14Catalog 13 (⟨5,(17),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid66 : RecordDataValid section14Catalog 13 (⟨5,(18),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid67 : RecordDataValid section14Catalog 13 (⟨5,(19),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid68 : RecordDataValid section14Catalog 13 (⟨5,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid69 : RecordDataValid section14Catalog 13 (⟨5,(21),[1,2,5,6,13,14],[170],25⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨25,[1,2,3,4,5,6,7,8,13,14,15,16],25⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid70 : RecordDataValid section14Catalog 13 (⟨5,(22),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid71 : RecordDataValid section14Catalog 13 (⟨5,(23),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid72 : RecordDataValid section14Catalog 13 (⟨5,(24),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid73 : RecordDataValid section14Catalog 13 (⟨9,(0),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid74 : RecordDataValid section14Catalog 13 (⟨9,(1),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid75 : RecordDataValid section14Catalog 13 (⟨9,(2),[1,2,5,6,13,14],[170],28⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨28,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],28⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid76 : RecordDataValid section14Catalog 13 (⟨9,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid77 : RecordDataValid section14Catalog 13 (⟨9,(4),[1,2,5,6,13,14],[170],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid78 : RecordDataValid section14Catalog 13 (⟨9,(5),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid79 : RecordDataValid section14Catalog 13 (⟨9,(6),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid80 : RecordDataValid section14Catalog 13 (⟨9,(7),[1,2,5,6,13,14],[170],31⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨31,[1,2,4,5,6,8,9,10,12,13,14,16],31⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid81 : RecordDataValid section14Catalog 13 (⟨9,(8),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid82 : RecordDataValid section14Catalog 13 (⟨9,(9),[1,2,5,6,13,14],[170],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid83 : RecordDataValid section14Catalog 13 (⟨9,(10),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid84 : RecordDataValid section14Catalog 13 (⟨9,(11),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid85 : RecordDataValid section14Catalog 13 (⟨9,(12),[1,2,5,6,13,14],[170],33⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨33,[1,2,4,5,6,8,9,10,12,13,14,16],33⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid86 : RecordDataValid section14Catalog 13 (⟨9,(13),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid87 : RecordDataValid section14Catalog 13 (⟨9,(14),[1,2,5,6,13,14],[170],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid88 : RecordDataValid section14Catalog 13 (⟨9,(15),[1,2,5,6,13,14],[170],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid89 : RecordDataValid section14Catalog 13 (⟨9,(16),[1,2,5,6,13,14],[170],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid90 : RecordDataValid section14Catalog 13 (⟨9,(17),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid91 : RecordDataValid section14Catalog 13 (⟨9,(18),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid92 : RecordDataValid section14Catalog 13 (⟨9,(19),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid93 : RecordDataValid section14Catalog 13 (⟨9,(20),[1,2,5,6,13,14],[170],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid94 : RecordDataValid section14Catalog 13 (⟨9,(21),[1,2,5,6,13,14],[170],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid95 : RecordDataValid section14Catalog 13 (⟨9,(22),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0064_0096 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 64).take 32 = [⟨5,(16),[1,2,5,6,13,14],[170],22⟩,⟨5,(17),[1,2,5,6,13,14],[170],23⟩,⟨5,(18),[1,2,5,6,13,14],[170],23⟩,⟨5,(19),[1,2,5,6,13,14],[170],23⟩,⟨5,(20),[1,2,5,6,13,14],[170],24⟩,⟨5,(21),[1,2,5,6,13,14],[170],25⟩,⟨5,(22),[1,2,5,6,13,14],[170],26⟩,⟨5,(23),[1,2,5,6,13,14],[170],26⟩,⟨5,(24),[1,2,5,6,13,14],[170],26⟩,⟨9,(0),[1,2,5,6,13,14],[170],6⟩,⟨9,(1),[1,2,5,6,13,14],[170],27⟩,⟨9,(2),[1,2,5,6,13,14],[170],28⟩,⟨9,(3),[1,2,5,6,13,14],[170],29⟩,⟨9,(4),[1,2,5,6,13,14],[170],30⟩,⟨9,(5),[1,2,5,6,13,14],[170],6⟩,⟨9,(6),[1,2,5,6,13,14],[170],27⟩,⟨9,(7),[1,2,5,6,13,14],[170],31⟩,⟨9,(8),[1,2,5,6,13,14],[170],29⟩,⟨9,(9),[1,2,5,6,13,14],[170],32⟩,⟨9,(10),[1,2,5,6,13,14],[170],6⟩,⟨9,(11),[1,2,5,6,13,14],[170],27⟩,⟨9,(12),[1,2,5,6,13,14],[170],33⟩,⟨9,(13),[1,2,5,6,13,14],[170],29⟩,⟨9,(14),[1,2,5,6,13,14],[170],34⟩,⟨9,(15),[1,2,5,6,13,14],[170],35⟩,⟨9,(16),[1,2,5,6,13,14],[170],36⟩,⟨9,(17),[1,2,5,6,13,14],[170],37⟩,⟨9,(18),[1,2,5,6,13,14],[170],29⟩,⟨9,(19),[1,2,5,6,13,14],[170],37⟩,⟨9,(20),[1,2,5,6,13,14],[170],38⟩,⟨9,(21),[1,2,5,6,13,14],[170],39⟩,⟨9,(22),[1,2,5,6,13,14],[170],40⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid64
  · exact recordValid_of_data section14Catalog 13 _ hnum valid65
  · exact recordValid_of_data section14Catalog 13 _ hnum valid66
  · exact recordValid_of_data section14Catalog 13 _ hnum valid67
  · exact recordValid_of_data section14Catalog 13 _ hnum valid68
  · exact recordValid_of_data section14Catalog 13 _ hnum valid69
  · exact recordValid_of_data section14Catalog 13 _ hnum valid70
  · exact recordValid_of_data section14Catalog 13 _ hnum valid71
  · exact recordValid_of_data section14Catalog 13 _ hnum valid72
  · exact recordValid_of_data section14Catalog 13 _ hnum valid73
  · exact recordValid_of_data section14Catalog 13 _ hnum valid74
  · exact recordValid_of_data section14Catalog 13 _ hnum valid75
  · exact recordValid_of_data section14Catalog 13 _ hnum valid76
  · exact recordValid_of_data section14Catalog 13 _ hnum valid77
  · exact recordValid_of_data section14Catalog 13 _ hnum valid78
  · exact recordValid_of_data section14Catalog 13 _ hnum valid79
  · exact recordValid_of_data section14Catalog 13 _ hnum valid80
  · exact recordValid_of_data section14Catalog 13 _ hnum valid81
  · exact recordValid_of_data section14Catalog 13 _ hnum valid82
  · exact recordValid_of_data section14Catalog 13 _ hnum valid83
  · exact recordValid_of_data section14Catalog 13 _ hnum valid84
  · exact recordValid_of_data section14Catalog 13 _ hnum valid85
  · exact recordValid_of_data section14Catalog 13 _ hnum valid86
  · exact recordValid_of_data section14Catalog 13 _ hnum valid87
  · exact recordValid_of_data section14Catalog 13 _ hnum valid88
  · exact recordValid_of_data section14Catalog 13 _ hnum valid89
  · exact recordValid_of_data section14Catalog 13 _ hnum valid90
  · exact recordValid_of_data section14Catalog 13 _ hnum valid91
  · exact recordValid_of_data section14Catalog 13 _ hnum valid92
  · exact recordValid_of_data section14Catalog 13 _ hnum valid93
  · exact recordValid_of_data section14Catalog 13 _ hnum valid94
  · exact recordValid_of_data section14Catalog 13 _ hnum valid95
end Section14Records_13_64_96

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0064_0096


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0096_0128
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_96_128
private theorem valid96 : RecordDataValid section14Catalog 13 (⟨9,(23),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid97 : RecordDataValid section14Catalog 13 (⟨9,(24),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid98 : RecordDataValid section14Catalog 13 (⟨14,(5),[13],[170],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid99 : RecordDataValid section14Catalog 13 (⟨14,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid100 : RecordDataValid section14Catalog 13 (⟨14,(8),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid101 : RecordDataValid section14Catalog 13 (⟨14,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid102 : RecordDataValid section14Catalog 13 (⟨14,(15),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid103 : RecordDataValid section14Catalog 13 (⟨14,(16),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid104 : RecordDataValid section14Catalog 13 (⟨14,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid105 : RecordDataValid section14Catalog 13 (⟨14,(19),[1,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid106 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid107 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,9,10,13,14],[1],57⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨57,[1,2,5,6,9,10,13,14],57⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid108 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid109 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid110 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨58,[1,2,3,5,6,7,13,14,15],58⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid111 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid112 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[45],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid113 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[61],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid114 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[64],63⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨63,[1,2,4,5,6,8,9,10,12,13,14,16],63⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid115 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[65],64⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨64,[1,2,4,5,6,8,9,10,12,13,14,16],64⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid116 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[80,84],65⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨65,[1,2,4,5,6,8,9,10,12,13,14,16],65⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid117 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[81,85],66⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨66,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],66⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid118 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨67,[1,2,5,6,13,14],67⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid119 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid120 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[108],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid121 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[109],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid122 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[124],71⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨71,[1,2,4,5,6,8,9,10,12,13,14,16],71⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid123 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[125],72⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨72,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],72⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid124 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[174],205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨205,[1,2,4,5,6,8,9,10,12,13,14,16],205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid125 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨206,[1,2,5,6,13,14],206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid126 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[175],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid127 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[186],208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨208,[1,2,3,5,6,7,13,14,15],208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0096_0128 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 96).take 32 = [⟨9,(23),[1,2,5,6,13,14],[170],29⟩,⟨9,(24),[1,2,5,6,13,14],[170],40⟩,⟨14,(5),[13],[170],105⟩,⟨14,(7),[1,2,5,6,13,14],[170],3⟩,⟨14,(8),[5,13],[170],48⟩,⟨14,(9),[5,6,13,14],[170],143⟩,⟨14,(15),[5,13],[170],48⟩,⟨14,(16),[5,13],[170],48⟩,⟨14,(17),[1,2,5,6,13,14],[170],48⟩,⟨14,(19),[1,13],[170],48⟩,⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨16,(-1),[1,2,5,6,9,10,13,14],[1],57⟩,⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩,⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩,⟨16,(-1),[1,2,5,6,13,14],[45],61⟩,⟨16,(-1),[1,2,5,6,13,14],[61],62⟩,⟨16,(-1),[1,2,5,6,13,14],[64],63⟩,⟨16,(-1),[1,2,5,6,13,14],[65],64⟩,⟨16,(-1),[1,2,5,6,13,14],[80,84],65⟩,⟨16,(-1),[1,2,5,6,13,14],[81,85],66⟩,⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩,⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩,⟨16,(-1),[1,2,5,6,13,14],[108],69⟩,⟨16,(-1),[1,2,5,6,13,14],[109],70⟩,⟨16,(-1),[1,2,5,6,13,14],[124],71⟩,⟨16,(-1),[1,2,5,6,13,14],[125],72⟩,⟨16,(-1),[1,2,5,6,13,14],[174],205⟩,⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩,⟨16,(-1),[1,2,5,6,13,14],[175],207⟩,⟨16,(-1),[1,2,5,6,13,14],[186],208⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid96
  · exact recordValid_of_data section14Catalog 13 _ hnum valid97
  · exact recordValid_of_data section14Catalog 13 _ hnum valid98
  · exact recordValid_of_data section14Catalog 13 _ hnum valid99
  · exact recordValid_of_data section14Catalog 13 _ hnum valid100
  · exact recordValid_of_data section14Catalog 13 _ hnum valid101
  · exact recordValid_of_data section14Catalog 13 _ hnum valid102
  · exact recordValid_of_data section14Catalog 13 _ hnum valid103
  · exact recordValid_of_data section14Catalog 13 _ hnum valid104
  · exact recordValid_of_data section14Catalog 13 _ hnum valid105
  · exact recordValid_of_data section14Catalog 13 _ hnum valid106
  · exact recordValid_of_data section14Catalog 13 _ hnum valid107
  · exact recordValid_of_data section14Catalog 13 _ hnum valid108
  · exact recordValid_of_data section14Catalog 13 _ hnum valid109
  · exact recordValid_of_data section14Catalog 13 _ hnum valid110
  · exact recordValid_of_data section14Catalog 13 _ hnum valid111
  · exact recordValid_of_data section14Catalog 13 _ hnum valid112
  · exact recordValid_of_data section14Catalog 13 _ hnum valid113
  · exact recordValid_of_data section14Catalog 13 _ hnum valid114
  · exact recordValid_of_data section14Catalog 13 _ hnum valid115
  · exact recordValid_of_data section14Catalog 13 _ hnum valid116
  · exact recordValid_of_data section14Catalog 13 _ hnum valid117
  · exact recordValid_of_data section14Catalog 13 _ hnum valid118
  · exact recordValid_of_data section14Catalog 13 _ hnum valid119
  · exact recordValid_of_data section14Catalog 13 _ hnum valid120
  · exact recordValid_of_data section14Catalog 13 _ hnum valid121
  · exact recordValid_of_data section14Catalog 13 _ hnum valid122
  · exact recordValid_of_data section14Catalog 13 _ hnum valid123
  · exact recordValid_of_data section14Catalog 13 _ hnum valid124
  · exact recordValid_of_data section14Catalog 13 _ hnum valid125
  · exact recordValid_of_data section14Catalog 13 _ hnum valid126
  · exact recordValid_of_data section14Catalog 13 _ hnum valid127
end Section14Records_13_96_128

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0096_0128


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0128_0160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_128_160
private theorem valid128 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[191],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid129 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨240,[1,2,5,6,9,10,13,14],240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid130 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨241,[1,2,3,5,6,7,13,14,15],241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid131 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[210],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid132 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid133 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[238],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid134 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,6,13,14],[254],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid135 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,13,14],[4,20],58⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨58,[1,2,3,5,6,7,13,14,15],58⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid136 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,13,14],[211],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid137 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,5,13,14],[235,251],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid138 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,13,14],[68],63⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨63,[1,2,4,5,6,8,9,10,12,13,14,16],63⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid139 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,13,14],[69],64⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨64,[1,2,4,5,6,8,9,10,12,13,14,16],64⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid140 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,2,13,14],[214,215],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid141 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,5,9,13],[0],57⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨57,[1,2,5,6,9,10,13,14],57⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid142 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,5,13],[16,17],59⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨59,[1,5,9,10,13],59⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid143 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,5,13],[40,56],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid144 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,5,13],[44],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid145 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,5,13],[60],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid146 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,5,13],[239],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid147 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,5,13],[255],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid148 : RecordDataValid section14Catalog 13 (⟨16,(-1),[1,13],[170],205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨205,[1,2,4,5,6,8,9,10,12,13,14,16],205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid149 : RecordDataValid section14Catalog 13 (⟨16,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid150 : RecordDataValid section14Catalog 13 (⟨16,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid151 : RecordDataValid section14Catalog 13 (⟨16,(-1),[13],[134],1727⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1727,[13,14],1732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid152 : RecordDataValid section14Catalog 13 (⟨16,(-1),[13,14],[130],1727⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1727,[13,14],1732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid153 : RecordDataValid section14Catalog 13 (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid154 : RecordDataValid section14Catalog 13 (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid155 : RecordDataValid section14Catalog 13 (⟨18,(0),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid156 : RecordDataValid section14Catalog 13 (⟨18,(0),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid157 : RecordDataValid section14Catalog 13 (⟨18,(0),[1,13],[146],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid158 : RecordDataValid section14Catalog 13 (⟨18,(0),[1,13],[151],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid159 : RecordDataValid section14Catalog 13 (⟨18,(0),[1,13],[147],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0128_0160 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 128).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 128).take 32 = [⟨16,(-1),[1,2,5,6,13,14],[191],239⟩,⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩,⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩,⟨16,(-1),[1,2,5,6,13,14],[210],242⟩,⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩,⟨16,(-1),[1,2,5,6,13,14],[238],244⟩,⟨16,(-1),[1,2,5,6,13,14],[254],245⟩,⟨16,(-1),[1,2,5,13,14],[4,20],58⟩,⟨16,(-1),[1,2,5,13,14],[211],242⟩,⟨16,(-1),[1,2,5,13,14],[235,251],243⟩,⟨16,(-1),[1,2,13,14],[68],63⟩,⟨16,(-1),[1,2,13,14],[69],64⟩,⟨16,(-1),[1,2,13,14],[214,215],242⟩,⟨16,(-1),[1,5,9,13],[0],57⟩,⟨16,(-1),[1,5,13],[16,17],59⟩,⟨16,(-1),[1,5,13],[40,56],60⟩,⟨16,(-1),[1,5,13],[44],61⟩,⟨16,(-1),[1,5,13],[60],62⟩,⟨16,(-1),[1,5,13],[239],244⟩,⟨16,(-1),[1,5,13],[255],245⟩,⟨16,(-1),[1,13],[170],205⟩,⟨16,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨16,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩,⟨16,(-1),[13],[134],1727⟩,⟨16,(-1),[13,14],[130],1727⟩,⟨18,(0),[1,2,5,6,13,14],[131],106⟩,⟨18,(0),[1,2,5,6,13,14],[150],125⟩,⟨18,(0),[1,2,13,14],[190],3⟩,⟨18,(0),[1,5,13],[135],125⟩,⟨18,(0),[1,13],[146],73⟩,⟨18,(0),[1,13],[151],125⟩,⟨18,(0),[1,13],[147],160⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid128
  · exact recordValid_of_data section14Catalog 13 _ hnum valid129
  · exact recordValid_of_data section14Catalog 13 _ hnum valid130
  · exact recordValid_of_data section14Catalog 13 _ hnum valid131
  · exact recordValid_of_data section14Catalog 13 _ hnum valid132
  · exact recordValid_of_data section14Catalog 13 _ hnum valid133
  · exact recordValid_of_data section14Catalog 13 _ hnum valid134
  · exact recordValid_of_data section14Catalog 13 _ hnum valid135
  · exact recordValid_of_data section14Catalog 13 _ hnum valid136
  · exact recordValid_of_data section14Catalog 13 _ hnum valid137
  · exact recordValid_of_data section14Catalog 13 _ hnum valid138
  · exact recordValid_of_data section14Catalog 13 _ hnum valid139
  · exact recordValid_of_data section14Catalog 13 _ hnum valid140
  · exact recordValid_of_data section14Catalog 13 _ hnum valid141
  · exact recordValid_of_data section14Catalog 13 _ hnum valid142
  · exact recordValid_of_data section14Catalog 13 _ hnum valid143
  · exact recordValid_of_data section14Catalog 13 _ hnum valid144
  · exact recordValid_of_data section14Catalog 13 _ hnum valid145
  · exact recordValid_of_data section14Catalog 13 _ hnum valid146
  · exact recordValid_of_data section14Catalog 13 _ hnum valid147
  · exact recordValid_of_data section14Catalog 13 _ hnum valid148
  · exact recordValid_of_data section14Catalog 13 _ hnum valid149
  · exact recordValid_of_data section14Catalog 13 _ hnum valid150
  · exact recordValid_of_data section14Catalog 13 _ hnum valid151
  · exact recordValid_of_data section14Catalog 13 _ hnum valid152
  · exact recordValid_of_data section14Catalog 13 _ hnum valid153
  · exact recordValid_of_data section14Catalog 13 _ hnum valid154
  · exact recordValid_of_data section14Catalog 13 _ hnum valid155
  · exact recordValid_of_data section14Catalog 13 _ hnum valid156
  · exact recordValid_of_data section14Catalog 13 _ hnum valid157
  · exact recordValid_of_data section14Catalog 13 _ hnum valid158
  · exact recordValid_of_data section14Catalog 13 _ hnum valid159
end Section14Records_13_128_160

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0128_0160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0160_0192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_160_192
private theorem valid160 : RecordDataValid section14Catalog 13 (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid161 : RecordDataValid section14Catalog 13 (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid162 : RecordDataValid section14Catalog 13 (⟨18,(1),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid163 : RecordDataValid section14Catalog 13 (⟨18,(1),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid164 : RecordDataValid section14Catalog 13 (⟨18,(1),[1,13],[146],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid165 : RecordDataValid section14Catalog 13 (⟨18,(1),[1,13],[151],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid166 : RecordDataValid section14Catalog 13 (⟨18,(1),[1,13],[147],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid167 : RecordDataValid section14Catalog 13 (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid168 : RecordDataValid section14Catalog 13 (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid169 : RecordDataValid section14Catalog 13 (⟨18,(2),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid170 : RecordDataValid section14Catalog 13 (⟨18,(2),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid171 : RecordDataValid section14Catalog 13 (⟨18,(2),[1,13],[146],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid172 : RecordDataValid section14Catalog 13 (⟨18,(2),[1,13],[151],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid173 : RecordDataValid section14Catalog 13 (⟨18,(2),[1,13],[147],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid174 : RecordDataValid section14Catalog 13 (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid175 : RecordDataValid section14Catalog 13 (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid176 : RecordDataValid section14Catalog 13 (⟨18,(3),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid177 : RecordDataValid section14Catalog 13 (⟨18,(3),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid178 : RecordDataValid section14Catalog 13 (⟨18,(3),[1,13],[146],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid179 : RecordDataValid section14Catalog 13 (⟨18,(3),[1,13],[151],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid180 : RecordDataValid section14Catalog 13 (⟨18,(3),[1,13],[147],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid181 : RecordDataValid section14Catalog 13 (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid182 : RecordDataValid section14Catalog 13 (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid183 : RecordDataValid section14Catalog 13 (⟨18,(4),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid184 : RecordDataValid section14Catalog 13 (⟨18,(4),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid185 : RecordDataValid section14Catalog 13 (⟨18,(4),[1,13],[146],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid186 : RecordDataValid section14Catalog 13 (⟨18,(4),[1,13],[151],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid187 : RecordDataValid section14Catalog 13 (⟨18,(4),[1,13],[147],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid188 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid189 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid190 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid191 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0160_0192 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 160).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 160).take 32 = [⟨18,(1),[1,2,5,6,13,14],[131],106⟩,⟨18,(1),[1,2,5,6,13,14],[150],125⟩,⟨18,(1),[1,2,13,14],[190],3⟩,⟨18,(1),[1,5,13],[135],125⟩,⟨18,(1),[1,13],[146],73⟩,⟨18,(1),[1,13],[151],125⟩,⟨18,(1),[1,13],[147],160⟩,⟨18,(2),[1,2,5,6,13,14],[131],106⟩,⟨18,(2),[1,2,5,6,13,14],[150],125⟩,⟨18,(2),[1,2,13,14],[190],3⟩,⟨18,(2),[1,5,13],[135],125⟩,⟨18,(2),[1,13],[146],73⟩,⟨18,(2),[1,13],[151],125⟩,⟨18,(2),[1,13],[147],160⟩,⟨18,(3),[1,2,5,6,13,14],[131],106⟩,⟨18,(3),[1,2,5,6,13,14],[150],125⟩,⟨18,(3),[1,2,13,14],[190],3⟩,⟨18,(3),[1,5,13],[135],125⟩,⟨18,(3),[1,13],[146],73⟩,⟨18,(3),[1,13],[151],125⟩,⟨18,(3),[1,13],[147],160⟩,⟨18,(4),[1,2,5,6,13,14],[131],106⟩,⟨18,(4),[1,2,5,6,13,14],[150],125⟩,⟨18,(4),[1,2,13,14],[190],3⟩,⟨18,(4),[1,5,13],[135],125⟩,⟨18,(4),[1,13],[146],73⟩,⟨18,(4),[1,13],[151],125⟩,⟨18,(4),[1,13],[147],160⟩,⟨18,(5),[1,2,5,6,13,14],[131],107⟩,⟨18,(5),[1,2,5,6,13,14],[150],126⟩,⟨18,(5),[1,2,13,14],[190],3⟩,⟨18,(5),[1,5,13],[135],126⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid160
  · exact recordValid_of_data section14Catalog 13 _ hnum valid161
  · exact recordValid_of_data section14Catalog 13 _ hnum valid162
  · exact recordValid_of_data section14Catalog 13 _ hnum valid163
  · exact recordValid_of_data section14Catalog 13 _ hnum valid164
  · exact recordValid_of_data section14Catalog 13 _ hnum valid165
  · exact recordValid_of_data section14Catalog 13 _ hnum valid166
  · exact recordValid_of_data section14Catalog 13 _ hnum valid167
  · exact recordValid_of_data section14Catalog 13 _ hnum valid168
  · exact recordValid_of_data section14Catalog 13 _ hnum valid169
  · exact recordValid_of_data section14Catalog 13 _ hnum valid170
  · exact recordValid_of_data section14Catalog 13 _ hnum valid171
  · exact recordValid_of_data section14Catalog 13 _ hnum valid172
  · exact recordValid_of_data section14Catalog 13 _ hnum valid173
  · exact recordValid_of_data section14Catalog 13 _ hnum valid174
  · exact recordValid_of_data section14Catalog 13 _ hnum valid175
  · exact recordValid_of_data section14Catalog 13 _ hnum valid176
  · exact recordValid_of_data section14Catalog 13 _ hnum valid177
  · exact recordValid_of_data section14Catalog 13 _ hnum valid178
  · exact recordValid_of_data section14Catalog 13 _ hnum valid179
  · exact recordValid_of_data section14Catalog 13 _ hnum valid180
  · exact recordValid_of_data section14Catalog 13 _ hnum valid181
  · exact recordValid_of_data section14Catalog 13 _ hnum valid182
  · exact recordValid_of_data section14Catalog 13 _ hnum valid183
  · exact recordValid_of_data section14Catalog 13 _ hnum valid184
  · exact recordValid_of_data section14Catalog 13 _ hnum valid185
  · exact recordValid_of_data section14Catalog 13 _ hnum valid186
  · exact recordValid_of_data section14Catalog 13 _ hnum valid187
  · exact recordValid_of_data section14Catalog 13 _ hnum valid188
  · exact recordValid_of_data section14Catalog 13 _ hnum valid189
  · exact recordValid_of_data section14Catalog 13 _ hnum valid190
  · exact recordValid_of_data section14Catalog 13 _ hnum valid191
end Section14Records_13_160_192

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0160_0192


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0192_0224
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_192_224
private theorem valid192 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid193 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid194 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid195 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid196 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid197 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid198 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid199 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid200 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid201 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid202 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid203 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid204 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid205 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid206 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid207 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid208 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid209 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid210 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid211 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid212 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid213 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid214 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid215 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid216 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid217 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid218 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid219 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid220 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid221 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid222 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid223 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0192_0224 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 192).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 192).take 32 = [⟨18,(5),[1,13],[146],74⟩,⟨18,(5),[1,13],[151],126⟩,⟨18,(5),[1,13],[147],161⟩,⟨18,(6),[1,2,5,6,13,14],[131],107⟩,⟨18,(6),[1,2,5,6,13,14],[150],126⟩,⟨18,(6),[1,2,13,14],[190],3⟩,⟨18,(6),[1,5,13],[135],126⟩,⟨18,(6),[1,13],[146],74⟩,⟨18,(6),[1,13],[151],126⟩,⟨18,(6),[1,13],[147],161⟩,⟨18,(7),[1,2,5,6,13,14],[131],107⟩,⟨18,(7),[1,2,5,6,13,14],[150],126⟩,⟨18,(7),[1,2,13,14],[190],3⟩,⟨18,(7),[1,5,13],[135],126⟩,⟨18,(7),[1,13],[146],74⟩,⟨18,(7),[1,13],[151],126⟩,⟨18,(7),[1,13],[147],161⟩,⟨18,(8),[1,2,5,6,13,14],[131],107⟩,⟨18,(8),[1,2,5,6,13,14],[150],126⟩,⟨18,(8),[1,2,13,14],[190],3⟩,⟨18,(8),[1,5,13],[135],126⟩,⟨18,(8),[1,13],[146],74⟩,⟨18,(8),[1,13],[151],126⟩,⟨18,(8),[1,13],[147],161⟩,⟨18,(9),[1,2,5,6,13,14],[131],107⟩,⟨18,(9),[1,2,5,6,13,14],[150],126⟩,⟨18,(9),[1,2,13,14],[190],3⟩,⟨18,(9),[1,5,13],[135],126⟩,⟨18,(9),[1,13],[146],74⟩,⟨18,(9),[1,13],[151],126⟩,⟨18,(9),[1,13],[147],161⟩,⟨18,(10),[1,2,5,6,13,14],[131],108⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid192
  · exact recordValid_of_data section14Catalog 13 _ hnum valid193
  · exact recordValid_of_data section14Catalog 13 _ hnum valid194
  · exact recordValid_of_data section14Catalog 13 _ hnum valid195
  · exact recordValid_of_data section14Catalog 13 _ hnum valid196
  · exact recordValid_of_data section14Catalog 13 _ hnum valid197
  · exact recordValid_of_data section14Catalog 13 _ hnum valid198
  · exact recordValid_of_data section14Catalog 13 _ hnum valid199
  · exact recordValid_of_data section14Catalog 13 _ hnum valid200
  · exact recordValid_of_data section14Catalog 13 _ hnum valid201
  · exact recordValid_of_data section14Catalog 13 _ hnum valid202
  · exact recordValid_of_data section14Catalog 13 _ hnum valid203
  · exact recordValid_of_data section14Catalog 13 _ hnum valid204
  · exact recordValid_of_data section14Catalog 13 _ hnum valid205
  · exact recordValid_of_data section14Catalog 13 _ hnum valid206
  · exact recordValid_of_data section14Catalog 13 _ hnum valid207
  · exact recordValid_of_data section14Catalog 13 _ hnum valid208
  · exact recordValid_of_data section14Catalog 13 _ hnum valid209
  · exact recordValid_of_data section14Catalog 13 _ hnum valid210
  · exact recordValid_of_data section14Catalog 13 _ hnum valid211
  · exact recordValid_of_data section14Catalog 13 _ hnum valid212
  · exact recordValid_of_data section14Catalog 13 _ hnum valid213
  · exact recordValid_of_data section14Catalog 13 _ hnum valid214
  · exact recordValid_of_data section14Catalog 13 _ hnum valid215
  · exact recordValid_of_data section14Catalog 13 _ hnum valid216
  · exact recordValid_of_data section14Catalog 13 _ hnum valid217
  · exact recordValid_of_data section14Catalog 13 _ hnum valid218
  · exact recordValid_of_data section14Catalog 13 _ hnum valid219
  · exact recordValid_of_data section14Catalog 13 _ hnum valid220
  · exact recordValid_of_data section14Catalog 13 _ hnum valid221
  · exact recordValid_of_data section14Catalog 13 _ hnum valid222
  · exact recordValid_of_data section14Catalog 13 _ hnum valid223
end Section14Records_13_192_224

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0192_0224


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0224_0256
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_224_256
private theorem valid224 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid225 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid226 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,5,13],[135],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid227 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,13],[146],75⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨75,[1,5,9,13],75⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid228 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,13],[151],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid229 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,13],[147],162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨162,[1,5,9,10,13],162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid230 : RecordDataValid section14Catalog 13 (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid231 : RecordDataValid section14Catalog 13 (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid232 : RecordDataValid section14Catalog 13 (⟨18,(11),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid233 : RecordDataValid section14Catalog 13 (⟨18,(11),[1,5,13],[135],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid234 : RecordDataValid section14Catalog 13 (⟨18,(11),[1,13],[146],76⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨76,[1,5,9,13],76⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid235 : RecordDataValid section14Catalog 13 (⟨18,(11),[1,13],[151],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid236 : RecordDataValid section14Catalog 13 (⟨18,(11),[1,13],[147],163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨163,[1,5,9,10,13],163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid237 : RecordDataValid section14Catalog 13 (⟨18,(12),[1,2,5,6,13,14],[131],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid238 : RecordDataValid section14Catalog 13 (⟨18,(12),[1,2,5,6,13,14],[150],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid239 : RecordDataValid section14Catalog 13 (⟨18,(12),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid240 : RecordDataValid section14Catalog 13 (⟨18,(12),[1,5,13],[135],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid241 : RecordDataValid section14Catalog 13 (⟨18,(12),[1,13],[146],77⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨77,[1,5,9,13],77⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid242 : RecordDataValid section14Catalog 13 (⟨18,(12),[1,13],[151],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid243 : RecordDataValid section14Catalog 13 (⟨18,(12),[1,13],[147],164⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨164,[1,5,9,10,13],164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid244 : RecordDataValid section14Catalog 13 (⟨18,(13),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid245 : RecordDataValid section14Catalog 13 (⟨18,(13),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid246 : RecordDataValid section14Catalog 13 (⟨18,(13),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid247 : RecordDataValid section14Catalog 13 (⟨18,(13),[1,5,13],[135],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid248 : RecordDataValid section14Catalog 13 (⟨18,(13),[1,13],[146],76⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨76,[1,5,9,13],76⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid249 : RecordDataValid section14Catalog 13 (⟨18,(13),[1,13],[151],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid250 : RecordDataValid section14Catalog 13 (⟨18,(13),[1,13],[147],163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨163,[1,5,9,10,13],163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid251 : RecordDataValid section14Catalog 13 (⟨18,(14),[1,2,5,6,13,14],[131],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid252 : RecordDataValid section14Catalog 13 (⟨18,(14),[1,2,5,6,13,14],[150],130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨130,[1,2,5,6,13,14],130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid253 : RecordDataValid section14Catalog 13 (⟨18,(14),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid254 : RecordDataValid section14Catalog 13 (⟨18,(14),[1,5,13],[135],130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨130,[1,2,5,6,13,14],130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid255 : RecordDataValid section14Catalog 13 (⟨18,(14),[1,13],[146],78⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨78,[1,5,9,13],78⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0224_0256 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 224).take 32 = [⟨18,(10),[1,2,5,6,13,14],[150],127⟩,⟨18,(10),[1,2,13,14],[190],3⟩,⟨18,(10),[1,5,13],[135],127⟩,⟨18,(10),[1,13],[146],75⟩,⟨18,(10),[1,13],[151],127⟩,⟨18,(10),[1,13],[147],162⟩,⟨18,(11),[1,2,5,6,13,14],[131],109⟩,⟨18,(11),[1,2,5,6,13,14],[150],128⟩,⟨18,(11),[1,2,13,14],[190],3⟩,⟨18,(11),[1,5,13],[135],128⟩,⟨18,(11),[1,13],[146],76⟩,⟨18,(11),[1,13],[151],128⟩,⟨18,(11),[1,13],[147],163⟩,⟨18,(12),[1,2,5,6,13,14],[131],110⟩,⟨18,(12),[1,2,5,6,13,14],[150],129⟩,⟨18,(12),[1,2,13,14],[190],3⟩,⟨18,(12),[1,5,13],[135],129⟩,⟨18,(12),[1,13],[146],77⟩,⟨18,(12),[1,13],[151],129⟩,⟨18,(12),[1,13],[147],164⟩,⟨18,(13),[1,2,5,6,13,14],[131],109⟩,⟨18,(13),[1,2,5,6,13,14],[150],128⟩,⟨18,(13),[1,2,13,14],[190],3⟩,⟨18,(13),[1,5,13],[135],128⟩,⟨18,(13),[1,13],[146],76⟩,⟨18,(13),[1,13],[151],128⟩,⟨18,(13),[1,13],[147],163⟩,⟨18,(14),[1,2,5,6,13,14],[131],111⟩,⟨18,(14),[1,2,5,6,13,14],[150],130⟩,⟨18,(14),[1,2,13,14],[190],3⟩,⟨18,(14),[1,5,13],[135],130⟩,⟨18,(14),[1,13],[146],78⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid224
  · exact recordValid_of_data section14Catalog 13 _ hnum valid225
  · exact recordValid_of_data section14Catalog 13 _ hnum valid226
  · exact recordValid_of_data section14Catalog 13 _ hnum valid227
  · exact recordValid_of_data section14Catalog 13 _ hnum valid228
  · exact recordValid_of_data section14Catalog 13 _ hnum valid229
  · exact recordValid_of_data section14Catalog 13 _ hnum valid230
  · exact recordValid_of_data section14Catalog 13 _ hnum valid231
  · exact recordValid_of_data section14Catalog 13 _ hnum valid232
  · exact recordValid_of_data section14Catalog 13 _ hnum valid233
  · exact recordValid_of_data section14Catalog 13 _ hnum valid234
  · exact recordValid_of_data section14Catalog 13 _ hnum valid235
  · exact recordValid_of_data section14Catalog 13 _ hnum valid236
  · exact recordValid_of_data section14Catalog 13 _ hnum valid237
  · exact recordValid_of_data section14Catalog 13 _ hnum valid238
  · exact recordValid_of_data section14Catalog 13 _ hnum valid239
  · exact recordValid_of_data section14Catalog 13 _ hnum valid240
  · exact recordValid_of_data section14Catalog 13 _ hnum valid241
  · exact recordValid_of_data section14Catalog 13 _ hnum valid242
  · exact recordValid_of_data section14Catalog 13 _ hnum valid243
  · exact recordValid_of_data section14Catalog 13 _ hnum valid244
  · exact recordValid_of_data section14Catalog 13 _ hnum valid245
  · exact recordValid_of_data section14Catalog 13 _ hnum valid246
  · exact recordValid_of_data section14Catalog 13 _ hnum valid247
  · exact recordValid_of_data section14Catalog 13 _ hnum valid248
  · exact recordValid_of_data section14Catalog 13 _ hnum valid249
  · exact recordValid_of_data section14Catalog 13 _ hnum valid250
  · exact recordValid_of_data section14Catalog 13 _ hnum valid251
  · exact recordValid_of_data section14Catalog 13 _ hnum valid252
  · exact recordValid_of_data section14Catalog 13 _ hnum valid253
  · exact recordValid_of_data section14Catalog 13 _ hnum valid254
  · exact recordValid_of_data section14Catalog 13 _ hnum valid255
end Section14Records_13_224_256

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0224_0256


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0256_0288
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_256_288
private theorem valid256 : RecordDataValid section14Catalog 13 (⟨18,(14),[1,13],[151],130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨130,[1,2,5,6,13,14],130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid257 : RecordDataValid section14Catalog 13 (⟨18,(14),[1,13],[147],165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨165,[1,5,9,10,13],165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid258 : RecordDataValid section14Catalog 13 (⟨18,(15),[1,2,5,6,13,14],[131],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid259 : RecordDataValid section14Catalog 13 (⟨18,(15),[1,2,5,6,13,14],[150],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid260 : RecordDataValid section14Catalog 13 (⟨18,(15),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid261 : RecordDataValid section14Catalog 13 (⟨18,(15),[1,5,13],[135],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid262 : RecordDataValid section14Catalog 13 (⟨18,(15),[1,13],[146],75⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨75,[1,5,9,13],75⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid263 : RecordDataValid section14Catalog 13 (⟨18,(15),[1,13],[151],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid264 : RecordDataValid section14Catalog 13 (⟨18,(15),[1,13],[147],162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨162,[1,5,9,10,13],162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid265 : RecordDataValid section14Catalog 13 (⟨18,(16),[1,2,5,6,13,14],[131],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid266 : RecordDataValid section14Catalog 13 (⟨18,(16),[1,2,5,6,13,14],[150],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid267 : RecordDataValid section14Catalog 13 (⟨18,(16),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid268 : RecordDataValid section14Catalog 13 (⟨18,(16),[1,5,13],[135],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid269 : RecordDataValid section14Catalog 13 (⟨18,(16),[1,13],[146],79⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨79,[1,5,9,13],79⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid270 : RecordDataValid section14Catalog 13 (⟨18,(16),[1,13],[151],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid271 : RecordDataValid section14Catalog 13 (⟨18,(16),[1,13],[147],166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨166,[1,5,9,10,13],166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid272 : RecordDataValid section14Catalog 13 (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid273 : RecordDataValid section14Catalog 13 (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid274 : RecordDataValid section14Catalog 13 (⟨18,(17),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid275 : RecordDataValid section14Catalog 13 (⟨18,(17),[1,5,13],[135],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid276 : RecordDataValid section14Catalog 13 (⟨18,(17),[1,13],[146],79⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨79,[1,5,9,13],79⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid277 : RecordDataValid section14Catalog 13 (⟨18,(17),[1,13],[151],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid278 : RecordDataValid section14Catalog 13 (⟨18,(17),[1,13],[147],166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨166,[1,5,9,10,13],166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid279 : RecordDataValid section14Catalog 13 (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid280 : RecordDataValid section14Catalog 13 (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid281 : RecordDataValid section14Catalog 13 (⟨18,(18),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid282 : RecordDataValid section14Catalog 13 (⟨18,(18),[1,5,13],[135],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid283 : RecordDataValid section14Catalog 13 (⟨18,(18),[1,13],[146],79⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨79,[1,5,9,13],79⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid284 : RecordDataValid section14Catalog 13 (⟨18,(18),[1,13],[151],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid285 : RecordDataValid section14Catalog 13 (⟨18,(18),[1,13],[147],166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨166,[1,5,9,10,13],166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid286 : RecordDataValid section14Catalog 13 (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid287 : RecordDataValid section14Catalog 13 (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0256_0288 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 256).take 32 = [⟨18,(14),[1,13],[151],130⟩,⟨18,(14),[1,13],[147],165⟩,⟨18,(15),[1,2,5,6,13,14],[131],108⟩,⟨18,(15),[1,2,5,6,13,14],[150],127⟩,⟨18,(15),[1,2,13,14],[190],3⟩,⟨18,(15),[1,5,13],[135],127⟩,⟨18,(15),[1,13],[146],75⟩,⟨18,(15),[1,13],[151],127⟩,⟨18,(15),[1,13],[147],162⟩,⟨18,(16),[1,2,5,6,13,14],[131],112⟩,⟨18,(16),[1,2,5,6,13,14],[150],131⟩,⟨18,(16),[1,2,13,14],[190],3⟩,⟨18,(16),[1,5,13],[135],131⟩,⟨18,(16),[1,13],[146],79⟩,⟨18,(16),[1,13],[151],131⟩,⟨18,(16),[1,13],[147],166⟩,⟨18,(17),[1,2,5,6,13,14],[131],112⟩,⟨18,(17),[1,2,5,6,13,14],[150],131⟩,⟨18,(17),[1,2,13,14],[190],3⟩,⟨18,(17),[1,5,13],[135],131⟩,⟨18,(17),[1,13],[146],79⟩,⟨18,(17),[1,13],[151],131⟩,⟨18,(17),[1,13],[147],166⟩,⟨18,(18),[1,2,5,6,13,14],[131],112⟩,⟨18,(18),[1,2,5,6,13,14],[150],131⟩,⟨18,(18),[1,2,13,14],[190],3⟩,⟨18,(18),[1,5,13],[135],131⟩,⟨18,(18),[1,13],[146],79⟩,⟨18,(18),[1,13],[151],131⟩,⟨18,(18),[1,13],[147],166⟩,⟨18,(19),[1,2,5,6,13,14],[131],112⟩,⟨18,(19),[1,2,5,6,13,14],[150],131⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid256
  · exact recordValid_of_data section14Catalog 13 _ hnum valid257
  · exact recordValid_of_data section14Catalog 13 _ hnum valid258
  · exact recordValid_of_data section14Catalog 13 _ hnum valid259
  · exact recordValid_of_data section14Catalog 13 _ hnum valid260
  · exact recordValid_of_data section14Catalog 13 _ hnum valid261
  · exact recordValid_of_data section14Catalog 13 _ hnum valid262
  · exact recordValid_of_data section14Catalog 13 _ hnum valid263
  · exact recordValid_of_data section14Catalog 13 _ hnum valid264
  · exact recordValid_of_data section14Catalog 13 _ hnum valid265
  · exact recordValid_of_data section14Catalog 13 _ hnum valid266
  · exact recordValid_of_data section14Catalog 13 _ hnum valid267
  · exact recordValid_of_data section14Catalog 13 _ hnum valid268
  · exact recordValid_of_data section14Catalog 13 _ hnum valid269
  · exact recordValid_of_data section14Catalog 13 _ hnum valid270
  · exact recordValid_of_data section14Catalog 13 _ hnum valid271
  · exact recordValid_of_data section14Catalog 13 _ hnum valid272
  · exact recordValid_of_data section14Catalog 13 _ hnum valid273
  · exact recordValid_of_data section14Catalog 13 _ hnum valid274
  · exact recordValid_of_data section14Catalog 13 _ hnum valid275
  · exact recordValid_of_data section14Catalog 13 _ hnum valid276
  · exact recordValid_of_data section14Catalog 13 _ hnum valid277
  · exact recordValid_of_data section14Catalog 13 _ hnum valid278
  · exact recordValid_of_data section14Catalog 13 _ hnum valid279
  · exact recordValid_of_data section14Catalog 13 _ hnum valid280
  · exact recordValid_of_data section14Catalog 13 _ hnum valid281
  · exact recordValid_of_data section14Catalog 13 _ hnum valid282
  · exact recordValid_of_data section14Catalog 13 _ hnum valid283
  · exact recordValid_of_data section14Catalog 13 _ hnum valid284
  · exact recordValid_of_data section14Catalog 13 _ hnum valid285
  · exact recordValid_of_data section14Catalog 13 _ hnum valid286
  · exact recordValid_of_data section14Catalog 13 _ hnum valid287
end Section14Records_13_256_288

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0256_0288


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0288_0320
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_288_320
private theorem valid288 : RecordDataValid section14Catalog 13 (⟨18,(19),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid289 : RecordDataValid section14Catalog 13 (⟨18,(19),[1,5,13],[135],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid290 : RecordDataValid section14Catalog 13 (⟨18,(19),[1,13],[146],79⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨79,[1,5,9,13],79⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid291 : RecordDataValid section14Catalog 13 (⟨18,(19),[1,13],[151],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid292 : RecordDataValid section14Catalog 13 (⟨18,(19),[1,13],[147],166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨166,[1,5,9,10,13],166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid293 : RecordDataValid section14Catalog 13 (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid294 : RecordDataValid section14Catalog 13 (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid295 : RecordDataValid section14Catalog 13 (⟨18,(20),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid296 : RecordDataValid section14Catalog 13 (⟨18,(20),[1,5,13],[135],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid297 : RecordDataValid section14Catalog 13 (⟨18,(20),[1,13],[146],75⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨75,[1,5,9,13],75⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid298 : RecordDataValid section14Catalog 13 (⟨18,(20),[1,13],[151],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid299 : RecordDataValid section14Catalog 13 (⟨18,(20),[1,13],[147],162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨162,[1,5,9,10,13],162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid300 : RecordDataValid section14Catalog 13 (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid301 : RecordDataValid section14Catalog 13 (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid302 : RecordDataValid section14Catalog 13 (⟨18,(21),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid303 : RecordDataValid section14Catalog 13 (⟨18,(21),[1,5,13],[135],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid304 : RecordDataValid section14Catalog 13 (⟨18,(21),[1,13],[146],76⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨76,[1,5,9,13],76⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid305 : RecordDataValid section14Catalog 13 (⟨18,(21),[1,13],[151],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid306 : RecordDataValid section14Catalog 13 (⟨18,(21),[1,13],[147],163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨163,[1,5,9,10,13],163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid307 : RecordDataValid section14Catalog 13 (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid308 : RecordDataValid section14Catalog 13 (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid309 : RecordDataValid section14Catalog 13 (⟨18,(22),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid310 : RecordDataValid section14Catalog 13 (⟨18,(22),[1,5,13],[135],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid311 : RecordDataValid section14Catalog 13 (⟨18,(22),[1,13],[146],77⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨77,[1,5,9,13],77⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid312 : RecordDataValid section14Catalog 13 (⟨18,(22),[1,13],[151],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid313 : RecordDataValid section14Catalog 13 (⟨18,(22),[1,13],[147],164⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨164,[1,5,9,10,13],164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid314 : RecordDataValid section14Catalog 13 (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid315 : RecordDataValid section14Catalog 13 (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid316 : RecordDataValid section14Catalog 13 (⟨18,(23),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid317 : RecordDataValid section14Catalog 13 (⟨18,(23),[1,5,13],[135],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid318 : RecordDataValid section14Catalog 13 (⟨18,(23),[1,13],[146],76⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨76,[1,5,9,13],76⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid319 : RecordDataValid section14Catalog 13 (⟨18,(23),[1,13],[151],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0288_0320 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 288).take 32 = [⟨18,(19),[1,2,13,14],[190],3⟩,⟨18,(19),[1,5,13],[135],131⟩,⟨18,(19),[1,13],[146],79⟩,⟨18,(19),[1,13],[151],131⟩,⟨18,(19),[1,13],[147],166⟩,⟨18,(20),[1,2,5,6,13,14],[131],108⟩,⟨18,(20),[1,2,5,6,13,14],[150],127⟩,⟨18,(20),[1,2,13,14],[190],3⟩,⟨18,(20),[1,5,13],[135],127⟩,⟨18,(20),[1,13],[146],75⟩,⟨18,(20),[1,13],[151],127⟩,⟨18,(20),[1,13],[147],162⟩,⟨18,(21),[1,2,5,6,13,14],[131],109⟩,⟨18,(21),[1,2,5,6,13,14],[150],128⟩,⟨18,(21),[1,2,13,14],[190],3⟩,⟨18,(21),[1,5,13],[135],128⟩,⟨18,(21),[1,13],[146],76⟩,⟨18,(21),[1,13],[151],128⟩,⟨18,(21),[1,13],[147],163⟩,⟨18,(22),[1,2,5,6,13,14],[131],110⟩,⟨18,(22),[1,2,5,6,13,14],[150],129⟩,⟨18,(22),[1,2,13,14],[190],3⟩,⟨18,(22),[1,5,13],[135],129⟩,⟨18,(22),[1,13],[146],77⟩,⟨18,(22),[1,13],[151],129⟩,⟨18,(22),[1,13],[147],164⟩,⟨18,(23),[1,2,5,6,13,14],[131],109⟩,⟨18,(23),[1,2,5,6,13,14],[150],128⟩,⟨18,(23),[1,2,13,14],[190],3⟩,⟨18,(23),[1,5,13],[135],128⟩,⟨18,(23),[1,13],[146],76⟩,⟨18,(23),[1,13],[151],128⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid288
  · exact recordValid_of_data section14Catalog 13 _ hnum valid289
  · exact recordValid_of_data section14Catalog 13 _ hnum valid290
  · exact recordValid_of_data section14Catalog 13 _ hnum valid291
  · exact recordValid_of_data section14Catalog 13 _ hnum valid292
  · exact recordValid_of_data section14Catalog 13 _ hnum valid293
  · exact recordValid_of_data section14Catalog 13 _ hnum valid294
  · exact recordValid_of_data section14Catalog 13 _ hnum valid295
  · exact recordValid_of_data section14Catalog 13 _ hnum valid296
  · exact recordValid_of_data section14Catalog 13 _ hnum valid297
  · exact recordValid_of_data section14Catalog 13 _ hnum valid298
  · exact recordValid_of_data section14Catalog 13 _ hnum valid299
  · exact recordValid_of_data section14Catalog 13 _ hnum valid300
  · exact recordValid_of_data section14Catalog 13 _ hnum valid301
  · exact recordValid_of_data section14Catalog 13 _ hnum valid302
  · exact recordValid_of_data section14Catalog 13 _ hnum valid303
  · exact recordValid_of_data section14Catalog 13 _ hnum valid304
  · exact recordValid_of_data section14Catalog 13 _ hnum valid305
  · exact recordValid_of_data section14Catalog 13 _ hnum valid306
  · exact recordValid_of_data section14Catalog 13 _ hnum valid307
  · exact recordValid_of_data section14Catalog 13 _ hnum valid308
  · exact recordValid_of_data section14Catalog 13 _ hnum valid309
  · exact recordValid_of_data section14Catalog 13 _ hnum valid310
  · exact recordValid_of_data section14Catalog 13 _ hnum valid311
  · exact recordValid_of_data section14Catalog 13 _ hnum valid312
  · exact recordValid_of_data section14Catalog 13 _ hnum valid313
  · exact recordValid_of_data section14Catalog 13 _ hnum valid314
  · exact recordValid_of_data section14Catalog 13 _ hnum valid315
  · exact recordValid_of_data section14Catalog 13 _ hnum valid316
  · exact recordValid_of_data section14Catalog 13 _ hnum valid317
  · exact recordValid_of_data section14Catalog 13 _ hnum valid318
  · exact recordValid_of_data section14Catalog 13 _ hnum valid319
end Section14Records_13_288_320

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0288_0320

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 64).take 256, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 64 192 320 (by decide) (by decide) (all_of_interval_split P xs 64 128 192 (by decide) (by decide) (all_of_interval_split P xs 64 96 128 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0064_0096 hnum) (Freiman.workReverse20260919_s0013_records_0096_0128 hnum)) (all_of_interval_split P xs 128 160 192 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0128_0160 hnum) (Freiman.workReverse20260919_s0013_records_0160_0192 hnum))) (all_of_interval_split P xs 192 256 320 (by decide) (by decide) (all_of_interval_split P xs 192 224 256 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0192_0224 hnum) (Freiman.workReverse20260919_s0013_records_0224_0256 hnum)) (all_of_interval_split P xs 256 288 320 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0256_0288 hnum) (Freiman.workReverse20260919_s0013_records_0288_0320 hnum))))

#print axioms solution
