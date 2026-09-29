-- Prove2me | solution 1 for Freiman.section14_s0015_records_0000_0032
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:37:59.354376+00:00
-- url     : https://prove2.me/submissions/19ea83eb-f8bb-47ce-a9c4-877531ad7ade

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
namespace Section14Records_15_0_32
private theorem valid0 : RecordDataValid section14Catalog 15 (⟨1,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1 : RecordDataValid section14Catalog 15 (⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2 : RecordDataValid section14Catalog 15 (⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3 : RecordDataValid section14Catalog 15 (⟨1,(-1),[3,7,15],[2,3],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4 : RecordDataValid section14Catalog 15 (⟨1,(-1),[3,7,15],[4,6,7],5⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid5 : RecordDataValid section14Catalog 15 (⟨1,(-1),[3,7,15],[8],7⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨7,[1,2,3,5,6,7,13,14,15],7⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid6 : RecordDataValid section14Catalog 15 (⟨1,(-1),[3,7,15],[9],9⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨9,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],9⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid7 : RecordDataValid section14Catalog 15 (⟨1,(-1),[3,7,15],[11],54⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨54,[1,2,3,5,6,7,13,14,15],54⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid8 : RecordDataValid section14Catalog 15 (⟨1,(-1),[3,7,15],[12,13,14,15],56⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨56,[1,2,3,5,6,7,9,10,11,13,14,15],56⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid9 : RecordDataValid section14Catalog 15 (⟨5,(0),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid10 : RecordDataValid section14Catalog 15 (⟨5,(1),[3,4,7,8,15,16],[10],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid11 : RecordDataValid section14Catalog 15 (⟨5,(2),[3,4,7,15,16],[10],12⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨12,[1,2,3,4,6,7,13,14,15,16],12⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid12 : RecordDataValid section14Catalog 15 (⟨5,(3),[3,4,7,15,16],[10],13⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨13,[1,2,3,4,6,7,13,14,15,16],13⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid13 : RecordDataValid section14Catalog 15 (⟨5,(4),[3,4,7,15,16],[10],14⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨14,[1,2,3,4,6,7,11,13,14,15,16],14⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid14 : RecordDataValid section14Catalog 15 (⟨5,(5),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid15 : RecordDataValid section14Catalog 15 (⟨5,(6),[3,4,7,8,15,16],[10],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid16 : RecordDataValid section14Catalog 15 (⟨5,(7),[3,4,7,8,15,16],[10],15⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨15,[1,2,3,4,5,6,7,8,13,14,15,16],15⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid17 : RecordDataValid section14Catalog 15 (⟨5,(8),[3,4,7,8,15,16],[10],16⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨16,[1,2,3,4,5,6,7,8,13,14,15,16],16⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid18 : RecordDataValid section14Catalog 15 (⟨5,(9),[3,4,7,8,15,16],[10],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid19 : RecordDataValid section14Catalog 15 (⟨5,(10),[3,4,7,8,15,16],[10],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid20 : RecordDataValid section14Catalog 15 (⟨5,(11),[3,4,7,8,15,16],[10],19⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨19,[1,2,3,4,5,6,7,8,13,14,15,16],19⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid21 : RecordDataValid section14Catalog 15 (⟨5,(12),[3,4,7,8,15,16],[10],20⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨20,[1,2,3,4,5,6,7,8,13,14,15,16],20⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid22 : RecordDataValid section14Catalog 15 (⟨5,(13),[3,4,7,8,15,16],[10],20⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨20,[1,2,3,4,5,6,7,8,13,14,15,16],20⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid23 : RecordDataValid section14Catalog 15 (⟨5,(14),[3,4,7,8,15,16],[10],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid24 : RecordDataValid section14Catalog 15 (⟨5,(15),[3,4,7,8,15,16],[10],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid25 : RecordDataValid section14Catalog 15 (⟨5,(16),[3,4,7,8,15,16],[10],22⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨22,[1,2,3,4,5,6,7,8,13,14,15,16],22⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid26 : RecordDataValid section14Catalog 15 (⟨5,(17),[3,4,7,8,15,16],[10],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid27 : RecordDataValid section14Catalog 15 (⟨5,(18),[3,4,7,8,15,16],[10],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid28 : RecordDataValid section14Catalog 15 (⟨5,(19),[3,4,7,8,15,16],[10],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid29 : RecordDataValid section14Catalog 15 (⟨5,(20),[3,4,7,8,15,16],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid30 : RecordDataValid section14Catalog 15 (⟨5,(21),[3,4,7,8,15,16],[10],25⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨25,[1,2,3,4,5,6,7,8,13,14,15,16],25⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid31 : RecordDataValid section14Catalog 15 (⟨5,(22),[3,4,7,8,15,16],[10],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 0).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 0).take 32 = [⟨1,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],1⟩,⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩,⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩,⟨1,(-1),[3,7,15],[2,3],1⟩,⟨1,(-1),[3,7,15],[4,6,7],5⟩,⟨1,(-1),[3,7,15],[8],7⟩,⟨1,(-1),[3,7,15],[9],9⟩,⟨1,(-1),[3,7,15],[11],54⟩,⟨1,(-1),[3,7,15],[12,13,14,15],56⟩,⟨5,(0),[3,4,7,8,15,16],[10],10⟩,⟨5,(1),[3,4,7,8,15,16],[10],11⟩,⟨5,(2),[3,4,7,15,16],[10],12⟩,⟨5,(3),[3,4,7,15,16],[10],13⟩,⟨5,(4),[3,4,7,15,16],[10],14⟩,⟨5,(5),[3,4,7,8,15,16],[10],10⟩,⟨5,(6),[3,4,7,8,15,16],[10],11⟩,⟨5,(7),[3,4,7,8,15,16],[10],15⟩,⟨5,(8),[3,4,7,8,15,16],[10],16⟩,⟨5,(9),[3,4,7,8,15,16],[10],17⟩,⟨5,(10),[3,4,7,8,15,16],[10],18⟩,⟨5,(11),[3,4,7,8,15,16],[10],19⟩,⟨5,(12),[3,4,7,8,15,16],[10],20⟩,⟨5,(13),[3,4,7,8,15,16],[10],20⟩,⟨5,(14),[3,4,7,8,15,16],[10],17⟩,⟨5,(15),[3,4,7,8,15,16],[10],21⟩,⟨5,(16),[3,4,7,8,15,16],[10],22⟩,⟨5,(17),[3,4,7,8,15,16],[10],23⟩,⟨5,(18),[3,4,7,8,15,16],[10],23⟩,⟨5,(19),[3,4,7,8,15,16],[10],23⟩,⟨5,(20),[3,4,7,8,15,16],[10],24⟩,⟨5,(21),[3,4,7,8,15,16],[10],25⟩,⟨5,(22),[3,4,7,8,15,16],[10],26⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid0
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1
  · exact recordValid_of_data section14Catalog 15 _ hnum valid2
  · exact recordValid_of_data section14Catalog 15 _ hnum valid3
  · exact recordValid_of_data section14Catalog 15 _ hnum valid4
  · exact recordValid_of_data section14Catalog 15 _ hnum valid5
  · exact recordValid_of_data section14Catalog 15 _ hnum valid6
  · exact recordValid_of_data section14Catalog 15 _ hnum valid7
  · exact recordValid_of_data section14Catalog 15 _ hnum valid8
  · exact recordValid_of_data section14Catalog 15 _ hnum valid9
  · exact recordValid_of_data section14Catalog 15 _ hnum valid10
  · exact recordValid_of_data section14Catalog 15 _ hnum valid11
  · exact recordValid_of_data section14Catalog 15 _ hnum valid12
  · exact recordValid_of_data section14Catalog 15 _ hnum valid13
  · exact recordValid_of_data section14Catalog 15 _ hnum valid14
  · exact recordValid_of_data section14Catalog 15 _ hnum valid15
  · exact recordValid_of_data section14Catalog 15 _ hnum valid16
  · exact recordValid_of_data section14Catalog 15 _ hnum valid17
  · exact recordValid_of_data section14Catalog 15 _ hnum valid18
  · exact recordValid_of_data section14Catalog 15 _ hnum valid19
  · exact recordValid_of_data section14Catalog 15 _ hnum valid20
  · exact recordValid_of_data section14Catalog 15 _ hnum valid21
  · exact recordValid_of_data section14Catalog 15 _ hnum valid22
  · exact recordValid_of_data section14Catalog 15 _ hnum valid23
  · exact recordValid_of_data section14Catalog 15 _ hnum valid24
  · exact recordValid_of_data section14Catalog 15 _ hnum valid25
  · exact recordValid_of_data section14Catalog 15 _ hnum valid26
  · exact recordValid_of_data section14Catalog 15 _ hnum valid27
  · exact recordValid_of_data section14Catalog 15 _ hnum valid28
  · exact recordValid_of_data section14Catalog 15 _ hnum valid29
  · exact recordValid_of_data section14Catalog 15 _ hnum valid30
  · exact recordValid_of_data section14Catalog 15 _ hnum valid31
end Section14Records_15_0_32

#print axioms solution
