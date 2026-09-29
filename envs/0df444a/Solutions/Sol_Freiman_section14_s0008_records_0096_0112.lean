-- Prove2me | solution 1 for Freiman.section14_s0008_records_0096_0112
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:46:10.940607+00:00
-- url     : https://prove2.me/submissions/24df3043-3d7b-4a4f-964a-78afb98e8505

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
namespace Section14Records_8_96_112
private theorem valid96 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[0],63⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨63,[1,2,4,5,6,8,9,10,12,13,14,16],63⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid97 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[1],64⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨64,[1,2,4,5,6,8,9,10,12,13,14,16],64⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid98 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[4],65⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨65,[1,2,4,5,6,8,9,10,12,13,14,16],65⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid99 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[9],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid100 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[13],72⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨72,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],72⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid101 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[10],205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨205,[1,2,4,5,6,8,9,10,12,13,14,16],205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid102 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[11],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid103 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[15],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid104 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,12,16],[7],1260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1260,[4,8,12,16],1264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid105 : RecordDataValid section14Catalog 8 (⟨16,(-1),[4,8,16],[2],1249⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1249,[4,8,16],1253⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid106 : RecordDataValid section14Catalog 8 (⟨16,(-1),[8,12],[14],1398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1398,[5,6,7,8,9,10,12],1403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid107 : RecordDataValid section14Catalog 8 (⟨16,(-1),[8,12],[3],1630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1630,[8,12],1635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid108 : RecordDataValid section14Catalog 8 (⟨20,(0),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid109 : RecordDataValid section14Catalog 8 (⟨20,(1),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid110 : RecordDataValid section14Catalog 8 (⟨20,(2),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid111 : RecordDataValid section14Catalog 8 (⟨20,(3),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 96).take 16, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 96).take 16 = [⟨16,(-1),[4,8,12,16],[0],63⟩,⟨16,(-1),[4,8,12,16],[1],64⟩,⟨16,(-1),[4,8,12,16],[4],65⟩,⟨16,(-1),[4,8,12,16],[9],70⟩,⟨16,(-1),[4,8,12,16],[13],72⟩,⟨16,(-1),[4,8,12,16],[10],205⟩,⟨16,(-1),[4,8,12,16],[11],207⟩,⟨16,(-1),[4,8,12,16],[15],239⟩,⟨16,(-1),[4,8,12,16],[7],1260⟩,⟨16,(-1),[4,8,16],[2],1249⟩,⟨16,(-1),[8,12],[14],1398⟩,⟨16,(-1),[8,12],[3],1630⟩,⟨20,(0),[4,8,16],[6],3⟩,⟨20,(1),[4,8,16],[6],3⟩,⟨20,(2),[4,8,16],[6],3⟩,⟨20,(3),[4,8,16],[6],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid96
  · exact recordValid_of_data section14Catalog 8 _ hnum valid97
  · exact recordValid_of_data section14Catalog 8 _ hnum valid98
  · exact recordValid_of_data section14Catalog 8 _ hnum valid99
  · exact recordValid_of_data section14Catalog 8 _ hnum valid100
  · exact recordValid_of_data section14Catalog 8 _ hnum valid101
  · exact recordValid_of_data section14Catalog 8 _ hnum valid102
  · exact recordValid_of_data section14Catalog 8 _ hnum valid103
  · exact recordValid_of_data section14Catalog 8 _ hnum valid104
  · exact recordValid_of_data section14Catalog 8 _ hnum valid105
  · exact recordValid_of_data section14Catalog 8 _ hnum valid106
  · exact recordValid_of_data section14Catalog 8 _ hnum valid107
  · exact recordValid_of_data section14Catalog 8 _ hnum valid108
  · exact recordValid_of_data section14Catalog 8 _ hnum valid109
  · exact recordValid_of_data section14Catalog 8 _ hnum valid110
  · exact recordValid_of_data section14Catalog 8 _ hnum valid111
end Section14Records_8_96_112

#print axioms solution
