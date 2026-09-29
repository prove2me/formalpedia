-- Prove2me | solution 1 for Freiman.section14_s0003_records_1024_1056
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T12:46:07.418084+00:00
-- url     : https://prove2.me/submissions/f7e3ec09-b486-4b54-953b-5ca3abec2acf

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
namespace Section14Records_3_1024_1056
private theorem valid1024 : RecordDataValid section14Catalog 3 (⟨192,(12),[3,7],[11],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1025 : RecordDataValid section14Catalog 3 (⟨192,(12),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1026 : RecordDataValid section14Catalog 3 (⟨192,(13),[3,7],[11],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1027 : RecordDataValid section14Catalog 3 (⟨192,(13),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1028 : RecordDataValid section14Catalog 3 (⟨192,(14),[3,7],[11],1004⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1004,[3,5,6,7],1008⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1029 : RecordDataValid section14Catalog 3 (⟨192,(14),[3,7,15],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1030 : RecordDataValid section14Catalog 3 (⟨192,(15),[3,7],[11],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1031 : RecordDataValid section14Catalog 3 (⟨192,(15),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1032 : RecordDataValid section14Catalog 3 (⟨192,(16),[3,7],[11],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1033 : RecordDataValid section14Catalog 3 (⟨192,(16),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1034 : RecordDataValid section14Catalog 3 (⟨192,(17),[3,7],[11],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1035 : RecordDataValid section14Catalog 3 (⟨192,(17),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1036 : RecordDataValid section14Catalog 3 (⟨192,(18),[3,7],[11],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1037 : RecordDataValid section14Catalog 3 (⟨192,(18),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1038 : RecordDataValid section14Catalog 3 (⟨192,(19),[3,7],[11],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1039 : RecordDataValid section14Catalog 3 (⟨192,(19),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1040 : RecordDataValid section14Catalog 3 (⟨192,(20),[3,7],[11],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1041 : RecordDataValid section14Catalog 3 (⟨192,(20),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1042 : RecordDataValid section14Catalog 3 (⟨192,(21),[3,7],[11],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1043 : RecordDataValid section14Catalog 3 (⟨192,(21),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1044 : RecordDataValid section14Catalog 3 (⟨192,(22),[3,7],[11],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1045 : RecordDataValid section14Catalog 3 (⟨192,(22),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1046 : RecordDataValid section14Catalog 3 (⟨192,(23),[3,7],[11],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1047 : RecordDataValid section14Catalog 3 (⟨192,(23),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1048 : RecordDataValid section14Catalog 3 (⟨192,(24),[3,7],[11],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1049 : RecordDataValid section14Catalog 3 (⟨192,(24),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1050 : RecordDataValid section14Catalog 3 (⟨195,(0),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1051 : RecordDataValid section14Catalog 3 (⟨195,(0),[3,7],[11],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1052 : RecordDataValid section14Catalog 3 (⟨195,(1),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1053 : RecordDataValid section14Catalog 3 (⟨195,(1),[3,7],[11],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1054 : RecordDataValid section14Catalog 3 (⟨195,(2),[3,4,8,12,15,16],[10],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1055 : RecordDataValid section14Catalog 3 (⟨195,(2),[3,7],[11],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1024).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1024).take 32 = [⟨192,(12),[3,7],[11],1005⟩,⟨192,(12),[3,7,15],[10],445⟩,⟨192,(13),[3,7],[11],1005⟩,⟨192,(13),[3,7,15],[10],445⟩,⟨192,(14),[3,7],[11],1004⟩,⟨192,(14),[3,7,15],[10],444⟩,⟨192,(15),[3,7],[11],1006⟩,⟨192,(15),[3,7,15],[10],446⟩,⟨192,(16),[3,7],[11],1006⟩,⟨192,(16),[3,7,15],[10],446⟩,⟨192,(17),[3,7],[11],1006⟩,⟨192,(17),[3,7,15],[10],446⟩,⟨192,(18),[3,7],[11],1006⟩,⟨192,(18),[3,7,15],[10],446⟩,⟨192,(19),[3,7],[11],1006⟩,⟨192,(19),[3,7,15],[10],446⟩,⟨192,(20),[3,7],[11],1007⟩,⟨192,(20),[3,7,15],[10],447⟩,⟨192,(21),[3,7],[11],1007⟩,⟨192,(21),[3,7,15],[10],447⟩,⟨192,(22),[3,7],[11],1007⟩,⟨192,(22),[3,7,15],[10],447⟩,⟨192,(23),[3,7],[11],1007⟩,⟨192,(23),[3,7,15],[10],447⟩,⟨192,(24),[3,7],[11],1007⟩,⟨192,(24),[3,7,15],[10],447⟩,⟨195,(0),[3,4,8,12,15,16],[10],697⟩,⟨195,(0),[3,7],[11],697⟩,⟨195,(1),[3,4,8,12,15,16],[10],697⟩,⟨195,(1),[3,7],[11],697⟩,⟨195,(2),[3,4,8,12,15,16],[10],698⟩,⟨195,(2),[3,7],[11],698⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1024
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1025
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1026
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1027
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1028
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1029
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1030
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1031
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1032
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1033
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1034
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1035
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1036
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1037
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1038
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1039
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1040
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1041
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1042
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1043
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1044
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1045
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1046
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1047
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1048
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1049
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1050
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1051
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1052
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1053
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1054
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1055
end Section14Records_3_1024_1056

#print axioms solution
