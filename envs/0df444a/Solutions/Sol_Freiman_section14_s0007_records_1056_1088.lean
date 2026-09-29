-- Prove2me | solution 1 for Freiman.section14_s0007_records_1056_1088
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:50:01.593486+00:00
-- url     : https://prove2.me/submissions/88e24de1-0e21-4918-a112-3397ad43e24c

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
namespace Section14Records_7_1056_1088
private theorem valid1056 : RecordDataValid section14Catalog 7 (⟨195,(4),[7],[10],1590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1590,[7],1595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1057 : RecordDataValid section14Catalog 7 (⟨195,(5),[3,7],[11],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1058 : RecordDataValid section14Catalog 7 (⟨195,(5),[7],[10],1591⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1591,[7],1596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1059 : RecordDataValid section14Catalog 7 (⟨195,(6),[3,7],[11],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1060 : RecordDataValid section14Catalog 7 (⟨195,(6),[7],[10],1590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1590,[7],1595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1061 : RecordDataValid section14Catalog 7 (⟨195,(7),[3,7],[11],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1062 : RecordDataValid section14Catalog 7 (⟨195,(7),[7],[10],1592⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1592,[7],1597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1063 : RecordDataValid section14Catalog 7 (⟨195,(8),[3,4,7,15,16],[10],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1064 : RecordDataValid section14Catalog 7 (⟨195,(8),[3,7],[11],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1065 : RecordDataValid section14Catalog 7 (⟨195,(9),[3,4,7,15,16],[10],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1066 : RecordDataValid section14Catalog 7 (⟨195,(9),[3,7],[11],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1067 : RecordDataValid section14Catalog 7 (⟨197,(0),[3,7],[11],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1068 : RecordDataValid section14Catalog 7 (⟨197,(0),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1069 : RecordDataValid section14Catalog 7 (⟨197,(1),[3,7],[11],1009⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1009,[3,5,6,7],1013⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1070 : RecordDataValid section14Catalog 7 (⟨197,(1),[3,7,15],[10],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1071 : RecordDataValid section14Catalog 7 (⟨197,(2),[3,7],[11],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1072 : RecordDataValid section14Catalog 7 (⟨197,(2),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1073 : RecordDataValid section14Catalog 7 (⟨197,(3),[3,7],[11],1010⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1010,[3,5,6,7],1014⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1074 : RecordDataValid section14Catalog 7 (⟨197,(3),[3,7,15],[10],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1075 : RecordDataValid section14Catalog 7 (⟨197,(4),[3,7],[11],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1076 : RecordDataValid section14Catalog 7 (⟨197,(4),[3,7,15],[10],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1077 : RecordDataValid section14Catalog 7 (⟨197,(5),[3,7],[11],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1078 : RecordDataValid section14Catalog 7 (⟨197,(5),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1079 : RecordDataValid section14Catalog 7 (⟨197,(6),[3,7],[11],1009⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1009,[3,5,6,7],1013⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1080 : RecordDataValid section14Catalog 7 (⟨197,(6),[3,7,15],[10],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1081 : RecordDataValid section14Catalog 7 (⟨197,(7),[3,7],[11],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1082 : RecordDataValid section14Catalog 7 (⟨197,(7),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1083 : RecordDataValid section14Catalog 7 (⟨197,(8),[3,7],[11],1010⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1010,[3,5,6,7],1014⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1084 : RecordDataValid section14Catalog 7 (⟨197,(8),[3,7,15],[10],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1085 : RecordDataValid section14Catalog 7 (⟨197,(9),[3,7],[11],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1086 : RecordDataValid section14Catalog 7 (⟨197,(9),[3,7,15],[10],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1087 : RecordDataValid section14Catalog 7 (⟨197,(10),[3,7],[11],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1056).take 32 = [⟨195,(4),[7],[10],1590⟩,⟨195,(5),[3,7],[11],700⟩,⟨195,(5),[7],[10],1591⟩,⟨195,(6),[3,7],[11],699⟩,⟨195,(6),[7],[10],1590⟩,⟨195,(7),[3,7],[11],701⟩,⟨195,(7),[7],[10],1592⟩,⟨195,(8),[3,4,7,15,16],[10],702⟩,⟨195,(8),[3,7],[11],702⟩,⟨195,(9),[3,4,7,15,16],[10],703⟩,⟨195,(9),[3,7],[11],703⟩,⟨197,(0),[3,7],[11],1008⟩,⟨197,(0),[3,7,15],[10],453⟩,⟨197,(1),[3,7],[11],1009⟩,⟨197,(1),[3,7,15],[10],454⟩,⟨197,(2),[3,7],[11],1008⟩,⟨197,(2),[3,7,15],[10],453⟩,⟨197,(3),[3,7],[11],1010⟩,⟨197,(3),[3,7,15],[10],455⟩,⟨197,(4),[3,7],[11],1011⟩,⟨197,(4),[3,7,15],[10],456⟩,⟨197,(5),[3,7],[11],1008⟩,⟨197,(5),[3,7,15],[10],453⟩,⟨197,(6),[3,7],[11],1009⟩,⟨197,(6),[3,7,15],[10],454⟩,⟨197,(7),[3,7],[11],1008⟩,⟨197,(7),[3,7,15],[10],453⟩,⟨197,(8),[3,7],[11],1010⟩,⟨197,(8),[3,7,15],[10],455⟩,⟨197,(9),[3,7],[11],1011⟩,⟨197,(9),[3,7,15],[10],456⟩,⟨197,(10),[3,7],[11],1012⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1056
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1057
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1058
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1059
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1060
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1061
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1062
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1063
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1064
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1065
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1066
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1067
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1068
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1069
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1070
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1071
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1072
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1073
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1074
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1075
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1076
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1077
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1078
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1079
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1080
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1081
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1082
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1083
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1084
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1085
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1086
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1087
end Section14Records_7_1056_1088

#print axioms solution
