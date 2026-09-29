-- Prove2me | solution 1 for Freiman.section14_s0008_records_1056_1088
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:15:06.888983+00:00
-- url     : https://prove2.me/submissions/e128f09a-c60f-4ccd-9c92-ac09f97b7464

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
namespace Section14Records_8_1056_1088
private theorem valid1056 : RecordDataValid section14Catalog 8 (⟨146,(6),[4,8,12,16],[10],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1057 : RecordDataValid section14Catalog 8 (⟨146,(7),[4,8,12,16],[10],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1058 : RecordDataValid section14Catalog 8 (⟨146,(8),[4,8,12,16],[10],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1059 : RecordDataValid section14Catalog 8 (⟨146,(9),[4,8,12,16],[10],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1060 : RecordDataValid section14Catalog 8 (⟨146,(10),[4,8,12,16],[10],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1061 : RecordDataValid section14Catalog 8 (⟨146,(11),[4,8,12,16],[10],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1062 : RecordDataValid section14Catalog 8 (⟨146,(12),[4,8,12,16],[10],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1063 : RecordDataValid section14Catalog 8 (⟨146,(13),[4,8,12,16],[10],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1064 : RecordDataValid section14Catalog 8 (⟨146,(14),[4,8,12,16],[10],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1065 : RecordDataValid section14Catalog 8 (⟨146,(15),[4,8,12,16],[10],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1066 : RecordDataValid section14Catalog 8 (⟨150,(0),[4,8,12],[10],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1067 : RecordDataValid section14Catalog 8 (⟨150,(1),[4,8,12],[10],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1068 : RecordDataValid section14Catalog 8 (⟨150,(2),[4,8,12],[10],622⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨622,[1,4,5,6,8,9,10,12],623⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1069 : RecordDataValid section14Catalog 8 (⟨150,(3),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1070 : RecordDataValid section14Catalog 8 (⟨150,(4),[4,8,12],[10],622⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨622,[1,4,5,6,8,9,10,12],623⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1071 : RecordDataValid section14Catalog 8 (⟨150,(5),[4,8,12],[10],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1072 : RecordDataValid section14Catalog 8 (⟨150,(6),[4,8,12],[10],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1073 : RecordDataValid section14Catalog 8 (⟨150,(7),[4,8,12],[10],623⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨623,[1,4,5,6,8,9,10,12],624⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1074 : RecordDataValid section14Catalog 8 (⟨150,(8),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1075 : RecordDataValid section14Catalog 8 (⟨150,(9),[4,8,12],[10],623⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨623,[1,4,5,6,8,9,10,12],624⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1076 : RecordDataValid section14Catalog 8 (⟨150,(10),[4,8,12],[10],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1077 : RecordDataValid section14Catalog 8 (⟨150,(11),[4,8,12],[10],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1078 : RecordDataValid section14Catalog 8 (⟨150,(12),[4,8,12],[10],624⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨624,[1,4,5,6,8,9,10,12],625⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1079 : RecordDataValid section14Catalog 8 (⟨150,(13),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1080 : RecordDataValid section14Catalog 8 (⟨150,(14),[4,8,12],[10],624⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨624,[1,4,5,6,8,9,10,12],625⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1081 : RecordDataValid section14Catalog 8 (⟨150,(15),[4,8,12],[10],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1082 : RecordDataValid section14Catalog 8 (⟨150,(16),[4,8,12],[10],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1083 : RecordDataValid section14Catalog 8 (⟨150,(17),[4,8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1084 : RecordDataValid section14Catalog 8 (⟨150,(18),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1085 : RecordDataValid section14Catalog 8 (⟨150,(19),[4,8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1086 : RecordDataValid section14Catalog 8 (⟨150,(20),[4,8,12],[10],876⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨876,[1,2,4,5,6,8,9,10,12],877⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1087 : RecordDataValid section14Catalog 8 (⟨150,(21),[4,8,12],[10],877⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨877,[1,2,4,5,6,8,9,10,12],878⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1056).take 32 = [⟨146,(6),[4,8,12,16],[10],611⟩,⟨146,(7),[4,8,12,16],[10],612⟩,⟨146,(8),[4,8,12,16],[10],613⟩,⟨146,(9),[4,8,12,16],[10],614⟩,⟨146,(10),[4,8,12,16],[10],615⟩,⟨146,(11),[4,8,12,16],[10],616⟩,⟨146,(12),[4,8,12,16],[10],617⟩,⟨146,(13),[4,8,12,16],[10],618⟩,⟨146,(14),[4,8,12,16],[10],619⟩,⟨146,(15),[4,8,12,16],[10],620⟩,⟨150,(0),[4,8,12],[10],387⟩,⟨150,(1),[4,8,12],[10],621⟩,⟨150,(2),[4,8,12],[10],622⟩,⟨150,(3),[4,8,12],[10],101⟩,⟨150,(4),[4,8,12],[10],622⟩,⟨150,(5),[4,8,12],[10],387⟩,⟨150,(6),[4,8,12],[10],621⟩,⟨150,(7),[4,8,12],[10],623⟩,⟨150,(8),[4,8,12],[10],101⟩,⟨150,(9),[4,8,12],[10],623⟩,⟨150,(10),[4,8,12],[10],387⟩,⟨150,(11),[4,8,12],[10],621⟩,⟨150,(12),[4,8,12],[10],624⟩,⟨150,(13),[4,8,12],[10],101⟩,⟨150,(14),[4,8,12],[10],624⟩,⟨150,(15),[4,8,12],[10],625⟩,⟨150,(16),[4,8,12],[10],626⟩,⟨150,(17),[4,8,12],[10],286⟩,⟨150,(18),[4,8,12],[10],101⟩,⟨150,(19),[4,8,12],[10],286⟩,⟨150,(20),[4,8,12],[10],876⟩,⟨150,(21),[4,8,12],[10],877⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1056
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1057
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1058
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1059
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1060
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1061
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1062
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1063
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1064
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1065
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1066
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1067
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1068
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1069
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1070
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1071
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1072
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1073
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1074
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1075
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1076
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1077
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1078
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1079
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1080
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1081
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1082
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1083
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1084
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1085
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1086
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1087
end Section14Records_8_1056_1088

#print axioms solution
