-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_1024_1152
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:48:23.199863+00:00
-- url     : https://prove2.me/submissions/5d414918-da23-4f0d-8f86-9716c1348fb4

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1024_1056
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1024_1056
private theorem valid1024 : RecordDataValid section14Catalog 6 (⟨47,(24),[1,2,5,6,13,14],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1025 : RecordDataValid section14Catalog 6 (⟨47,(24),[1,2,5,6,13,14],[190],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1026 : RecordDataValid section14Catalog 6 (⟨47,(24),[6],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1027 : RecordDataValid section14Catalog 6 (⟨50,(0),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1028 : RecordDataValid section14Catalog 6 (⟨50,(0),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1029 : RecordDataValid section14Catalog 6 (⟨50,(0),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1030 : RecordDataValid section14Catalog 6 (⟨50,(0),[6],[150],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1031 : RecordDataValid section14Catalog 6 (⟨50,(1),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1032 : RecordDataValid section14Catalog 6 (⟨50,(1),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1033 : RecordDataValid section14Catalog 6 (⟨50,(1),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1034 : RecordDataValid section14Catalog 6 (⟨50,(1),[6],[150],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1035 : RecordDataValid section14Catalog 6 (⟨50,(2),[1,2,5,6],[170],275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨275,[1,2,5,6],276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1036 : RecordDataValid section14Catalog 6 (⟨50,(2),[1,2,5,6],[174],303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨303,[1,2,4,5,6,8,9,10,12],304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1037 : RecordDataValid section14Catalog 6 (⟨50,(2),[1,2,5,6],[190],333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨333,[1,2,4,5,6,8,9,10,12],334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1038 : RecordDataValid section14Catalog 6 (⟨50,(2),[6],[150],333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨333,[1,2,4,5,6,8,9,10,12],334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1039 : RecordDataValid section14Catalog 6 (⟨50,(3),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1040 : RecordDataValid section14Catalog 6 (⟨50,(3),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1041 : RecordDataValid section14Catalog 6 (⟨50,(3),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1042 : RecordDataValid section14Catalog 6 (⟨50,(3),[6],[150],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1043 : RecordDataValid section14Catalog 6 (⟨50,(4),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1044 : RecordDataValid section14Catalog 6 (⟨50,(4),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1045 : RecordDataValid section14Catalog 6 (⟨50,(4),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1046 : RecordDataValid section14Catalog 6 (⟨50,(4),[6],[150],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1047 : RecordDataValid section14Catalog 6 (⟨50,(5),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1048 : RecordDataValid section14Catalog 6 (⟨50,(5),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1049 : RecordDataValid section14Catalog 6 (⟨50,(5),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1050 : RecordDataValid section14Catalog 6 (⟨50,(5),[6],[150],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1051 : RecordDataValid section14Catalog 6 (⟨50,(6),[1,2,5,6],[170],277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨277,[1,2,5,6],278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1052 : RecordDataValid section14Catalog 6 (⟨50,(6),[1,2,5,6],[174],305⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨305,[1,2,4,5,6,8,9,10,12],306⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1053 : RecordDataValid section14Catalog 6 (⟨50,(6),[1,2,5,6],[190],335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨335,[1,2,4,5,6,8,9,10,12],336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1054 : RecordDataValid section14Catalog 6 (⟨50,(6),[6],[150],335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨335,[1,2,4,5,6,8,9,10,12],336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1055 : RecordDataValid section14Catalog 6 (⟨50,(7),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1024_1056 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1024).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1024).take 32 = [⟨47,(24),[1,2,5,6,13,14],[174],300⟩,⟨47,(24),[1,2,5,6,13,14],[190],324⟩,⟨47,(24),[6],[150],199⟩,⟨50,(0),[1,2,5,6],[170],273⟩,⟨50,(0),[1,2,5,6],[174],301⟩,⟨50,(0),[1,2,5,6],[190],331⟩,⟨50,(0),[6],[150],331⟩,⟨50,(1),[1,2,5,6],[170],274⟩,⟨50,(1),[1,2,5,6],[174],302⟩,⟨50,(1),[1,2,5,6],[190],332⟩,⟨50,(1),[6],[150],332⟩,⟨50,(2),[1,2,5,6],[170],275⟩,⟨50,(2),[1,2,5,6],[174],303⟩,⟨50,(2),[1,2,5,6],[190],333⟩,⟨50,(2),[6],[150],333⟩,⟨50,(3),[1,2,5,6],[170],276⟩,⟨50,(3),[1,2,5,6],[174],304⟩,⟨50,(3),[1,2,5,6],[190],334⟩,⟨50,(3),[6],[150],334⟩,⟨50,(4),[1,2,5,6],[170],273⟩,⟨50,(4),[1,2,5,6],[174],301⟩,⟨50,(4),[1,2,5,6],[190],331⟩,⟨50,(4),[6],[150],331⟩,⟨50,(5),[1,2,5,6],[170],274⟩,⟨50,(5),[1,2,5,6],[174],302⟩,⟨50,(5),[1,2,5,6],[190],332⟩,⟨50,(5),[6],[150],332⟩,⟨50,(6),[1,2,5,6],[170],277⟩,⟨50,(6),[1,2,5,6],[174],305⟩,⟨50,(6),[1,2,5,6],[190],335⟩,⟨50,(6),[6],[150],335⟩,⟨50,(7),[1,2,5,6],[170],276⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1024
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1025
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1026
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1027
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1028
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1029
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1030
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1031
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1032
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1033
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1034
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1035
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1036
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1037
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1038
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1039
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1040
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1041
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1042
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1043
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1044
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1045
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1046
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1047
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1048
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1049
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1050
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1051
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1052
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1053
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1054
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1055
end Section14Records_6_1024_1056

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1024_1056


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1056_1088
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1056_1088
private theorem valid1056 : RecordDataValid section14Catalog 6 (⟨50,(7),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1057 : RecordDataValid section14Catalog 6 (⟨50,(7),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1058 : RecordDataValid section14Catalog 6 (⟨50,(7),[6],[150],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1059 : RecordDataValid section14Catalog 6 (⟨50,(8),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1060 : RecordDataValid section14Catalog 6 (⟨50,(8),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1061 : RecordDataValid section14Catalog 6 (⟨50,(8),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1062 : RecordDataValid section14Catalog 6 (⟨50,(8),[6],[150],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1063 : RecordDataValid section14Catalog 6 (⟨50,(9),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1064 : RecordDataValid section14Catalog 6 (⟨50,(9),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1065 : RecordDataValid section14Catalog 6 (⟨50,(9),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1066 : RecordDataValid section14Catalog 6 (⟨50,(9),[6],[150],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1067 : RecordDataValid section14Catalog 6 (⟨50,(10),[1,2,5,6],[170],275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨275,[1,2,5,6],276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1068 : RecordDataValid section14Catalog 6 (⟨50,(10),[1,2,5,6],[174],303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨303,[1,2,4,5,6,8,9,10,12],304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1069 : RecordDataValid section14Catalog 6 (⟨50,(10),[1,2,5,6],[190],333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨333,[1,2,4,5,6,8,9,10,12],334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1070 : RecordDataValid section14Catalog 6 (⟨50,(10),[6],[150],333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨333,[1,2,4,5,6,8,9,10,12],334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1071 : RecordDataValid section14Catalog 6 (⟨50,(11),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1072 : RecordDataValid section14Catalog 6 (⟨50,(11),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1073 : RecordDataValid section14Catalog 6 (⟨50,(11),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1074 : RecordDataValid section14Catalog 6 (⟨50,(11),[6],[150],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1075 : RecordDataValid section14Catalog 6 (⟨50,(12),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1076 : RecordDataValid section14Catalog 6 (⟨50,(12),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1077 : RecordDataValid section14Catalog 6 (⟨50,(12),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1078 : RecordDataValid section14Catalog 6 (⟨50,(12),[6],[150],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1079 : RecordDataValid section14Catalog 6 (⟨50,(13),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1080 : RecordDataValid section14Catalog 6 (⟨50,(13),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1081 : RecordDataValid section14Catalog 6 (⟨50,(13),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1082 : RecordDataValid section14Catalog 6 (⟨50,(13),[6],[150],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1083 : RecordDataValid section14Catalog 6 (⟨50,(14),[1,2,5,6],[170],278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨278,[1,2,5,6],279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1084 : RecordDataValid section14Catalog 6 (⟨50,(14),[1,2,5,6],[174],306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨306,[1,2,4,5,6,8,9,10,12],307⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1085 : RecordDataValid section14Catalog 6 (⟨50,(14),[1,2,5,6],[190],336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨336,[1,2,4,5,6,8,9,10,12],337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1086 : RecordDataValid section14Catalog 6 (⟨50,(14),[6],[150],336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨336,[1,2,4,5,6,8,9,10,12],337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1087 : RecordDataValid section14Catalog 6 (⟨50,(15),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1056_1088 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1056).take 32 = [⟨50,(7),[1,2,5,6],[174],304⟩,⟨50,(7),[1,2,5,6],[190],334⟩,⟨50,(7),[6],[150],334⟩,⟨50,(8),[1,2,5,6],[170],273⟩,⟨50,(8),[1,2,5,6],[174],301⟩,⟨50,(8),[1,2,5,6],[190],331⟩,⟨50,(8),[6],[150],331⟩,⟨50,(9),[1,2,5,6],[170],274⟩,⟨50,(9),[1,2,5,6],[174],302⟩,⟨50,(9),[1,2,5,6],[190],332⟩,⟨50,(9),[6],[150],332⟩,⟨50,(10),[1,2,5,6],[170],275⟩,⟨50,(10),[1,2,5,6],[174],303⟩,⟨50,(10),[1,2,5,6],[190],333⟩,⟨50,(10),[6],[150],333⟩,⟨50,(11),[1,2,5,6],[170],276⟩,⟨50,(11),[1,2,5,6],[174],304⟩,⟨50,(11),[1,2,5,6],[190],334⟩,⟨50,(11),[6],[150],334⟩,⟨50,(12),[1,2,5,6],[170],273⟩,⟨50,(12),[1,2,5,6],[174],301⟩,⟨50,(12),[1,2,5,6],[190],331⟩,⟨50,(12),[6],[150],331⟩,⟨50,(13),[1,2,5,6],[170],274⟩,⟨50,(13),[1,2,5,6],[174],302⟩,⟨50,(13),[1,2,5,6],[190],332⟩,⟨50,(13),[6],[150],332⟩,⟨50,(14),[1,2,5,6],[170],278⟩,⟨50,(14),[1,2,5,6],[174],306⟩,⟨50,(14),[1,2,5,6],[190],336⟩,⟨50,(14),[6],[150],336⟩,⟨50,(15),[1,2,5,6],[170],276⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1056
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1057
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1058
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1059
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1060
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1061
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1062
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1063
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1064
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1065
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1066
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1067
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1068
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1069
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1070
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1071
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1072
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1073
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1074
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1075
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1076
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1077
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1078
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1079
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1080
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1081
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1082
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1083
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1084
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1085
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1086
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1087
end Section14Records_6_1056_1088

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1056_1088


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1088_1120
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1088_1120
private theorem valid1088 : RecordDataValid section14Catalog 6 (⟨50,(15),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1089 : RecordDataValid section14Catalog 6 (⟨50,(15),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1090 : RecordDataValid section14Catalog 6 (⟨50,(15),[6],[150],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1091 : RecordDataValid section14Catalog 6 (⟨53,(0),[1,2,5,6],[170],279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨279,[1,2,3,4,5,6,7,8,9,10,11,12],280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1092 : RecordDataValid section14Catalog 6 (⟨53,(0),[1,2,5,6],[190],325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨325,[1,2,4,5,6,8,9,10,12],326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1093 : RecordDataValid section14Catalog 6 (⟨53,(0),[5,6],[174],279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨279,[1,2,3,4,5,6,7,8,9,10,11,12],280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1094 : RecordDataValid section14Catalog 6 (⟨53,(0),[6],[150],360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨360,[1,2,3,4,5,6,7,8,9,10,12],361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1095 : RecordDataValid section14Catalog 6 (⟨53,(1),[1,2,5,6],[170],280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨280,[1,2,3,4,5,6,7,8,9,10,11,12],281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1096 : RecordDataValid section14Catalog 6 (⟨53,(1),[1,2,5,6],[190],326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨326,[1,2,4,5,6,8,9,10,12],327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1097 : RecordDataValid section14Catalog 6 (⟨53,(1),[6],[174],280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨280,[1,2,3,4,5,6,7,8,9,10,11,12],281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1098 : RecordDataValid section14Catalog 6 (⟨53,(1),[6],[150],361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨361,[1,2,3,4,5,6,7,8,9,10,12],362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1099 : RecordDataValid section14Catalog 6 (⟨53,(2),[1,2,5,6],[170],281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨281,[1,2,3,4,5,6,7,8,9,10,11,12],282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1100 : RecordDataValid section14Catalog 6 (⟨53,(2),[1,2,5,6],[174],309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨309,[1,2,3,5,6,7],310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1101 : RecordDataValid section14Catalog 6 (⟨53,(2),[1,2,5,6],[190],327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨327,[1,2,4,5,6,8,9,10,12],328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1102 : RecordDataValid section14Catalog 6 (⟨53,(2),[6],[150],362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨362,[1,2,3,4,5,6,7,8,9,10,12],363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1103 : RecordDataValid section14Catalog 6 (⟨53,(3),[1,2,5,6],[170],282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨282,[1,2,3,4,5,6,7,8,9,10,11,12],283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1104 : RecordDataValid section14Catalog 6 (⟨53,(3),[1,2,5,6],[190],328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨328,[1,2,4,5,6,8,9,10,12],329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1105 : RecordDataValid section14Catalog 6 (⟨53,(3),[6],[174],282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨282,[1,2,3,4,5,6,7,8,9,10,11,12],283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1106 : RecordDataValid section14Catalog 6 (⟨53,(3),[6],[150],363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨363,[1,2,3,4,5,6,7,8,9,10,12],364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1107 : RecordDataValid section14Catalog 6 (⟨55,(0),[1,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1108 : RecordDataValid section14Catalog 6 (⟨55,(0),[2,6,13,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1109 : RecordDataValid section14Catalog 6 (⟨55,(0),[6],[150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1110 : RecordDataValid section14Catalog 6 (⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1111 : RecordDataValid section14Catalog 6 (⟨55,(1),[6],[150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1112 : RecordDataValid section14Catalog 6 (⟨55,(2),[1,2,5,6,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1113 : RecordDataValid section14Catalog 6 (⟨55,(2),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1114 : RecordDataValid section14Catalog 6 (⟨55,(2),[6,13],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1115 : RecordDataValid section14Catalog 6 (⟨55,(3),[1,2,5,6,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1116 : RecordDataValid section14Catalog 6 (⟨55,(3),[1,6,13],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1117 : RecordDataValid section14Catalog 6 (⟨55,(3),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1118 : RecordDataValid section14Catalog 6 (⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1119 : RecordDataValid section14Catalog 6 (⟨55,(4),[6],[150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1088_1120 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1088).take 32 = [⟨50,(15),[1,2,5,6],[174],304⟩,⟨50,(15),[1,2,5,6],[190],334⟩,⟨50,(15),[6],[150],334⟩,⟨53,(0),[1,2,5,6],[170],279⟩,⟨53,(0),[1,2,5,6],[190],325⟩,⟨53,(0),[5,6],[174],279⟩,⟨53,(0),[6],[150],360⟩,⟨53,(1),[1,2,5,6],[170],280⟩,⟨53,(1),[1,2,5,6],[190],326⟩,⟨53,(1),[6],[174],280⟩,⟨53,(1),[6],[150],361⟩,⟨53,(2),[1,2,5,6],[170],281⟩,⟨53,(2),[1,2,5,6],[174],309⟩,⟨53,(2),[1,2,5,6],[190],327⟩,⟨53,(2),[6],[150],362⟩,⟨53,(3),[1,2,5,6],[170],282⟩,⟨53,(3),[1,2,5,6],[190],328⟩,⟨53,(3),[6],[174],282⟩,⟨53,(3),[6],[150],363⟩,⟨55,(0),[1,5,6,13,14],[190],3⟩,⟨55,(0),[2,6,13,14],[170,174],97⟩,⟨55,(0),[6],[150],98⟩,⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(1),[6],[150],159⟩,⟨55,(2),[1,2,5,6,14],[170,174],97⟩,⟨55,(2),[6],[150],3⟩,⟨55,(2),[6,13],[190],2⟩,⟨55,(3),[1,2,5,6,14],[190],234⟩,⟨55,(3),[1,6,13],[170,174],2⟩,⟨55,(3),[6],[150],3⟩,⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(4),[6],[150],98⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1088
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1089
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1090
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1091
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1092
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1093
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1094
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1095
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1096
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1097
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1098
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1099
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1100
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1101
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1102
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1103
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1104
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1105
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1106
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1107
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1108
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1109
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1110
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1111
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1112
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1113
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1114
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1115
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1116
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1117
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1118
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1119
end Section14Records_6_1088_1120

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1088_1120


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1120_1152
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1120_1152
private theorem valid1120 : RecordDataValid section14Catalog 6 (⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1121 : RecordDataValid section14Catalog 6 (⟨55,(5),[6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1122 : RecordDataValid section14Catalog 6 (⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1123 : RecordDataValid section14Catalog 6 (⟨55,(6),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1124 : RecordDataValid section14Catalog 6 (⟨55,(6),[6,13],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1125 : RecordDataValid section14Catalog 6 (⟨55,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1126 : RecordDataValid section14Catalog 6 (⟨55,(7),[1,6,13],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1127 : RecordDataValid section14Catalog 6 (⟨55,(7),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1128 : RecordDataValid section14Catalog 6 (⟨55,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1129 : RecordDataValid section14Catalog 6 (⟨55,(8),[5,6,13,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1130 : RecordDataValid section14Catalog 6 (⟨55,(8),[6],[150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1131 : RecordDataValid section14Catalog 6 (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1132 : RecordDataValid section14Catalog 6 (⟨55,(9),[6],[150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1133 : RecordDataValid section14Catalog 6 (⟨55,(10),[1,2,5,6,13,14],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1134 : RecordDataValid section14Catalog 6 (⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1135 : RecordDataValid section14Catalog 6 (⟨55,(10),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1136 : RecordDataValid section14Catalog 6 (⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1137 : RecordDataValid section14Catalog 6 (⟨55,(11),[1,2,5,6,13,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1138 : RecordDataValid section14Catalog 6 (⟨55,(11),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1139 : RecordDataValid section14Catalog 6 (⟨55,(12),[5,6,13],[170,174,190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1140 : RecordDataValid section14Catalog 6 (⟨55,(12),[6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1141 : RecordDataValid section14Catalog 6 (⟨55,(13),[5,6,13],[170,174,190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1142 : RecordDataValid section14Catalog 6 (⟨55,(13),[6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1143 : RecordDataValid section14Catalog 6 (⟨55,(14),[1,2,5,6,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1144 : RecordDataValid section14Catalog 6 (⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1145 : RecordDataValid section14Catalog 6 (⟨55,(14),[6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1146 : RecordDataValid section14Catalog 6 (⟨55,(15),[1,2,5,6,13],[170,174],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1147 : RecordDataValid section14Catalog 6 (⟨55,(15),[1,2,5,6,13,14],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1148 : RecordDataValid section14Catalog 6 (⟨55,(15),[6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1149 : RecordDataValid section14Catalog 6 (⟨57,(0),[1,2,5,6],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1150 : RecordDataValid section14Catalog 6 (⟨57,(0),[6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1151 : RecordDataValid section14Catalog 6 (⟨57,(1),[1,2,5,6],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1120_1152 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1120).take 32 = [⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(5),[6],[150],2⟩,⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩,⟨55,(6),[6],[150],3⟩,⟨55,(6),[6,13],[190],2⟩,⟨55,(7),[1,2,5,6,13,14],[190],2⟩,⟨55,(7),[1,6,13],[170,174],2⟩,⟨55,(7),[6],[150],3⟩,⟨55,(8),[1,2,5,6,13,14],[190],3⟩,⟨55,(8),[5,6,13,14],[170,174],97⟩,⟨55,(8),[6],[150],98⟩,⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩,⟨55,(9),[6],[150],159⟩,⟨55,(10),[1,2,5,6,13,14],[190],29⟩,⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩,⟨55,(10),[6],[150],3⟩,⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩,⟨55,(11),[1,2,5,6,13,14],[190],234⟩,⟨55,(11),[6],[150],3⟩,⟨55,(12),[5,6,13],[170,174,190],99⟩,⟨55,(12),[6],[150],99⟩,⟨55,(13),[5,6,13],[170,174,190],99⟩,⟨55,(13),[6],[150],99⟩,⟨55,(14),[1,2,5,6,13],[190],99⟩,⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩,⟨55,(14),[6],[150],99⟩,⟨55,(15),[1,2,5,6,13],[170,174],99⟩,⟨55,(15),[1,2,5,6,13,14],[190],99⟩,⟨55,(15),[6],[150],99⟩,⟨57,(0),[1,2,5,6],[170,174,190],2⟩,⟨57,(0),[6],[150],2⟩,⟨57,(1),[1,2,5,6],[170,174,190],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1120
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1121
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1122
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1123
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1124
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1125
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1126
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1127
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1128
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1129
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1130
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1131
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1132
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1133
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1134
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1135
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1136
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1137
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1138
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1139
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1140
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1141
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1142
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1143
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1144
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1145
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1146
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1147
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1148
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1149
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1150
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1151
end Section14Records_6_1120_1152

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1120_1152

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1024).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 1024 1088 1152 (by decide) (by decide) (all_of_interval_split P xs 1024 1056 1088 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1024_1056 hnum) (Freiman.workReverse20260919_s0006_records_1056_1088 hnum)) (all_of_interval_split P xs 1088 1120 1152 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1088_1120 hnum) (Freiman.workReverse20260919_s0006_records_1120_1152 hnum)))

#print axioms solution
