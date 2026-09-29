-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_1024_1152
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:01:57.841418+00:00
-- url     : https://prove2.me/submissions/455e2695-6093-4bc4-befa-f2b6534d7193

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1024_1056
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1024_1056
private theorem valid1024 : RecordDataValid section14Catalog 1 (⟨28,(8),[1,2],[190],224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨224,[1,2,3],224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1025 : RecordDataValid section14Catalog 1 (⟨28,(8),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1026 : RecordDataValid section14Catalog 1 (⟨28,(8),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1027 : RecordDataValid section14Catalog 1 (⟨28,(8),[1,5],[130],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1028 : RecordDataValid section14Catalog 1 (⟨28,(8),[1,5],[134,135],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1029 : RecordDataValid section14Catalog 1 (⟨28,(9),[1],[146],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1030 : RecordDataValid section14Catalog 1 (⟨28,(9),[1],[151],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1031 : RecordDataValid section14Catalog 1 (⟨28,(9),[1],[147],175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨175,[1,5,9,10],175⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1032 : RecordDataValid section14Catalog 1 (⟨28,(9),[1,2],[190],224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨224,[1,2,3],224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1033 : RecordDataValid section14Catalog 1 (⟨28,(9),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1034 : RecordDataValid section14Catalog 1 (⟨28,(9),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1035 : RecordDataValid section14Catalog 1 (⟨28,(9),[1,5],[130],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1036 : RecordDataValid section14Catalog 1 (⟨28,(9),[1,5],[134,135],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1037 : RecordDataValid section14Catalog 1 (⟨28,(10),[1],[146],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1038 : RecordDataValid section14Catalog 1 (⟨28,(10),[1],[151],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1039 : RecordDataValid section14Catalog 1 (⟨28,(10),[1],[147],176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨176,[1,5,9,10],176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1040 : RecordDataValid section14Catalog 1 (⟨28,(10),[1,2],[190],225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨225,[1,2,3,4],225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1041 : RecordDataValid section14Catalog 1 (⟨28,(10),[1,2,5,6],[131],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1042 : RecordDataValid section14Catalog 1 (⟨28,(10),[1,2,5,6],[150],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1043 : RecordDataValid section14Catalog 1 (⟨28,(10),[1,5],[130],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1044 : RecordDataValid section14Catalog 1 (⟨28,(10),[1,5],[134,135],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1045 : RecordDataValid section14Catalog 1 (⟨28,(11),[1],[146],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1046 : RecordDataValid section14Catalog 1 (⟨28,(11),[1],[151],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1047 : RecordDataValid section14Catalog 1 (⟨28,(11),[1],[147],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1048 : RecordDataValid section14Catalog 1 (⟨28,(11),[1,2],[190],226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨226,[1,2],226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1049 : RecordDataValid section14Catalog 1 (⟨28,(11),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1050 : RecordDataValid section14Catalog 1 (⟨28,(11),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1051 : RecordDataValid section14Catalog 1 (⟨28,(11),[1,5],[130],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1052 : RecordDataValid section14Catalog 1 (⟨28,(11),[1,5],[134,135],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1053 : RecordDataValid section14Catalog 1 (⟨28,(12),[1],[146],89⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨89,[1,5,9],89⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1054 : RecordDataValid section14Catalog 1 (⟨28,(12),[1],[151],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1055 : RecordDataValid section14Catalog 1 (⟨28,(12),[1],[147],178⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨178,[1,5,9,10],178⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1024_1056 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1024).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1024).take 32 = [⟨28,(8),[1,2],[190],224⟩,⟨28,(8),[1,2,5,6],[131],114⟩,⟨28,(8),[1,2,5,6],[150],133⟩,⟨28,(8),[1,5],[130],86⟩,⟨28,(8),[1,5],[134,135],133⟩,⟨28,(9),[1],[146],86⟩,⟨28,(9),[1],[151],133⟩,⟨28,(9),[1],[147],175⟩,⟨28,(9),[1,2],[190],224⟩,⟨28,(9),[1,2,5,6],[131],114⟩,⟨28,(9),[1,2,5,6],[150],133⟩,⟨28,(9),[1,5],[130],86⟩,⟨28,(9),[1,5],[134,135],133⟩,⟨28,(10),[1],[146],87⟩,⟨28,(10),[1],[151],134⟩,⟨28,(10),[1],[147],176⟩,⟨28,(10),[1,2],[190],225⟩,⟨28,(10),[1,2,5,6],[131],115⟩,⟨28,(10),[1,2,5,6],[150],134⟩,⟨28,(10),[1,5],[130],87⟩,⟨28,(10),[1,5],[134,135],134⟩,⟨28,(11),[1],[146],88⟩,⟨28,(11),[1],[151],135⟩,⟨28,(11),[1],[147],177⟩,⟨28,(11),[1,2],[190],226⟩,⟨28,(11),[1,2,5,6],[131],116⟩,⟨28,(11),[1,2,5,6],[150],135⟩,⟨28,(11),[1,5],[130],88⟩,⟨28,(11),[1,5],[134,135],135⟩,⟨28,(12),[1],[146],89⟩,⟨28,(12),[1],[151],136⟩,⟨28,(12),[1],[147],178⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1024
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1025
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1026
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1027
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1028
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1029
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1030
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1031
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1032
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1033
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1034
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1035
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1036
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1037
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1038
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1039
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1040
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1041
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1042
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1043
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1044
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1045
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1046
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1047
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1048
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1049
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1050
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1051
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1052
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1053
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1054
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1055
end Section14Records_1_1024_1056

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1024_1056


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1056_1088
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1056_1088
private theorem valid1056 : RecordDataValid section14Catalog 1 (⟨28,(12),[1,2],[190],227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨227,[1,2,3],227⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1057 : RecordDataValid section14Catalog 1 (⟨28,(12),[1,2,5,6],[131],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1058 : RecordDataValid section14Catalog 1 (⟨28,(12),[1,2,5,6],[150],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1059 : RecordDataValid section14Catalog 1 (⟨28,(12),[1,5],[130],89⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨89,[1,5,9],89⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1060 : RecordDataValid section14Catalog 1 (⟨28,(12),[1,5],[134,135],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1061 : RecordDataValid section14Catalog 1 (⟨28,(13),[1],[146],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1062 : RecordDataValid section14Catalog 1 (⟨28,(13),[1],[151],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1063 : RecordDataValid section14Catalog 1 (⟨28,(13),[1],[147],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1064 : RecordDataValid section14Catalog 1 (⟨28,(13),[1,2],[190],226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨226,[1,2],226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1065 : RecordDataValid section14Catalog 1 (⟨28,(13),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1066 : RecordDataValid section14Catalog 1 (⟨28,(13),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1067 : RecordDataValid section14Catalog 1 (⟨28,(13),[1,5],[130],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1068 : RecordDataValid section14Catalog 1 (⟨28,(13),[1,5],[134,135],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1069 : RecordDataValid section14Catalog 1 (⟨28,(14),[1],[146],90⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨90,[1,5,9],90⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1070 : RecordDataValid section14Catalog 1 (⟨28,(14),[1],[151],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1071 : RecordDataValid section14Catalog 1 (⟨28,(14),[1],[147],179⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨179,[1,5,9,10],179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1072 : RecordDataValid section14Catalog 1 (⟨28,(14),[1,2],[190],228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨228,[1,2],228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1073 : RecordDataValid section14Catalog 1 (⟨28,(14),[1,2,5,6],[131],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1074 : RecordDataValid section14Catalog 1 (⟨28,(14),[1,2,5,6],[150],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1075 : RecordDataValid section14Catalog 1 (⟨28,(14),[1,5],[130],90⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨90,[1,5,9],90⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1076 : RecordDataValid section14Catalog 1 (⟨28,(14),[1,5],[134,135],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1077 : RecordDataValid section14Catalog 1 (⟨28,(15),[1],[146],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1078 : RecordDataValid section14Catalog 1 (⟨28,(15),[1],[151],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1079 : RecordDataValid section14Catalog 1 (⟨28,(15),[1],[147],176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨176,[1,5,9,10],176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1080 : RecordDataValid section14Catalog 1 (⟨28,(15),[1,2],[190],225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨225,[1,2,3,4],225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1081 : RecordDataValid section14Catalog 1 (⟨28,(15),[1,2,5,6],[131],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1082 : RecordDataValid section14Catalog 1 (⟨28,(15),[1,2,5,6],[150],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1083 : RecordDataValid section14Catalog 1 (⟨28,(15),[1,5],[130],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1084 : RecordDataValid section14Catalog 1 (⟨28,(15),[1,5],[134,135],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1085 : RecordDataValid section14Catalog 1 (⟨28,(16),[1],[146],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1086 : RecordDataValid section14Catalog 1 (⟨28,(16),[1],[151],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1087 : RecordDataValid section14Catalog 1 (⟨28,(16),[1],[147],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1056_1088 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1056).take 32 = [⟨28,(12),[1,2],[190],227⟩,⟨28,(12),[1,2,5,6],[131],117⟩,⟨28,(12),[1,2,5,6],[150],136⟩,⟨28,(12),[1,5],[130],89⟩,⟨28,(12),[1,5],[134,135],136⟩,⟨28,(13),[1],[146],88⟩,⟨28,(13),[1],[151],135⟩,⟨28,(13),[1],[147],177⟩,⟨28,(13),[1,2],[190],226⟩,⟨28,(13),[1,2,5,6],[131],116⟩,⟨28,(13),[1,2,5,6],[150],135⟩,⟨28,(13),[1,5],[130],88⟩,⟨28,(13),[1,5],[134,135],135⟩,⟨28,(14),[1],[146],90⟩,⟨28,(14),[1],[151],137⟩,⟨28,(14),[1],[147],179⟩,⟨28,(14),[1,2],[190],228⟩,⟨28,(14),[1,2,5,6],[131],118⟩,⟨28,(14),[1,2,5,6],[150],137⟩,⟨28,(14),[1,5],[130],90⟩,⟨28,(14),[1,5],[134,135],137⟩,⟨28,(15),[1],[146],87⟩,⟨28,(15),[1],[151],134⟩,⟨28,(15),[1],[147],176⟩,⟨28,(15),[1,2],[190],225⟩,⟨28,(15),[1,2,5,6],[131],115⟩,⟨28,(15),[1,2,5,6],[150],134⟩,⟨28,(15),[1,5],[130],87⟩,⟨28,(15),[1,5],[134,135],134⟩,⟨28,(16),[1],[146],91⟩,⟨28,(16),[1],[151],138⟩,⟨28,(16),[1],[147],180⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1056
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1057
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1058
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1059
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1060
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1061
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1062
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1063
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1064
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1065
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1066
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1067
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1068
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1069
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1070
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1071
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1072
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1073
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1074
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1075
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1076
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1077
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1078
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1079
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1080
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1081
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1082
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1083
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1084
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1085
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1086
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1087
end Section14Records_1_1056_1088

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1056_1088


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1088_1120
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1088_1120
private theorem valid1088 : RecordDataValid section14Catalog 1 (⟨28,(16),[1,2],[190],229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨229,[1,2,3],229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1089 : RecordDataValid section14Catalog 1 (⟨28,(16),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1090 : RecordDataValid section14Catalog 1 (⟨28,(16),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1091 : RecordDataValid section14Catalog 1 (⟨28,(16),[1,5],[130],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1092 : RecordDataValid section14Catalog 1 (⟨28,(16),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1093 : RecordDataValid section14Catalog 1 (⟨28,(17),[1],[146],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1094 : RecordDataValid section14Catalog 1 (⟨28,(17),[1],[151],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1095 : RecordDataValid section14Catalog 1 (⟨28,(17),[1],[147],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1096 : RecordDataValid section14Catalog 1 (⟨28,(17),[1,2],[190],229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨229,[1,2,3],229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1097 : RecordDataValid section14Catalog 1 (⟨28,(17),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1098 : RecordDataValid section14Catalog 1 (⟨28,(17),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1099 : RecordDataValid section14Catalog 1 (⟨28,(17),[1,5],[130],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1100 : RecordDataValid section14Catalog 1 (⟨28,(17),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1101 : RecordDataValid section14Catalog 1 (⟨28,(18),[1],[146],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1102 : RecordDataValid section14Catalog 1 (⟨28,(18),[1],[151],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1103 : RecordDataValid section14Catalog 1 (⟨28,(18),[1],[147],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1104 : RecordDataValid section14Catalog 1 (⟨28,(18),[1,2],[190],229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨229,[1,2,3],229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1105 : RecordDataValid section14Catalog 1 (⟨28,(18),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1106 : RecordDataValid section14Catalog 1 (⟨28,(18),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1107 : RecordDataValid section14Catalog 1 (⟨28,(18),[1,5],[130],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1108 : RecordDataValid section14Catalog 1 (⟨28,(18),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1109 : RecordDataValid section14Catalog 1 (⟨28,(19),[1],[146],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1110 : RecordDataValid section14Catalog 1 (⟨28,(19),[1],[151],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1111 : RecordDataValid section14Catalog 1 (⟨28,(19),[1],[147],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1112 : RecordDataValid section14Catalog 1 (⟨28,(19),[1,2],[190],229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨229,[1,2,3],229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1113 : RecordDataValid section14Catalog 1 (⟨28,(19),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1114 : RecordDataValid section14Catalog 1 (⟨28,(19),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1115 : RecordDataValid section14Catalog 1 (⟨28,(19),[1,5],[130],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1116 : RecordDataValid section14Catalog 1 (⟨28,(19),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1117 : RecordDataValid section14Catalog 1 (⟨28,(20),[1],[146],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1118 : RecordDataValid section14Catalog 1 (⟨28,(20),[1],[151],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1119 : RecordDataValid section14Catalog 1 (⟨28,(20),[1],[147],176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨176,[1,5,9,10],176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1088_1120 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1088).take 32 = [⟨28,(16),[1,2],[190],229⟩,⟨28,(16),[1,2,5,6],[131],119⟩,⟨28,(16),[1,2,5,6],[150],138⟩,⟨28,(16),[1,5],[130],91⟩,⟨28,(16),[1,5],[134,135],138⟩,⟨28,(17),[1],[146],91⟩,⟨28,(17),[1],[151],138⟩,⟨28,(17),[1],[147],180⟩,⟨28,(17),[1,2],[190],229⟩,⟨28,(17),[1,2,5,6],[131],119⟩,⟨28,(17),[1,2,5,6],[150],138⟩,⟨28,(17),[1,5],[130],91⟩,⟨28,(17),[1,5],[134,135],138⟩,⟨28,(18),[1],[146],91⟩,⟨28,(18),[1],[151],138⟩,⟨28,(18),[1],[147],180⟩,⟨28,(18),[1,2],[190],229⟩,⟨28,(18),[1,2,5,6],[131],119⟩,⟨28,(18),[1,2,5,6],[150],138⟩,⟨28,(18),[1,5],[130],91⟩,⟨28,(18),[1,5],[134,135],138⟩,⟨28,(19),[1],[146],91⟩,⟨28,(19),[1],[151],138⟩,⟨28,(19),[1],[147],180⟩,⟨28,(19),[1,2],[190],229⟩,⟨28,(19),[1,2,5,6],[131],119⟩,⟨28,(19),[1,2,5,6],[150],138⟩,⟨28,(19),[1,5],[130],91⟩,⟨28,(19),[1,5],[134,135],138⟩,⟨28,(20),[1],[146],87⟩,⟨28,(20),[1],[151],134⟩,⟨28,(20),[1],[147],176⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1088
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1089
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1090
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1091
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1092
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1093
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1094
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1095
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1096
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1097
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1098
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1099
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1100
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1101
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1102
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1103
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1104
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1105
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1106
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1107
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1108
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1109
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1110
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1111
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1112
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1113
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1114
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1115
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1116
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1117
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1118
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1119
end Section14Records_1_1088_1120

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1088_1120


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1120_1152
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1120_1152
private theorem valid1120 : RecordDataValid section14Catalog 1 (⟨28,(20),[1,2],[190],225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨225,[1,2,3,4],225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1121 : RecordDataValid section14Catalog 1 (⟨28,(20),[1,2,5,6],[131],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1122 : RecordDataValid section14Catalog 1 (⟨28,(20),[1,2,5,6],[150],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1123 : RecordDataValid section14Catalog 1 (⟨28,(20),[1,5],[130],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1124 : RecordDataValid section14Catalog 1 (⟨28,(20),[1,5],[134,135],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1125 : RecordDataValid section14Catalog 1 (⟨28,(21),[1],[146],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1126 : RecordDataValid section14Catalog 1 (⟨28,(21),[1],[151],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1127 : RecordDataValid section14Catalog 1 (⟨28,(21),[1],[147],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1128 : RecordDataValid section14Catalog 1 (⟨28,(21),[1,2],[190],226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨226,[1,2],226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1129 : RecordDataValid section14Catalog 1 (⟨28,(21),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1130 : RecordDataValid section14Catalog 1 (⟨28,(21),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1131 : RecordDataValid section14Catalog 1 (⟨28,(21),[1,5],[130],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1132 : RecordDataValid section14Catalog 1 (⟨28,(21),[1,5],[134,135],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1133 : RecordDataValid section14Catalog 1 (⟨28,(22),[1],[146],89⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨89,[1,5,9],89⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1134 : RecordDataValid section14Catalog 1 (⟨28,(22),[1],[151],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1135 : RecordDataValid section14Catalog 1 (⟨28,(22),[1],[147],178⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨178,[1,5,9,10],178⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1136 : RecordDataValid section14Catalog 1 (⟨28,(22),[1,2],[190],227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨227,[1,2,3],227⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1137 : RecordDataValid section14Catalog 1 (⟨28,(22),[1,2,5,6],[131],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1138 : RecordDataValid section14Catalog 1 (⟨28,(22),[1,2,5,6],[150],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1139 : RecordDataValid section14Catalog 1 (⟨28,(22),[1,5],[130],89⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨89,[1,5,9],89⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1140 : RecordDataValid section14Catalog 1 (⟨28,(22),[1,5],[134,135],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1141 : RecordDataValid section14Catalog 1 (⟨28,(23),[1],[146],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1142 : RecordDataValid section14Catalog 1 (⟨28,(23),[1],[151],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1143 : RecordDataValid section14Catalog 1 (⟨28,(23),[1],[147],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1144 : RecordDataValid section14Catalog 1 (⟨28,(23),[1,2],[190],226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨226,[1,2],226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1145 : RecordDataValid section14Catalog 1 (⟨28,(23),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1146 : RecordDataValid section14Catalog 1 (⟨28,(23),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1147 : RecordDataValid section14Catalog 1 (⟨28,(23),[1,5],[130],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1148 : RecordDataValid section14Catalog 1 (⟨28,(23),[1,5],[134,135],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1149 : RecordDataValid section14Catalog 1 (⟨28,(24),[1],[146],90⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨90,[1,5,9],90⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1150 : RecordDataValid section14Catalog 1 (⟨28,(24),[1],[151],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1151 : RecordDataValid section14Catalog 1 (⟨28,(24),[1],[147],179⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨179,[1,5,9,10],179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1120_1152 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1120).take 32 = [⟨28,(20),[1,2],[190],225⟩,⟨28,(20),[1,2,5,6],[131],115⟩,⟨28,(20),[1,2,5,6],[150],134⟩,⟨28,(20),[1,5],[130],87⟩,⟨28,(20),[1,5],[134,135],134⟩,⟨28,(21),[1],[146],88⟩,⟨28,(21),[1],[151],135⟩,⟨28,(21),[1],[147],177⟩,⟨28,(21),[1,2],[190],226⟩,⟨28,(21),[1,2,5,6],[131],116⟩,⟨28,(21),[1,2,5,6],[150],135⟩,⟨28,(21),[1,5],[130],88⟩,⟨28,(21),[1,5],[134,135],135⟩,⟨28,(22),[1],[146],89⟩,⟨28,(22),[1],[151],136⟩,⟨28,(22),[1],[147],178⟩,⟨28,(22),[1,2],[190],227⟩,⟨28,(22),[1,2,5,6],[131],117⟩,⟨28,(22),[1,2,5,6],[150],136⟩,⟨28,(22),[1,5],[130],89⟩,⟨28,(22),[1,5],[134,135],136⟩,⟨28,(23),[1],[146],88⟩,⟨28,(23),[1],[151],135⟩,⟨28,(23),[1],[147],177⟩,⟨28,(23),[1,2],[190],226⟩,⟨28,(23),[1,2,5,6],[131],116⟩,⟨28,(23),[1,2,5,6],[150],135⟩,⟨28,(23),[1,5],[130],88⟩,⟨28,(23),[1,5],[134,135],135⟩,⟨28,(24),[1],[146],90⟩,⟨28,(24),[1],[151],137⟩,⟨28,(24),[1],[147],179⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1120
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1121
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1122
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1123
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1124
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1125
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1126
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1127
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1128
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1129
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1130
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1131
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1132
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1133
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1134
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1135
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1136
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1137
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1138
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1139
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1140
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1141
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1142
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1143
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1144
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1145
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1146
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1147
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1148
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1149
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1150
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1151
end Section14Records_1_1120_1152

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1120_1152

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1024).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 1024 1088 1152 (by decide) (by decide) (all_of_interval_split P xs 1024 1056 1088 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1024_1056 hnum) (Freiman.workReverse20260919_s0001_records_1056_1088 hnum)) (all_of_interval_split P xs 1088 1120 1152 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1088_1120 hnum) (Freiman.workReverse20260919_s0001_records_1120_1152 hnum)))

#print axioms solution
