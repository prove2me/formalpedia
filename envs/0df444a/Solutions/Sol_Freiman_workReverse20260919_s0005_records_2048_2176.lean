-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_2048_2176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:14:11.520993+00:00
-- url     : https://prove2.me/submissions/8a609510-93e6-49c4-bb64-f22d5c2851a5

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2048_2080
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2048_2080
private theorem valid2048 : RecordDataValid section14Catalog 5 (⟨106,(4),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2049 : RecordDataValid section14Catalog 5 (⟨106,(5),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2050 : RecordDataValid section14Catalog 5 (⟨106,(6),[1,5,6,13],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2051 : RecordDataValid section14Catalog 5 (⟨106,(7),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2052 : RecordDataValid section14Catalog 5 (⟨106,(8),[1,5,6,13],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2053 : RecordDataValid section14Catalog 5 (⟨106,(9),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2054 : RecordDataValid section14Catalog 5 (⟨106,(10),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2055 : RecordDataValid section14Catalog 5 (⟨106,(11),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2056 : RecordDataValid section14Catalog 5 (⟨106,(12),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2057 : RecordDataValid section14Catalog 5 (⟨106,(13),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2058 : RecordDataValid section14Catalog 5 (⟨106,(14),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2059 : RecordDataValid section14Catalog 5 (⟨106,(15),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2060 : RecordDataValid section14Catalog 5 (⟨106,(16),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2061 : RecordDataValid section14Catalog 5 (⟨106,(17),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2062 : RecordDataValid section14Catalog 5 (⟨106,(18),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2063 : RecordDataValid section14Catalog 5 (⟨106,(19),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2064 : RecordDataValid section14Catalog 5 (⟨106,(20),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2065 : RecordDataValid section14Catalog 5 (⟨106,(21),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2066 : RecordDataValid section14Catalog 5 (⟨106,(22),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2067 : RecordDataValid section14Catalog 5 (⟨106,(23),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2068 : RecordDataValid section14Catalog 5 (⟨106,(24),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2069 : RecordDataValid section14Catalog 5 (⟨109,(0),[1,5,6,13],[170],448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨448,[1,4,5,6,8,9,10,12,13,16],449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2070 : RecordDataValid section14Catalog 5 (⟨109,(1),[1,5,6,13],[170],448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨448,[1,4,5,6,8,9,10,12,13,16],449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2071 : RecordDataValid section14Catalog 5 (⟨109,(2),[1,5,6,13],[170],449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨449,[1,4,5,6,8,9,10,12,13,16],450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2072 : RecordDataValid section14Catalog 5 (⟨109,(3),[1,5,6,13],[170],449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨449,[1,4,5,6,8,9,10,12,13,16],450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2073 : RecordDataValid section14Catalog 5 (⟨109,(4),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2074 : RecordDataValid section14Catalog 5 (⟨109,(5),[1,5,6,13],[170],451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨451,[1,4,5,6,8,9,10,12,13,16],452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2075 : RecordDataValid section14Catalog 5 (⟨109,(6),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2076 : RecordDataValid section14Catalog 5 (⟨109,(7),[1,5,6,13],[170],452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨452,[1,4,5,6,8,9,10,12,13,16],453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2077 : RecordDataValid section14Catalog 5 (⟨109,(8),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2078 : RecordDataValid section14Catalog 5 (⟨109,(9),[1,5,6,13],[170],451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨451,[1,4,5,6,8,9,10,12,13,16],452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2079 : RecordDataValid section14Catalog 5 (⟨111,(0),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2048_2080 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2048).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2048).take 32 = [⟨106,(4),[1,5,6,13],[170],444⟩,⟨106,(5),[1,5,6,13],[170],441⟩,⟨106,(6),[1,5,6,13],[170],442⟩,⟨106,(7),[1,5,6,13],[170],441⟩,⟨106,(8),[1,5,6,13],[170],443⟩,⟨106,(9),[1,5,6,13],[170],444⟩,⟨106,(10),[1,5,6,13],[170],445⟩,⟨106,(11),[1,5,6,13],[170],445⟩,⟨106,(12),[1,5,6,13],[170],445⟩,⟨106,(13),[1,5,6,13],[170],445⟩,⟨106,(14),[1,5,6,13],[170],444⟩,⟨106,(15),[1,5,6,13],[170],446⟩,⟨106,(16),[1,5,6,13],[170],446⟩,⟨106,(17),[1,5,6,13],[170],446⟩,⟨106,(18),[1,5,6,13],[170],446⟩,⟨106,(19),[1,5,6,13],[170],446⟩,⟨106,(20),[1,5,6,13],[170],447⟩,⟨106,(21),[1,5,6,13],[170],447⟩,⟨106,(22),[1,5,6,13],[170],447⟩,⟨106,(23),[1,5,6,13],[170],447⟩,⟨106,(24),[1,5,6,13],[170],447⟩,⟨109,(0),[1,5,6,13],[170],448⟩,⟨109,(1),[1,5,6,13],[170],448⟩,⟨109,(2),[1,5,6,13],[170],449⟩,⟨109,(3),[1,5,6,13],[170],449⟩,⟨109,(4),[1,5,6,13],[170],450⟩,⟨109,(5),[1,5,6,13],[170],451⟩,⟨109,(6),[1,5,6,13],[170],450⟩,⟨109,(7),[1,5,6,13],[170],452⟩,⟨109,(8),[1,5,6,13],[170],450⟩,⟨109,(9),[1,5,6,13],[170],451⟩,⟨111,(0),[1,5,6,13],[170],453⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2048
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2049
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2050
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2051
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2052
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2053
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2054
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2055
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2056
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2057
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2058
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2059
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2060
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2061
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2062
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2063
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2064
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2065
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2066
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2067
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2068
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2069
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2070
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2071
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2072
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2073
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2074
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2075
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2076
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2077
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2078
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2079
end Section14Records_5_2048_2080

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2048_2080


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2080_2112
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2080_2112
private theorem valid2080 : RecordDataValid section14Catalog 5 (⟨111,(1),[1,5,6,13],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2081 : RecordDataValid section14Catalog 5 (⟨111,(2),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2082 : RecordDataValid section14Catalog 5 (⟨111,(3),[1,5,6,13],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2083 : RecordDataValid section14Catalog 5 (⟨111,(4),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2084 : RecordDataValid section14Catalog 5 (⟨111,(5),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2085 : RecordDataValid section14Catalog 5 (⟨111,(6),[1,5,6,13],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2086 : RecordDataValid section14Catalog 5 (⟨111,(7),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2087 : RecordDataValid section14Catalog 5 (⟨111,(8),[1,5,6,13],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2088 : RecordDataValid section14Catalog 5 (⟨111,(9),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2089 : RecordDataValid section14Catalog 5 (⟨111,(10),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2090 : RecordDataValid section14Catalog 5 (⟨111,(11),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2091 : RecordDataValid section14Catalog 5 (⟨111,(12),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2092 : RecordDataValid section14Catalog 5 (⟨111,(13),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2093 : RecordDataValid section14Catalog 5 (⟨111,(14),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2094 : RecordDataValid section14Catalog 5 (⟨111,(15),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2095 : RecordDataValid section14Catalog 5 (⟨111,(16),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2096 : RecordDataValid section14Catalog 5 (⟨111,(17),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2097 : RecordDataValid section14Catalog 5 (⟨111,(18),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2098 : RecordDataValid section14Catalog 5 (⟨111,(19),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2099 : RecordDataValid section14Catalog 5 (⟨111,(20),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2100 : RecordDataValid section14Catalog 5 (⟨111,(21),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2101 : RecordDataValid section14Catalog 5 (⟨111,(22),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2102 : RecordDataValid section14Catalog 5 (⟨111,(23),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2103 : RecordDataValid section14Catalog 5 (⟨111,(24),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2104 : RecordDataValid section14Catalog 5 (⟨114,(0),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2105 : RecordDataValid section14Catalog 5 (⟨114,(1),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2106 : RecordDataValid section14Catalog 5 (⟨114,(2),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2107 : RecordDataValid section14Catalog 5 (⟨114,(3),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2108 : RecordDataValid section14Catalog 5 (⟨114,(4),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2109 : RecordDataValid section14Catalog 5 (⟨114,(5),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2110 : RecordDataValid section14Catalog 5 (⟨114,(6),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2111 : RecordDataValid section14Catalog 5 (⟨114,(7),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2080_2112 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2080).take 32 = [⟨111,(1),[1,5,6,13],[170],454⟩,⟨111,(2),[1,5,6,13],[170],453⟩,⟨111,(3),[1,5,6,13],[170],455⟩,⟨111,(4),[1,5,6,13],[170],456⟩,⟨111,(5),[1,5,6,13],[170],453⟩,⟨111,(6),[1,5,6,13],[170],454⟩,⟨111,(7),[1,5,6,13],[170],453⟩,⟨111,(8),[1,5,6,13],[170],455⟩,⟨111,(9),[1,5,6,13],[170],456⟩,⟨111,(10),[1,5,6,13],[170],457⟩,⟨111,(11),[1,5,6,13],[170],457⟩,⟨111,(12),[1,5,6,13],[170],457⟩,⟨111,(13),[1,5,6,13],[170],457⟩,⟨111,(14),[1,5,6,13],[170],456⟩,⟨111,(15),[1,5,6,13],[170],458⟩,⟨111,(16),[1,5,6,13],[170],458⟩,⟨111,(17),[1,5,6,13],[170],458⟩,⟨111,(18),[1,5,6,13],[170],458⟩,⟨111,(19),[1,5,6,13],[170],458⟩,⟨111,(20),[1,5,6,13],[170],459⟩,⟨111,(21),[1,5,6,13],[170],459⟩,⟨111,(22),[1,5,6,13],[170],459⟩,⟨111,(23),[1,5,6,13],[170],459⟩,⟨111,(24),[1,5,6,13],[170],459⟩,⟨114,(0),[1,5,6,13],[170],460⟩,⟨114,(1),[1,5,6,13],[170],460⟩,⟨114,(2),[1,5,6,13],[170],460⟩,⟨114,(3),[1,5,6,13],[170],460⟩,⟨114,(4),[1,5,6,13],[170],460⟩,⟨114,(5),[1,5,6,13],[170],461⟩,⟨114,(6),[1,5,6,13],[170],461⟩,⟨114,(7),[1,5,6,13],[170],461⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2080
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2081
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2082
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2083
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2084
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2085
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2086
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2087
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2088
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2089
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2090
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2091
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2092
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2093
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2094
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2095
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2096
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2097
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2098
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2099
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2100
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2101
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2102
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2103
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2104
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2105
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2106
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2107
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2108
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2109
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2110
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2111
end Section14Records_5_2080_2112

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2080_2112


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2112_2144
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2112_2144
private theorem valid2112 : RecordDataValid section14Catalog 5 (⟨114,(8),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2113 : RecordDataValid section14Catalog 5 (⟨114,(9),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2114 : RecordDataValid section14Catalog 5 (⟨114,(10),[1,5,6,13],[170],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2115 : RecordDataValid section14Catalog 5 (⟨114,(11),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2116 : RecordDataValid section14Catalog 5 (⟨114,(12),[1,5,6,13],[170],464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2117 : RecordDataValid section14Catalog 5 (⟨114,(13),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2118 : RecordDataValid section14Catalog 5 (⟨114,(14),[1,5,6,13],[170],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2119 : RecordDataValid section14Catalog 5 (⟨114,(15),[1,5,6,13],[170],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2120 : RecordDataValid section14Catalog 5 (⟨114,(16),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2121 : RecordDataValid section14Catalog 5 (⟨114,(17),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2122 : RecordDataValid section14Catalog 5 (⟨114,(18),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2123 : RecordDataValid section14Catalog 5 (⟨114,(19),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2124 : RecordDataValid section14Catalog 5 (⟨114,(20),[1,5,6,13],[170],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2125 : RecordDataValid section14Catalog 5 (⟨114,(21),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2126 : RecordDataValid section14Catalog 5 (⟨114,(22),[1,5,6,13],[170],464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2127 : RecordDataValid section14Catalog 5 (⟨114,(23),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2128 : RecordDataValid section14Catalog 5 (⟨114,(24),[1,5,6,13],[170],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2129 : RecordDataValid section14Catalog 5 (⟨116,(0),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2130 : RecordDataValid section14Catalog 5 (⟨116,(1),[1,5,6,13],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2131 : RecordDataValid section14Catalog 5 (⟨116,(2),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2132 : RecordDataValid section14Catalog 5 (⟨116,(3),[1,5,6,13],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2133 : RecordDataValid section14Catalog 5 (⟨116,(4),[1,5,6,13],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2134 : RecordDataValid section14Catalog 5 (⟨116,(5),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2135 : RecordDataValid section14Catalog 5 (⟨116,(6),[1,5,6,13],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2136 : RecordDataValid section14Catalog 5 (⟨116,(7),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2137 : RecordDataValid section14Catalog 5 (⟨116,(8),[1,5,6,13],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2138 : RecordDataValid section14Catalog 5 (⟨116,(9),[1,5,6,13],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2139 : RecordDataValid section14Catalog 5 (⟨116,(10),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2140 : RecordDataValid section14Catalog 5 (⟨116,(11),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2141 : RecordDataValid section14Catalog 5 (⟨116,(12),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2142 : RecordDataValid section14Catalog 5 (⟨116,(13),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2143 : RecordDataValid section14Catalog 5 (⟨116,(14),[1,5,6,13],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2112_2144 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2112).take 32 = [⟨114,(8),[1,5,6,13],[170],461⟩,⟨114,(9),[1,5,6,13],[170],461⟩,⟨114,(10),[1,5,6,13],[170],462⟩,⟨114,(11),[1,5,6,13],[170],463⟩,⟨114,(12),[1,5,6,13],[170],464⟩,⟨114,(13),[1,5,6,13],[170],463⟩,⟨114,(14),[1,5,6,13],[170],465⟩,⟨114,(15),[1,5,6,13],[170],462⟩,⟨114,(16),[1,5,6,13],[170],466⟩,⟨114,(17),[1,5,6,13],[170],466⟩,⟨114,(18),[1,5,6,13],[170],466⟩,⟨114,(19),[1,5,6,13],[170],466⟩,⟨114,(20),[1,5,6,13],[170],462⟩,⟨114,(21),[1,5,6,13],[170],463⟩,⟨114,(22),[1,5,6,13],[170],464⟩,⟨114,(23),[1,5,6,13],[170],463⟩,⟨114,(24),[1,5,6,13],[170],465⟩,⟨116,(0),[1,5,6,13],[170],467⟩,⟨116,(1),[1,5,6,13],[170],468⟩,⟨116,(2),[1,5,6,13],[170],467⟩,⟨116,(3),[1,5,6,13],[170],469⟩,⟨116,(4),[1,5,6,13],[170],470⟩,⟨116,(5),[1,5,6,13],[170],467⟩,⟨116,(6),[1,5,6,13],[170],468⟩,⟨116,(7),[1,5,6,13],[170],467⟩,⟨116,(8),[1,5,6,13],[170],469⟩,⟨116,(9),[1,5,6,13],[170],470⟩,⟨116,(10),[1,5,6,13],[170],471⟩,⟨116,(11),[1,5,6,13],[170],471⟩,⟨116,(12),[1,5,6,13],[170],471⟩,⟨116,(13),[1,5,6,13],[170],471⟩,⟨116,(14),[1,5,6,13],[170],470⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2112
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2113
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2114
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2115
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2116
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2117
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2118
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2119
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2120
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2121
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2122
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2123
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2124
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2125
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2126
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2127
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2128
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2129
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2130
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2131
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2132
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2133
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2134
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2135
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2136
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2137
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2138
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2139
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2140
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2141
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2142
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2143
end Section14Records_5_2112_2144

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2112_2144


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2144_2176
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2144_2176
private theorem valid2144 : RecordDataValid section14Catalog 5 (⟨116,(15),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2145 : RecordDataValid section14Catalog 5 (⟨116,(16),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2146 : RecordDataValid section14Catalog 5 (⟨116,(17),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2147 : RecordDataValid section14Catalog 5 (⟨116,(18),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2148 : RecordDataValid section14Catalog 5 (⟨116,(19),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2149 : RecordDataValid section14Catalog 5 (⟨116,(20),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2150 : RecordDataValid section14Catalog 5 (⟨116,(21),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2151 : RecordDataValid section14Catalog 5 (⟨116,(22),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2152 : RecordDataValid section14Catalog 5 (⟨116,(23),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2153 : RecordDataValid section14Catalog 5 (⟨116,(24),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2154 : RecordDataValid section14Catalog 5 (⟨119,(0),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2155 : RecordDataValid section14Catalog 5 (⟨119,(1),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2156 : RecordDataValid section14Catalog 5 (⟨119,(2),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2157 : RecordDataValid section14Catalog 5 (⟨119,(3),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2158 : RecordDataValid section14Catalog 5 (⟨119,(4),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2159 : RecordDataValid section14Catalog 5 (⟨119,(5),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2160 : RecordDataValid section14Catalog 5 (⟨119,(6),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2161 : RecordDataValid section14Catalog 5 (⟨119,(7),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2162 : RecordDataValid section14Catalog 5 (⟨119,(8),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2163 : RecordDataValid section14Catalog 5 (⟨119,(9),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2164 : RecordDataValid section14Catalog 5 (⟨119,(10),[1,5,6,13],[170],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2165 : RecordDataValid section14Catalog 5 (⟨119,(11),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2166 : RecordDataValid section14Catalog 5 (⟨119,(12),[1,5,6,13],[170],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2167 : RecordDataValid section14Catalog 5 (⟨119,(13),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2168 : RecordDataValid section14Catalog 5 (⟨119,(14),[1,5,6,13],[170],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2169 : RecordDataValid section14Catalog 5 (⟨119,(15),[1,5,6,13],[170],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2170 : RecordDataValid section14Catalog 5 (⟨119,(16),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2171 : RecordDataValid section14Catalog 5 (⟨119,(17),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2172 : RecordDataValid section14Catalog 5 (⟨119,(18),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2173 : RecordDataValid section14Catalog 5 (⟨119,(19),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2174 : RecordDataValid section14Catalog 5 (⟨119,(20),[1,5,6,13],[170],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2175 : RecordDataValid section14Catalog 5 (⟨119,(21),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2144_2176 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2144).take 32 = [⟨116,(15),[1,5,6,13],[170],472⟩,⟨116,(16),[1,5,6,13],[170],472⟩,⟨116,(17),[1,5,6,13],[170],472⟩,⟨116,(18),[1,5,6,13],[170],472⟩,⟨116,(19),[1,5,6,13],[170],472⟩,⟨116,(20),[1,5,6,13],[170],473⟩,⟨116,(21),[1,5,6,13],[170],473⟩,⟨116,(22),[1,5,6,13],[170],473⟩,⟨116,(23),[1,5,6,13],[170],473⟩,⟨116,(24),[1,5,6,13],[170],473⟩,⟨119,(0),[1,5,6,13],[170],474⟩,⟨119,(1),[1,5,6,13],[170],474⟩,⟨119,(2),[1,5,6,13],[170],474⟩,⟨119,(3),[1,5,6,13],[170],474⟩,⟨119,(4),[1,5,6,13],[170],474⟩,⟨119,(5),[1,5,6,13],[170],475⟩,⟨119,(6),[1,5,6,13],[170],475⟩,⟨119,(7),[1,5,6,13],[170],475⟩,⟨119,(8),[1,5,6,13],[170],475⟩,⟨119,(9),[1,5,6,13],[170],475⟩,⟨119,(10),[1,5,6,13],[170],476⟩,⟨119,(11),[1,5,6,13],[170],477⟩,⟨119,(12),[1,5,6,13],[170],478⟩,⟨119,(13),[1,5,6,13],[170],477⟩,⟨119,(14),[1,5,6,13],[170],479⟩,⟨119,(15),[1,5,6,13],[170],476⟩,⟨119,(16),[1,5,6,13],[170],480⟩,⟨119,(17),[1,5,6,13],[170],480⟩,⟨119,(18),[1,5,6,13],[170],480⟩,⟨119,(19),[1,5,6,13],[170],480⟩,⟨119,(20),[1,5,6,13],[170],476⟩,⟨119,(21),[1,5,6,13],[170],477⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2144
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2145
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2146
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2147
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2148
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2149
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2150
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2151
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2152
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2153
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2154
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2155
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2156
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2157
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2158
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2159
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2160
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2161
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2162
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2163
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2164
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2165
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2166
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2167
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2168
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2169
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2170
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2171
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2172
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2173
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2174
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2175
end Section14Records_5_2144_2176

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2144_2176

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2048).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 2048 2112 2176 (by decide) (by decide) (all_of_interval_split P xs 2048 2080 2112 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2048_2080 hnum) (Freiman.workReverse20260919_s0005_records_2080_2112 hnum)) (all_of_interval_split P xs 2112 2144 2176 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2112_2144 hnum) (Freiman.workReverse20260919_s0005_records_2144_2176 hnum)))

#print axioms solution
