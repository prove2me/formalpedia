-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_0928_0960
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:17:30.722443+00:00
-- url     : https://prove2.me/submissions/095e241e-592b-44f6-81da-75afea5f7e0b

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
namespace Section14Records_13_928_960
private theorem valid928 : RecordDataValid section14Catalog 13 (⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid929 : RecordDataValid section14Catalog 13 (⟨40,(24),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid930 : RecordDataValid section14Catalog 13 (⟨42,(0),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid931 : RecordDataValid section14Catalog 13 (⟨42,(0),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid932 : RecordDataValid section14Catalog 13 (⟨42,(0),[1,2,5,6,13,14],[190],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid933 : RecordDataValid section14Catalog 13 (⟨42,(0),[1,5,13],[186],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid934 : RecordDataValid section14Catalog 13 (⟨42,(1),[1,2,5,6,13,14],[170],254⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨254,[1,2,3,4,5,6,7,8,13,14,15,16],255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid935 : RecordDataValid section14Catalog 13 (⟨42,(1),[1,2,5,6,13,14],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid936 : RecordDataValid section14Catalog 13 (⟨42,(1),[1,2,5,6,13,14],[190],313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨313,[1,2,4,5,6,8,13,14,16],314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid937 : RecordDataValid section14Catalog 13 (⟨42,(1),[1,5,13],[186],313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨313,[1,2,4,5,6,8,13,14,16],314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid938 : RecordDataValid section14Catalog 13 (⟨42,(2),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid939 : RecordDataValid section14Catalog 13 (⟨42,(2),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid940 : RecordDataValid section14Catalog 13 (⟨42,(2),[1,2,5,6,13,14],[190],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid941 : RecordDataValid section14Catalog 13 (⟨42,(2),[1,5,13],[186],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid942 : RecordDataValid section14Catalog 13 (⟨42,(3),[1,2,5,6,13,14],[170],255⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨255,[1,2,3,4,5,6,7,8,13,14,15,16],256⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid943 : RecordDataValid section14Catalog 13 (⟨42,(3),[1,2,5,6,13,14],[174],290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨290,[1,2,3,5,6,7,13,14,15],291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid944 : RecordDataValid section14Catalog 13 (⟨42,(3),[1,2,5,6,13,14],[190],314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨314,[1,2,4,5,6,8,13,14,16],315⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid945 : RecordDataValid section14Catalog 13 (⟨42,(3),[1,5,13],[186],314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨314,[1,2,4,5,6,8,13,14,16],315⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid946 : RecordDataValid section14Catalog 13 (⟨42,(4),[1,2,5,6,13,14],[170],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid947 : RecordDataValid section14Catalog 13 (⟨42,(4),[1,2,5,6,13,14],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid948 : RecordDataValid section14Catalog 13 (⟨42,(4),[1,2,5,6,13,14],[190],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid949 : RecordDataValid section14Catalog 13 (⟨42,(4),[1,5,13],[186],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid950 : RecordDataValid section14Catalog 13 (⟨42,(5),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid951 : RecordDataValid section14Catalog 13 (⟨42,(5),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid952 : RecordDataValid section14Catalog 13 (⟨42,(5),[1,2,5,6,13,14],[190],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid953 : RecordDataValid section14Catalog 13 (⟨42,(5),[1,5,13],[186],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid954 : RecordDataValid section14Catalog 13 (⟨42,(6),[1,2,5,6,13,14],[170],254⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨254,[1,2,3,4,5,6,7,8,13,14,15,16],255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid955 : RecordDataValid section14Catalog 13 (⟨42,(6),[1,2,5,6,13,14],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid956 : RecordDataValid section14Catalog 13 (⟨42,(6),[1,2,5,6,13,14],[190],313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨313,[1,2,4,5,6,8,13,14,16],314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid957 : RecordDataValid section14Catalog 13 (⟨42,(6),[1,5,13],[186],313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨313,[1,2,4,5,6,8,13,14,16],314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid958 : RecordDataValid section14Catalog 13 (⟨42,(7),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid959 : RecordDataValid section14Catalog 13 (⟨42,(7),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 928).take 32 = [⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(24),[1,5,13],[186],3⟩,⟨42,(0),[1,2,5,6,13,14],[170],253⟩,⟨42,(0),[1,2,5,6,13,14],[174],288⟩,⟨42,(0),[1,2,5,6,13,14],[190],312⟩,⟨42,(0),[1,5,13],[186],312⟩,⟨42,(1),[1,2,5,6,13,14],[170],254⟩,⟨42,(1),[1,2,5,6,13,14],[174],289⟩,⟨42,(1),[1,2,5,6,13,14],[190],313⟩,⟨42,(1),[1,5,13],[186],313⟩,⟨42,(2),[1,2,5,6,13,14],[170],253⟩,⟨42,(2),[1,2,5,6,13,14],[174],288⟩,⟨42,(2),[1,2,5,6,13,14],[190],312⟩,⟨42,(2),[1,5,13],[186],312⟩,⟨42,(3),[1,2,5,6,13,14],[170],255⟩,⟨42,(3),[1,2,5,6,13,14],[174],290⟩,⟨42,(3),[1,2,5,6,13,14],[190],314⟩,⟨42,(3),[1,5,13],[186],314⟩,⟨42,(4),[1,2,5,6,13,14],[170],256⟩,⟨42,(4),[1,2,5,6,13,14],[174],291⟩,⟨42,(4),[1,2,5,6,13,14],[190],315⟩,⟨42,(4),[1,5,13],[186],315⟩,⟨42,(5),[1,2,5,6,13,14],[170],253⟩,⟨42,(5),[1,2,5,6,13,14],[174],288⟩,⟨42,(5),[1,2,5,6,13,14],[190],312⟩,⟨42,(5),[1,5,13],[186],312⟩,⟨42,(6),[1,2,5,6,13,14],[170],254⟩,⟨42,(6),[1,2,5,6,13,14],[174],289⟩,⟨42,(6),[1,2,5,6,13,14],[190],313⟩,⟨42,(6),[1,5,13],[186],313⟩,⟨42,(7),[1,2,5,6,13,14],[170],253⟩,⟨42,(7),[1,2,5,6,13,14],[174],288⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid928
  · exact recordValid_of_data section14Catalog 13 _ hnum valid929
  · exact recordValid_of_data section14Catalog 13 _ hnum valid930
  · exact recordValid_of_data section14Catalog 13 _ hnum valid931
  · exact recordValid_of_data section14Catalog 13 _ hnum valid932
  · exact recordValid_of_data section14Catalog 13 _ hnum valid933
  · exact recordValid_of_data section14Catalog 13 _ hnum valid934
  · exact recordValid_of_data section14Catalog 13 _ hnum valid935
  · exact recordValid_of_data section14Catalog 13 _ hnum valid936
  · exact recordValid_of_data section14Catalog 13 _ hnum valid937
  · exact recordValid_of_data section14Catalog 13 _ hnum valid938
  · exact recordValid_of_data section14Catalog 13 _ hnum valid939
  · exact recordValid_of_data section14Catalog 13 _ hnum valid940
  · exact recordValid_of_data section14Catalog 13 _ hnum valid941
  · exact recordValid_of_data section14Catalog 13 _ hnum valid942
  · exact recordValid_of_data section14Catalog 13 _ hnum valid943
  · exact recordValid_of_data section14Catalog 13 _ hnum valid944
  · exact recordValid_of_data section14Catalog 13 _ hnum valid945
  · exact recordValid_of_data section14Catalog 13 _ hnum valid946
  · exact recordValid_of_data section14Catalog 13 _ hnum valid947
  · exact recordValid_of_data section14Catalog 13 _ hnum valid948
  · exact recordValid_of_data section14Catalog 13 _ hnum valid949
  · exact recordValid_of_data section14Catalog 13 _ hnum valid950
  · exact recordValid_of_data section14Catalog 13 _ hnum valid951
  · exact recordValid_of_data section14Catalog 13 _ hnum valid952
  · exact recordValid_of_data section14Catalog 13 _ hnum valid953
  · exact recordValid_of_data section14Catalog 13 _ hnum valid954
  · exact recordValid_of_data section14Catalog 13 _ hnum valid955
  · exact recordValid_of_data section14Catalog 13 _ hnum valid956
  · exact recordValid_of_data section14Catalog 13 _ hnum valid957
  · exact recordValid_of_data section14Catalog 13 _ hnum valid958
  · exact recordValid_of_data section14Catalog 13 _ hnum valid959
end Section14Records_13_928_960

#print axioms solution
