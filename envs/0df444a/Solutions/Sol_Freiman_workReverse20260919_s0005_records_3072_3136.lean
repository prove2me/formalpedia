-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3072_3136
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:30:58.592724+00:00
-- url     : https://prove2.me/submissions/1f92b036-2543-4c0a-8a09-7b58ee6919f6

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3072_3104
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3072_3104
private theorem valid3072 : RecordDataValid section14Catalog 5 (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3073 : RecordDataValid section14Catalog 5 (⟨195,(5),[5,6],[174],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3074 : RecordDataValid section14Catalog 5 (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3075 : RecordDataValid section14Catalog 5 (⟨195,(6),[5,6],[174],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3076 : RecordDataValid section14Catalog 5 (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3077 : RecordDataValid section14Catalog 5 (⟨195,(7),[5,6],[174],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3078 : RecordDataValid section14Catalog 5 (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3079 : RecordDataValid section14Catalog 5 (⟨195,(8),[5,6],[174],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3080 : RecordDataValid section14Catalog 5 (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3081 : RecordDataValid section14Catalog 5 (⟨195,(9),[5,6],[174],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3082 : RecordDataValid section14Catalog 5 (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3083 : RecordDataValid section14Catalog 5 (⟨197,(0),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3084 : RecordDataValid section14Catalog 5 (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3085 : RecordDataValid section14Catalog 5 (⟨197,(1),[5,6],[174],1009⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1009,[3,5,6,7],1013⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3086 : RecordDataValid section14Catalog 5 (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3087 : RecordDataValid section14Catalog 5 (⟨197,(2),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3088 : RecordDataValid section14Catalog 5 (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3089 : RecordDataValid section14Catalog 5 (⟨197,(3),[5,6],[174],1010⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1010,[3,5,6,7],1014⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3090 : RecordDataValid section14Catalog 5 (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3091 : RecordDataValid section14Catalog 5 (⟨197,(4),[5,6],[174],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3092 : RecordDataValid section14Catalog 5 (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3093 : RecordDataValid section14Catalog 5 (⟨197,(5),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3094 : RecordDataValid section14Catalog 5 (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3095 : RecordDataValid section14Catalog 5 (⟨197,(6),[5,6],[174],1009⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1009,[3,5,6,7],1013⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3096 : RecordDataValid section14Catalog 5 (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3097 : RecordDataValid section14Catalog 5 (⟨197,(7),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3098 : RecordDataValid section14Catalog 5 (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3099 : RecordDataValid section14Catalog 5 (⟨197,(8),[5,6],[174],1010⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1010,[3,5,6,7],1014⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3100 : RecordDataValid section14Catalog 5 (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3101 : RecordDataValid section14Catalog 5 (⟨197,(9),[5,6],[174],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3102 : RecordDataValid section14Catalog 5 (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3103 : RecordDataValid section14Catalog 5 (⟨197,(10),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3072_3104 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3072).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3072).take 32 = [⟨195,(5),[1,2,5,6,13,14],[170],700⟩,⟨195,(5),[5,6],[174],700⟩,⟨195,(6),[1,2,5,6,13,14],[170],699⟩,⟨195,(6),[5,6],[174],699⟩,⟨195,(7),[1,2,5,6,13,14],[170],701⟩,⟨195,(7),[5,6],[174],701⟩,⟨195,(8),[1,2,5,6,13,14],[170],702⟩,⟨195,(8),[5,6],[174],702⟩,⟨195,(9),[1,2,5,6,13,14],[170],703⟩,⟨195,(9),[5,6],[174],703⟩,⟨197,(0),[1,2,5,6,13,14],[170],453⟩,⟨197,(0),[5,6],[174],1008⟩,⟨197,(1),[1,2,5,6,13,14],[170],454⟩,⟨197,(1),[5,6],[174],1009⟩,⟨197,(2),[1,2,5,6,13,14],[170],453⟩,⟨197,(2),[5,6],[174],1008⟩,⟨197,(3),[1,2,5,6,13,14],[170],455⟩,⟨197,(3),[5,6],[174],1010⟩,⟨197,(4),[1,2,5,6,13,14],[170],456⟩,⟨197,(4),[5,6],[174],1011⟩,⟨197,(5),[1,2,5,6,13,14],[170],453⟩,⟨197,(5),[5,6],[174],1008⟩,⟨197,(6),[1,2,5,6,13,14],[170],454⟩,⟨197,(6),[5,6],[174],1009⟩,⟨197,(7),[1,2,5,6,13,14],[170],453⟩,⟨197,(7),[5,6],[174],1008⟩,⟨197,(8),[1,2,5,6,13,14],[170],455⟩,⟨197,(8),[5,6],[174],1010⟩,⟨197,(9),[1,2,5,6,13,14],[170],456⟩,⟨197,(9),[5,6],[174],1011⟩,⟨197,(10),[1,2,5,6,13,14],[170],457⟩,⟨197,(10),[5,6],[174],1012⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3072
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3073
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3074
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3075
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3076
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3077
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3078
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3079
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3080
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3081
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3082
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3083
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3084
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3085
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3086
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3087
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3088
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3089
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3090
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3091
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3092
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3093
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3094
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3095
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3096
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3097
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3098
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3099
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3100
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3101
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3102
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3103
end Section14Records_5_3072_3104

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3072_3104


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3104_3136
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3104_3136
private theorem valid3104 : RecordDataValid section14Catalog 5 (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3105 : RecordDataValid section14Catalog 5 (⟨197,(11),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3106 : RecordDataValid section14Catalog 5 (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3107 : RecordDataValid section14Catalog 5 (⟨197,(12),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3108 : RecordDataValid section14Catalog 5 (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3109 : RecordDataValid section14Catalog 5 (⟨197,(13),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3110 : RecordDataValid section14Catalog 5 (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3111 : RecordDataValid section14Catalog 5 (⟨197,(14),[5,6],[174],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3112 : RecordDataValid section14Catalog 5 (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3113 : RecordDataValid section14Catalog 5 (⟨197,(15),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3114 : RecordDataValid section14Catalog 5 (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3115 : RecordDataValid section14Catalog 5 (⟨197,(16),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3116 : RecordDataValid section14Catalog 5 (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3117 : RecordDataValid section14Catalog 5 (⟨197,(17),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3118 : RecordDataValid section14Catalog 5 (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3119 : RecordDataValid section14Catalog 5 (⟨197,(18),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3120 : RecordDataValid section14Catalog 5 (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3121 : RecordDataValid section14Catalog 5 (⟨197,(19),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3122 : RecordDataValid section14Catalog 5 (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3123 : RecordDataValid section14Catalog 5 (⟨197,(20),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3124 : RecordDataValid section14Catalog 5 (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3125 : RecordDataValid section14Catalog 5 (⟨197,(21),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3126 : RecordDataValid section14Catalog 5 (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3127 : RecordDataValid section14Catalog 5 (⟨197,(22),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3128 : RecordDataValid section14Catalog 5 (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3129 : RecordDataValid section14Catalog 5 (⟨197,(23),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3130 : RecordDataValid section14Catalog 5 (⟨197,(24),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3131 : RecordDataValid section14Catalog 5 (⟨197,(24),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3132 : RecordDataValid section14Catalog 5 (⟨200,(0),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3133 : RecordDataValid section14Catalog 5 (⟨200,(0),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3134 : RecordDataValid section14Catalog 5 (⟨200,(1),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3135 : RecordDataValid section14Catalog 5 (⟨200,(1),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3104_3136 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3104).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3104).take 32 = [⟨197,(11),[1,2,5,6,13,14],[170],457⟩,⟨197,(11),[5,6],[174],1012⟩,⟨197,(12),[1,2,5,6,13,14],[170],457⟩,⟨197,(12),[5,6],[174],1012⟩,⟨197,(13),[1,2,5,6,13,14],[170],457⟩,⟨197,(13),[5,6],[174],1012⟩,⟨197,(14),[1,2,5,6,13,14],[170],456⟩,⟨197,(14),[5,6],[174],1011⟩,⟨197,(15),[1,2,5,6,13,14],[170],458⟩,⟨197,(15),[5,6],[174],1013⟩,⟨197,(16),[1,2,5,6,13,14],[170],458⟩,⟨197,(16),[5,6],[174],1013⟩,⟨197,(17),[1,2,5,6,13,14],[170],458⟩,⟨197,(17),[5,6],[174],1013⟩,⟨197,(18),[1,2,5,6,13,14],[170],458⟩,⟨197,(18),[5,6],[174],1013⟩,⟨197,(19),[1,2,5,6,13,14],[170],458⟩,⟨197,(19),[5,6],[174],1013⟩,⟨197,(20),[1,2,5,6,13,14],[170],459⟩,⟨197,(20),[5,6],[174],1014⟩,⟨197,(21),[1,2,5,6,13,14],[170],459⟩,⟨197,(21),[5,6],[174],1014⟩,⟨197,(22),[1,2,5,6,13,14],[170],459⟩,⟨197,(22),[5,6],[174],1014⟩,⟨197,(23),[1,2,5,6,13,14],[170],459⟩,⟨197,(23),[5,6],[174],1014⟩,⟨197,(24),[1,2,5,6,13,14],[170],459⟩,⟨197,(24),[5,6],[174],1014⟩,⟨200,(0),[1,2,5,6,13,14],[170],704⟩,⟨200,(0),[5,6],[174],704⟩,⟨200,(1),[1,2,5,6,13,14],[170],704⟩,⟨200,(1),[5,6],[174],704⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3104
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3105
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3106
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3107
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3108
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3109
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3110
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3111
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3112
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3113
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3114
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3115
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3116
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3117
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3118
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3119
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3120
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3121
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3122
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3123
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3124
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3125
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3126
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3127
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3128
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3129
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3130
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3131
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3132
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3133
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3134
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3135
end Section14Records_5_3104_3136

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3104_3136

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3072).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3072 3104 3136 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3072_3104 hnum) (Freiman.workReverse20260919_s0005_records_3104_3136 hnum))

#print axioms solution
