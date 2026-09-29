-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2880_2944
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:18:21.209505+00:00
-- url     : https://prove2.me/submissions/7c3ffa8e-054a-4dd9-90f7-ec9b7e630116

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2880_2912
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2880_2912
private theorem valid2880 : RecordDataValid section14Catalog 6 (⟨200,(19),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2881 : RecordDataValid section14Catalog 6 (⟨200,(20),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2882 : RecordDataValid section14Catalog 6 (⟨200,(20),[5,6],[174],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2883 : RecordDataValid section14Catalog 6 (⟨200,(21),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2884 : RecordDataValid section14Catalog 6 (⟨200,(21),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2885 : RecordDataValid section14Catalog 6 (⟨200,(22),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2886 : RecordDataValid section14Catalog 6 (⟨200,(22),[5,6],[174],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2887 : RecordDataValid section14Catalog 6 (⟨200,(23),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2888 : RecordDataValid section14Catalog 6 (⟨200,(23),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2889 : RecordDataValid section14Catalog 6 (⟨200,(24),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2890 : RecordDataValid section14Catalog 6 (⟨200,(24),[5,6],[174],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2891 : RecordDataValid section14Catalog 6 (⟨202,(0),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2892 : RecordDataValid section14Catalog 6 (⟨202,(0),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2893 : RecordDataValid section14Catalog 6 (⟨202,(1),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2894 : RecordDataValid section14Catalog 6 (⟨202,(1),[5,6],[174],1016⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1016,[3,5,6,7],1020⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2895 : RecordDataValid section14Catalog 6 (⟨202,(2),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2896 : RecordDataValid section14Catalog 6 (⟨202,(2),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2897 : RecordDataValid section14Catalog 6 (⟨202,(3),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2898 : RecordDataValid section14Catalog 6 (⟨202,(3),[5,6],[174],1017⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1017,[3,5,6,7],1021⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2899 : RecordDataValid section14Catalog 6 (⟨202,(4),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2900 : RecordDataValid section14Catalog 6 (⟨202,(4),[5,6],[174],1018⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1018,[3,5,6,7],1022⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2901 : RecordDataValid section14Catalog 6 (⟨202,(5),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2902 : RecordDataValid section14Catalog 6 (⟨202,(5),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2903 : RecordDataValid section14Catalog 6 (⟨202,(6),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2904 : RecordDataValid section14Catalog 6 (⟨202,(6),[5,6],[174],1016⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1016,[3,5,6,7],1020⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2905 : RecordDataValid section14Catalog 6 (⟨202,(7),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2906 : RecordDataValid section14Catalog 6 (⟨202,(7),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2907 : RecordDataValid section14Catalog 6 (⟨202,(8),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2908 : RecordDataValid section14Catalog 6 (⟨202,(8),[5,6],[174],1017⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1017,[3,5,6,7],1021⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2909 : RecordDataValid section14Catalog 6 (⟨202,(9),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2910 : RecordDataValid section14Catalog 6 (⟨202,(9),[5,6],[174],1018⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1018,[3,5,6,7],1022⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2911 : RecordDataValid section14Catalog 6 (⟨202,(10),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2880_2912 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2880).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2880).take 32 = [⟨200,(19),[5,6],[174],710⟩,⟨200,(20),[1,2,5,6,13,14],[170],706⟩,⟨200,(20),[5,6],[174],706⟩,⟨200,(21),[1,2,5,6,13,14],[170],707⟩,⟨200,(21),[5,6],[174],707⟩,⟨200,(22),[1,2,5,6,13,14],[170],708⟩,⟨200,(22),[5,6],[174],708⟩,⟨200,(23),[1,2,5,6,13,14],[170],707⟩,⟨200,(23),[5,6],[174],707⟩,⟨200,(24),[1,2,5,6,13,14],[170],709⟩,⟨200,(24),[5,6],[174],709⟩,⟨202,(0),[1,2,5,6,13,14],[170],467⟩,⟨202,(0),[5,6],[174],1015⟩,⟨202,(1),[1,2,5,6,13,14],[170],468⟩,⟨202,(1),[5,6],[174],1016⟩,⟨202,(2),[1,2,5,6,13,14],[170],467⟩,⟨202,(2),[5,6],[174],1015⟩,⟨202,(3),[1,2,5,6,13,14],[170],469⟩,⟨202,(3),[5,6],[174],1017⟩,⟨202,(4),[1,2,5,6,13,14],[170],470⟩,⟨202,(4),[5,6],[174],1018⟩,⟨202,(5),[1,2,5,6,13,14],[170],467⟩,⟨202,(5),[5,6],[174],1015⟩,⟨202,(6),[1,2,5,6,13,14],[170],468⟩,⟨202,(6),[5,6],[174],1016⟩,⟨202,(7),[1,2,5,6,13,14],[170],467⟩,⟨202,(7),[5,6],[174],1015⟩,⟨202,(8),[1,2,5,6,13,14],[170],469⟩,⟨202,(8),[5,6],[174],1017⟩,⟨202,(9),[1,2,5,6,13,14],[170],470⟩,⟨202,(9),[5,6],[174],1018⟩,⟨202,(10),[1,2,5,6,13,14],[170],471⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2880
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2881
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2882
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2883
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2884
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2885
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2886
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2887
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2888
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2889
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2890
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2891
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2892
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2893
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2894
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2895
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2896
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2897
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2898
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2899
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2900
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2901
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2902
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2903
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2904
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2905
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2906
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2907
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2908
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2909
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2910
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2911
end Section14Records_6_2880_2912

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2880_2912


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2912_2944
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2912_2944
private theorem valid2912 : RecordDataValid section14Catalog 6 (⟨202,(10),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2913 : RecordDataValid section14Catalog 6 (⟨202,(11),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2914 : RecordDataValid section14Catalog 6 (⟨202,(11),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2915 : RecordDataValid section14Catalog 6 (⟨202,(12),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2916 : RecordDataValid section14Catalog 6 (⟨202,(12),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2917 : RecordDataValid section14Catalog 6 (⟨202,(13),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2918 : RecordDataValid section14Catalog 6 (⟨202,(13),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2919 : RecordDataValid section14Catalog 6 (⟨202,(14),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2920 : RecordDataValid section14Catalog 6 (⟨202,(14),[5,6],[174],1018⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1018,[3,5,6,7],1022⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2921 : RecordDataValid section14Catalog 6 (⟨202,(15),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2922 : RecordDataValid section14Catalog 6 (⟨202,(15),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2923 : RecordDataValid section14Catalog 6 (⟨202,(16),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2924 : RecordDataValid section14Catalog 6 (⟨202,(16),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2925 : RecordDataValid section14Catalog 6 (⟨202,(17),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2926 : RecordDataValid section14Catalog 6 (⟨202,(17),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2927 : RecordDataValid section14Catalog 6 (⟨202,(18),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2928 : RecordDataValid section14Catalog 6 (⟨202,(18),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2929 : RecordDataValid section14Catalog 6 (⟨202,(19),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2930 : RecordDataValid section14Catalog 6 (⟨202,(19),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2931 : RecordDataValid section14Catalog 6 (⟨202,(20),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2932 : RecordDataValid section14Catalog 6 (⟨202,(20),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2933 : RecordDataValid section14Catalog 6 (⟨202,(21),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2934 : RecordDataValid section14Catalog 6 (⟨202,(21),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2935 : RecordDataValid section14Catalog 6 (⟨202,(22),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2936 : RecordDataValid section14Catalog 6 (⟨202,(22),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2937 : RecordDataValid section14Catalog 6 (⟨202,(23),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2938 : RecordDataValid section14Catalog 6 (⟨202,(23),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2939 : RecordDataValid section14Catalog 6 (⟨202,(24),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2940 : RecordDataValid section14Catalog 6 (⟨202,(24),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2941 : RecordDataValid section14Catalog 6 (⟨205,(0),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2942 : RecordDataValid section14Catalog 6 (⟨205,(0),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2943 : RecordDataValid section14Catalog 6 (⟨205,(1),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2912_2944 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2912).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2912).take 32 = [⟨202,(10),[5,6],[174],1019⟩,⟨202,(11),[1,2,5,6,13,14],[170],471⟩,⟨202,(11),[5,6],[174],1019⟩,⟨202,(12),[1,2,5,6,13,14],[170],471⟩,⟨202,(12),[5,6],[174],1019⟩,⟨202,(13),[1,2,5,6,13,14],[170],471⟩,⟨202,(13),[5,6],[174],1019⟩,⟨202,(14),[1,2,5,6,13,14],[170],470⟩,⟨202,(14),[5,6],[174],1018⟩,⟨202,(15),[1,2,5,6,13,14],[170],472⟩,⟨202,(15),[5,6],[174],1020⟩,⟨202,(16),[1,2,5,6,13,14],[170],472⟩,⟨202,(16),[5,6],[174],1020⟩,⟨202,(17),[1,2,5,6,13,14],[170],472⟩,⟨202,(17),[5,6],[174],1020⟩,⟨202,(18),[1,2,5,6,13,14],[170],472⟩,⟨202,(18),[5,6],[174],1020⟩,⟨202,(19),[1,2,5,6,13,14],[170],472⟩,⟨202,(19),[5,6],[174],1020⟩,⟨202,(20),[1,2,5,6,13,14],[170],473⟩,⟨202,(20),[5,6],[174],1021⟩,⟨202,(21),[1,2,5,6,13,14],[170],473⟩,⟨202,(21),[5,6],[174],1021⟩,⟨202,(22),[1,2,5,6,13,14],[170],473⟩,⟨202,(22),[5,6],[174],1021⟩,⟨202,(23),[1,2,5,6,13,14],[170],473⟩,⟨202,(23),[5,6],[174],1021⟩,⟨202,(24),[1,2,5,6,13,14],[170],473⟩,⟨202,(24),[5,6],[174],1021⟩,⟨205,(0),[1,2,5,6,13,14],[170],711⟩,⟨205,(0),[5,6],[174],711⟩,⟨205,(1),[1,2,5,6,13,14],[170],711⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2912
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2913
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2914
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2915
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2916
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2917
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2918
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2919
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2920
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2921
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2922
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2923
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2924
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2925
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2926
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2927
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2928
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2929
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2930
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2931
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2932
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2933
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2934
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2935
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2936
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2937
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2938
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2939
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2940
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2941
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2942
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2943
end Section14Records_6_2912_2944

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2912_2944

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2880).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2880 2912 2944 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2880_2912 hnum) (Freiman.workReverse20260919_s0006_records_2912_2944 hnum))

#print axioms solution
