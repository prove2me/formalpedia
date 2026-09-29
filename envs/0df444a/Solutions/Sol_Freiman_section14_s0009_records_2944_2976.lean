-- Prove2me | solution 1 for Freiman.section14_s0009_records_2944_2976
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:59:00.090643+00:00
-- url     : https://prove2.me/submissions/d0fc535c-3c16-4ced-8cfd-6af79f39e5b5

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
namespace Section14Records_9_2944_2976
private theorem valid2944 : RecordDataValid section14Catalog 9 (⟨562,(7),[9,10],[42],1667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1667,[9,10,11,12],1672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2945 : RecordDataValid section14Catalog 9 (⟨562,(8),[9,10],[42],1668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1668,[9,10,11,12],1673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2946 : RecordDataValid section14Catalog 9 (⟨562,(9),[9,10],[42],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2947 : RecordDataValid section14Catalog 9 (⟨567,(0),[9,10],[42],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2948 : RecordDataValid section14Catalog 9 (⟨567,(1),[9],[42],1669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1669,[9,12],1674⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2949 : RecordDataValid section14Catalog 9 (⟨567,(2),[9],[42],1670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1670,[9,12],1675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2950 : RecordDataValid section14Catalog 9 (⟨567,(3),[9],[42],1671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1671,[9,12],1676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2951 : RecordDataValid section14Catalog 9 (⟨567,(4),[9],[42],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2952 : RecordDataValid section14Catalog 9 (⟨567,(5),[9,10],[42],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2953 : RecordDataValid section14Catalog 9 (⟨567,(6),[9],[42],1669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1669,[9,12],1674⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2954 : RecordDataValid section14Catalog 9 (⟨567,(7),[9],[42],1670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1670,[9,12],1675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2955 : RecordDataValid section14Catalog 9 (⟨567,(8),[9],[42],1671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1671,[9,12],1676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2956 : RecordDataValid section14Catalog 9 (⟨567,(9),[9],[42],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2957 : RecordDataValid section14Catalog 9 (⟨572,(0),[9,10],[42],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2958 : RecordDataValid section14Catalog 9 (⟨572,(1),[9,10],[42],1672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1672,[9,10,11],1677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2959 : RecordDataValid section14Catalog 9 (⟨572,(2),[9,10],[42],1673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1673,[9,10,11,12],1678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2960 : RecordDataValid section14Catalog 9 (⟨572,(3),[9,10],[42],1674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1674,[9,10,11,12],1679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2961 : RecordDataValid section14Catalog 9 (⟨572,(4),[9,10],[42],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2962 : RecordDataValid section14Catalog 9 (⟨572,(5),[9,10],[42],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2963 : RecordDataValid section14Catalog 9 (⟨572,(6),[9,10],[42],1672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1672,[9,10,11],1677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2964 : RecordDataValid section14Catalog 9 (⟨572,(7),[9,10],[42],1673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1673,[9,10,11,12],1678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2965 : RecordDataValid section14Catalog 9 (⟨572,(8),[9,10],[42],1674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1674,[9,10,11,12],1679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2966 : RecordDataValid section14Catalog 9 (⟨572,(9),[9,10],[42],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2967 : RecordDataValid section14Catalog 9 (⟨577,(0),[9,10],[42],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2968 : RecordDataValid section14Catalog 9 (⟨577,(1),[9,10],[42],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2969 : RecordDataValid section14Catalog 9 (⟨577,(2),[9,10],[42],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2970 : RecordDataValid section14Catalog 9 (⟨577,(3),[9,10],[42],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2971 : RecordDataValid section14Catalog 9 (⟨577,(4),[9,10],[42],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2972 : RecordDataValid section14Catalog 9 (⟨577,(5),[9,10],[42],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2973 : RecordDataValid section14Catalog 9 (⟨577,(6),[9,10],[42],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2974 : RecordDataValid section14Catalog 9 (⟨577,(7),[9,10],[42],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2975 : RecordDataValid section14Catalog 9 (⟨577,(8),[9,10],[42],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2944).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2944).take 32 = [⟨562,(7),[9,10],[42],1667⟩,⟨562,(8),[9,10],[42],1668⟩,⟨562,(9),[9,10],[42],396⟩,⟨567,(0),[9,10],[42],1649⟩,⟨567,(1),[9],[42],1669⟩,⟨567,(2),[9],[42],1670⟩,⟨567,(3),[9],[42],1671⟩,⟨567,(4),[9],[42],1275⟩,⟨567,(5),[9,10],[42],1649⟩,⟨567,(6),[9],[42],1669⟩,⟨567,(7),[9],[42],1670⟩,⟨567,(8),[9],[42],1671⟩,⟨567,(9),[9],[42],1275⟩,⟨572,(0),[9,10],[42],1649⟩,⟨572,(1),[9,10],[42],1672⟩,⟨572,(2),[9,10],[42],1673⟩,⟨572,(3),[9,10],[42],1674⟩,⟨572,(4),[9,10],[42],890⟩,⟨572,(5),[9,10],[42],1649⟩,⟨572,(6),[9,10],[42],1672⟩,⟨572,(7),[9,10],[42],1673⟩,⟨572,(8),[9,10],[42],1674⟩,⟨572,(9),[9,10],[42],890⟩,⟨577,(0),[9,10],[42],904⟩,⟨577,(1),[9,10],[42],904⟩,⟨577,(2),[9,10],[42],900⟩,⟨577,(3),[9,10],[42],901⟩,⟨577,(4),[9,10],[42],902⟩,⟨577,(5),[9,10],[42],905⟩,⟨577,(6),[9,10],[42],905⟩,⟨577,(7),[9,10],[42],905⟩,⟨577,(8),[9,10],[42],901⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2944
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2945
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2946
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2947
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2948
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2949
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2950
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2951
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2952
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2953
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2954
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2955
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2956
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2957
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2958
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2959
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2960
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2961
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2962
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2963
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2964
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2965
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2966
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2967
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2968
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2969
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2970
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2971
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2972
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2973
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2974
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2975
end Section14Records_9_2944_2976

#print axioms solution
