-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_2880_2944
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:30:43.432668+00:00
-- url     : https://prove2.me/submissions/8936e480-7dca-41df-bdb9-cf68b66d2fde

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2880_2912
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2880_2912
private theorem valid2880 : RecordDataValid section14Catalog 5 (⟨183,(7),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2881 : RecordDataValid section14Catalog 5 (⟨183,(7),[5,6],[174],992⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨992,[3,5,6,7],996⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2882 : RecordDataValid section14Catalog 5 (⟨183,(8),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2883 : RecordDataValid section14Catalog 5 (⟨183,(8),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2884 : RecordDataValid section14Catalog 5 (⟨183,(9),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2885 : RecordDataValid section14Catalog 5 (⟨183,(9),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2886 : RecordDataValid section14Catalog 5 (⟨183,(10),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2887 : RecordDataValid section14Catalog 5 (⟨183,(10),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2888 : RecordDataValid section14Catalog 5 (⟨183,(11),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2889 : RecordDataValid section14Catalog 5 (⟨183,(11),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2890 : RecordDataValid section14Catalog 5 (⟨183,(12),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2891 : RecordDataValid section14Catalog 5 (⟨183,(12),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2892 : RecordDataValid section14Catalog 5 (⟨183,(13),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2893 : RecordDataValid section14Catalog 5 (⟨183,(13),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2894 : RecordDataValid section14Catalog 5 (⟨183,(14),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2895 : RecordDataValid section14Catalog 5 (⟨183,(14),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2896 : RecordDataValid section14Catalog 5 (⟨183,(15),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2897 : RecordDataValid section14Catalog 5 (⟨183,(15),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2898 : RecordDataValid section14Catalog 5 (⟨185,(0),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2899 : RecordDataValid section14Catalog 5 (⟨185,(0),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2900 : RecordDataValid section14Catalog 5 (⟨185,(1),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2901 : RecordDataValid section14Catalog 5 (⟨185,(1),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2902 : RecordDataValid section14Catalog 5 (⟨185,(2),[1,2,5,6,13,14],[170],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2903 : RecordDataValid section14Catalog 5 (⟨185,(2),[5,6],[174],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2904 : RecordDataValid section14Catalog 5 (⟨185,(3),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2905 : RecordDataValid section14Catalog 5 (⟨185,(3),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2906 : RecordDataValid section14Catalog 5 (⟨185,(4),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2907 : RecordDataValid section14Catalog 5 (⟨185,(4),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2908 : RecordDataValid section14Catalog 5 (⟨185,(5),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2909 : RecordDataValid section14Catalog 5 (⟨185,(5),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2910 : RecordDataValid section14Catalog 5 (⟨185,(6),[1,2,5,6,13,14],[170],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2911 : RecordDataValid section14Catalog 5 (⟨185,(6),[5,6],[174],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2880_2912 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2880).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2880).take 32 = [⟨183,(7),[1,2,5,6,13,14],[170],675⟩,⟨183,(7),[5,6],[174],992⟩,⟨183,(8),[1,2,5,6,13,14],[170],676⟩,⟨183,(8),[5,6],[174],993⟩,⟨183,(9),[1,2,5,6,13,14],[170],676⟩,⟨183,(9),[5,6],[174],993⟩,⟨183,(10),[1,2,5,6,13,14],[170],676⟩,⟨183,(10),[5,6],[174],993⟩,⟨183,(11),[1,2,5,6,13,14],[170],676⟩,⟨183,(11),[5,6],[174],993⟩,⟨183,(12),[1,2,5,6,13,14],[170],677⟩,⟨183,(12),[5,6],[174],994⟩,⟨183,(13),[1,2,5,6,13,14],[170],677⟩,⟨183,(13),[5,6],[174],994⟩,⟨183,(14),[1,2,5,6,13,14],[170],677⟩,⟨183,(14),[5,6],[174],994⟩,⟨183,(15),[1,2,5,6,13,14],[170],677⟩,⟨183,(15),[5,6],[174],994⟩,⟨185,(0),[1,2,5,6,13,14],[170],678⟩,⟨185,(0),[5,6],[174],678⟩,⟨185,(1),[1,2,5,6,13,14],[170],679⟩,⟨185,(1),[5,6],[174],679⟩,⟨185,(2),[1,2,5,6,13,14],[170],680⟩,⟨185,(2),[5,6],[174],680⟩,⟨185,(3),[1,2,5,6,13,14],[170],681⟩,⟨185,(3),[5,6],[174],681⟩,⟨185,(4),[1,2,5,6,13,14],[170],678⟩,⟨185,(4),[5,6],[174],678⟩,⟨185,(5),[1,2,5,6,13,14],[170],679⟩,⟨185,(5),[5,6],[174],679⟩,⟨185,(6),[1,2,5,6,13,14],[170],682⟩,⟨185,(6),[5,6],[174],682⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2880
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2881
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2882
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2883
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2884
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2885
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2886
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2887
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2888
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2889
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2890
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2891
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2892
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2893
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2894
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2895
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2896
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2897
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2898
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2899
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2900
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2901
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2902
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2903
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2904
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2905
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2906
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2907
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2908
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2909
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2910
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2911
end Section14Records_5_2880_2912

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2880_2912


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2912_2944
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2912_2944
private theorem valid2912 : RecordDataValid section14Catalog 5 (⟨185,(7),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2913 : RecordDataValid section14Catalog 5 (⟨185,(7),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2914 : RecordDataValid section14Catalog 5 (⟨185,(8),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2915 : RecordDataValid section14Catalog 5 (⟨185,(8),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2916 : RecordDataValid section14Catalog 5 (⟨185,(9),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2917 : RecordDataValid section14Catalog 5 (⟨185,(9),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2918 : RecordDataValid section14Catalog 5 (⟨185,(10),[1,2,5,6,13,14],[170],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2919 : RecordDataValid section14Catalog 5 (⟨185,(10),[5,6],[174],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2920 : RecordDataValid section14Catalog 5 (⟨185,(11),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2921 : RecordDataValid section14Catalog 5 (⟨185,(11),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2922 : RecordDataValid section14Catalog 5 (⟨185,(12),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2923 : RecordDataValid section14Catalog 5 (⟨185,(12),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2924 : RecordDataValid section14Catalog 5 (⟨185,(13),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2925 : RecordDataValid section14Catalog 5 (⟨185,(13),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2926 : RecordDataValid section14Catalog 5 (⟨185,(14),[1,2,5,6,13,14],[170],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2927 : RecordDataValid section14Catalog 5 (⟨185,(14),[5,6],[174],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2928 : RecordDataValid section14Catalog 5 (⟨185,(15),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2929 : RecordDataValid section14Catalog 5 (⟨185,(15),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2930 : RecordDataValid section14Catalog 5 (⟨188,(0),[1,2,5,6,13,14],[170],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2931 : RecordDataValid section14Catalog 5 (⟨188,(0),[5,6],[174],995⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨995,[3,5,6,7],999⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2932 : RecordDataValid section14Catalog 5 (⟨188,(1),[1,2,5,6,13,14],[170],685⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨685,[1,2,3,5,6,7,10,11,13,14,15],686⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2933 : RecordDataValid section14Catalog 5 (⟨188,(1),[5,6],[174],996⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨996,[3,5,6,7],1000⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2934 : RecordDataValid section14Catalog 5 (⟨188,(2),[1,2,5,6,13,14],[170],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2935 : RecordDataValid section14Catalog 5 (⟨188,(2),[5,6],[174],995⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨995,[3,5,6,7],999⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2936 : RecordDataValid section14Catalog 5 (⟨188,(3),[1,2,5,6,13,14],[170],686⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨686,[1,2,3,5,6,7,10,11,13,14,15],687⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2937 : RecordDataValid section14Catalog 5 (⟨188,(3),[5,6],[174],997⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨997,[3,5,6,7],1001⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2938 : RecordDataValid section14Catalog 5 (⟨188,(4),[1,2,5,6,13,14],[170],687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨687,[1,2,3,5,6,7,10,11,13,14,15],688⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2939 : RecordDataValid section14Catalog 5 (⟨188,(4),[5,6],[174],998⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨998,[3,5,6,7],1002⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2940 : RecordDataValid section14Catalog 5 (⟨188,(5),[1,2,5,6,13,14],[170],687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨687,[1,2,3,5,6,7,10,11,13,14,15],688⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2941 : RecordDataValid section14Catalog 5 (⟨188,(5),[5,6],[174],998⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨998,[3,5,6,7],1002⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2942 : RecordDataValid section14Catalog 5 (⟨188,(6),[1,2,5,6,13,14],[170],687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨687,[1,2,3,5,6,7,10,11,13,14,15],688⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2943 : RecordDataValid section14Catalog 5 (⟨188,(6),[5,6],[174],998⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨998,[3,5,6,7],1002⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2912_2944 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2912).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2912).take 32 = [⟨185,(7),[1,2,5,6,13,14],[170],681⟩,⟨185,(7),[5,6],[174],681⟩,⟨185,(8),[1,2,5,6,13,14],[170],678⟩,⟨185,(8),[5,6],[174],678⟩,⟨185,(9),[1,2,5,6,13,14],[170],679⟩,⟨185,(9),[5,6],[174],679⟩,⟨185,(10),[1,2,5,6,13,14],[170],680⟩,⟨185,(10),[5,6],[174],680⟩,⟨185,(11),[1,2,5,6,13,14],[170],681⟩,⟨185,(11),[5,6],[174],681⟩,⟨185,(12),[1,2,5,6,13,14],[170],678⟩,⟨185,(12),[5,6],[174],678⟩,⟨185,(13),[1,2,5,6,13,14],[170],679⟩,⟨185,(13),[5,6],[174],679⟩,⟨185,(14),[1,2,5,6,13,14],[170],683⟩,⟨185,(14),[5,6],[174],683⟩,⟨185,(15),[1,2,5,6,13,14],[170],681⟩,⟨185,(15),[5,6],[174],681⟩,⟨188,(0),[1,2,5,6,13,14],[170],684⟩,⟨188,(0),[5,6],[174],995⟩,⟨188,(1),[1,2,5,6,13,14],[170],685⟩,⟨188,(1),[5,6],[174],996⟩,⟨188,(2),[1,2,5,6,13,14],[170],684⟩,⟨188,(2),[5,6],[174],995⟩,⟨188,(3),[1,2,5,6,13,14],[170],686⟩,⟨188,(3),[5,6],[174],997⟩,⟨188,(4),[1,2,5,6,13,14],[170],687⟩,⟨188,(4),[5,6],[174],998⟩,⟨188,(5),[1,2,5,6,13,14],[170],687⟩,⟨188,(5),[5,6],[174],998⟩,⟨188,(6),[1,2,5,6,13,14],[170],687⟩,⟨188,(6),[5,6],[174],998⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2912
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2913
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2914
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2915
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2916
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2917
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2918
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2919
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2920
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2921
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2922
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2923
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2924
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2925
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2926
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2927
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2928
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2929
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2930
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2931
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2932
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2933
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2934
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2935
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2936
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2937
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2938
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2939
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2940
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2941
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2942
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2943
end Section14Records_5_2912_2944

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2912_2944

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2880).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 2880 2912 2944 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2880_2912 hnum) (Freiman.workReverse20260919_s0005_records_2912_2944 hnum))

#print axioms solution
