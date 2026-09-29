-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2944_3008
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:18:32.837417+00:00
-- url     : https://prove2.me/submissions/f69fb526-16dd-45d2-bccc-e9977ed75286

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2944_2976
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2944_2976
private theorem valid2944 : RecordDataValid section14Catalog 6 (⟨205,(1),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2945 : RecordDataValid section14Catalog 6 (⟨205,(2),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2946 : RecordDataValid section14Catalog 6 (⟨205,(2),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2947 : RecordDataValid section14Catalog 6 (⟨205,(3),[1,2,5,6,13,14],[170],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2948 : RecordDataValid section14Catalog 6 (⟨205,(3),[5,6],[174],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2949 : RecordDataValid section14Catalog 6 (⟨205,(4),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2950 : RecordDataValid section14Catalog 6 (⟨205,(4),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2951 : RecordDataValid section14Catalog 6 (⟨205,(5),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2952 : RecordDataValid section14Catalog 6 (⟨205,(5),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2953 : RecordDataValid section14Catalog 6 (⟨205,(6),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2954 : RecordDataValid section14Catalog 6 (⟨205,(6),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2955 : RecordDataValid section14Catalog 6 (⟨205,(7),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2956 : RecordDataValid section14Catalog 6 (⟨205,(7),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2957 : RecordDataValid section14Catalog 6 (⟨205,(8),[1,2,5,6,13,14],[170],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2958 : RecordDataValid section14Catalog 6 (⟨205,(8),[5,6],[174],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2959 : RecordDataValid section14Catalog 6 (⟨205,(9),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2960 : RecordDataValid section14Catalog 6 (⟨205,(9),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2961 : RecordDataValid section14Catalog 6 (⟨205,(10),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2962 : RecordDataValid section14Catalog 6 (⟨205,(10),[5,6],[174],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2963 : RecordDataValid section14Catalog 6 (⟨205,(11),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2964 : RecordDataValid section14Catalog 6 (⟨205,(11),[5,6],[174],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2965 : RecordDataValid section14Catalog 6 (⟨205,(12),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2966 : RecordDataValid section14Catalog 6 (⟨205,(12),[5,6],[174],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2967 : RecordDataValid section14Catalog 6 (⟨205,(13),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2968 : RecordDataValid section14Catalog 6 (⟨205,(13),[5,6],[174],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2969 : RecordDataValid section14Catalog 6 (⟨205,(14),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2970 : RecordDataValid section14Catalog 6 (⟨205,(14),[5,6],[174],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2971 : RecordDataValid section14Catalog 6 (⟨205,(15),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2972 : RecordDataValid section14Catalog 6 (⟨205,(15),[5,6],[174],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2973 : RecordDataValid section14Catalog 6 (⟨205,(16),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2974 : RecordDataValid section14Catalog 6 (⟨205,(16),[5,6],[174],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2975 : RecordDataValid section14Catalog 6 (⟨205,(17),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2944_2976 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2944).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2944).take 32 = [⟨205,(1),[5,6],[174],711⟩,⟨205,(2),[1,2,5,6,13,14],[170],711⟩,⟨205,(2),[5,6],[174],711⟩,⟨205,(3),[1,2,5,6,13,14],[170],712⟩,⟨205,(3),[5,6],[174],712⟩,⟨205,(4),[1,2,5,6,13,14],[170],711⟩,⟨205,(4),[5,6],[174],711⟩,⟨205,(5),[1,2,5,6,13,14],[170],713⟩,⟨205,(5),[5,6],[174],713⟩,⟨205,(6),[1,2,5,6,13,14],[170],713⟩,⟨205,(6),[5,6],[174],713⟩,⟨205,(7),[1,2,5,6,13,14],[170],713⟩,⟨205,(7),[5,6],[174],713⟩,⟨205,(8),[1,2,5,6,13,14],[170],714⟩,⟨205,(8),[5,6],[174],714⟩,⟨205,(9),[1,2,5,6,13,14],[170],713⟩,⟨205,(9),[5,6],[174],713⟩,⟨205,(10),[1,2,5,6,13,14],[170],715⟩,⟨205,(10),[5,6],[174],715⟩,⟨205,(11),[1,2,5,6,13,14],[170],716⟩,⟨205,(11),[5,6],[174],716⟩,⟨205,(12),[1,2,5,6,13,14],[170],717⟩,⟨205,(12),[5,6],[174],717⟩,⟨205,(13),[1,2,5,6,13,14],[170],718⟩,⟨205,(13),[5,6],[174],718⟩,⟨205,(14),[1,2,5,6,13,14],[170],719⟩,⟨205,(14),[5,6],[174],719⟩,⟨205,(15),[1,2,5,6,13,14],[170],715⟩,⟨205,(15),[5,6],[174],715⟩,⟨205,(16),[1,2,5,6,13,14],[170],720⟩,⟨205,(16),[5,6],[174],720⟩,⟨205,(17),[1,2,5,6,13,14],[170],720⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2944
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2945
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2946
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2947
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2948
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2949
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2950
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2951
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2952
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2953
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2954
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2955
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2956
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2957
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2958
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2959
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2960
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2961
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2962
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2963
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2964
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2965
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2966
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2967
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2968
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2969
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2970
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2971
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2972
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2973
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2974
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2975
end Section14Records_6_2944_2976

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2944_2976


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2976_3008
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2976_3008
private theorem valid2976 : RecordDataValid section14Catalog 6 (⟨205,(17),[5,6],[174],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2977 : RecordDataValid section14Catalog 6 (⟨205,(18),[1,2,5,6,13,14],[170],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2978 : RecordDataValid section14Catalog 6 (⟨205,(18),[5,6],[174],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2979 : RecordDataValid section14Catalog 6 (⟨205,(19),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2980 : RecordDataValid section14Catalog 6 (⟨205,(19),[5,6],[174],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2981 : RecordDataValid section14Catalog 6 (⟨205,(20),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2982 : RecordDataValid section14Catalog 6 (⟨205,(20),[5,6],[174],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2983 : RecordDataValid section14Catalog 6 (⟨205,(21),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2984 : RecordDataValid section14Catalog 6 (⟨205,(21),[5,6],[174],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2985 : RecordDataValid section14Catalog 6 (⟨205,(22),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2986 : RecordDataValid section14Catalog 6 (⟨205,(22),[5,6],[174],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2987 : RecordDataValid section14Catalog 6 (⟨205,(23),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2988 : RecordDataValid section14Catalog 6 (⟨205,(23),[5,6],[174],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2989 : RecordDataValid section14Catalog 6 (⟨205,(24),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2990 : RecordDataValid section14Catalog 6 (⟨205,(24),[5,6],[174],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2991 : RecordDataValid section14Catalog 6 (⟨207,(0),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2992 : RecordDataValid section14Catalog 6 (⟨207,(0),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2993 : RecordDataValid section14Catalog 6 (⟨207,(1),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2994 : RecordDataValid section14Catalog 6 (⟨207,(1),[5,6],[174],1023⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1023,[3,5,6,7],1027⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2995 : RecordDataValid section14Catalog 6 (⟨207,(2),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2996 : RecordDataValid section14Catalog 6 (⟨207,(2),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2997 : RecordDataValid section14Catalog 6 (⟨207,(3),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2998 : RecordDataValid section14Catalog 6 (⟨207,(3),[5,6],[174],1024⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1024,[3,5,6,7],1028⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2999 : RecordDataValid section14Catalog 6 (⟨207,(4),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3000 : RecordDataValid section14Catalog 6 (⟨207,(4),[5,6],[174],1025⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1025,[3,5,6,7],1029⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3001 : RecordDataValid section14Catalog 6 (⟨207,(5),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3002 : RecordDataValid section14Catalog 6 (⟨207,(5),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3003 : RecordDataValid section14Catalog 6 (⟨207,(6),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3004 : RecordDataValid section14Catalog 6 (⟨207,(6),[5,6],[174],1023⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1023,[3,5,6,7],1027⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3005 : RecordDataValid section14Catalog 6 (⟨207,(7),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3006 : RecordDataValid section14Catalog 6 (⟨207,(7),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3007 : RecordDataValid section14Catalog 6 (⟨207,(8),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2976_3008 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2976).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2976).take 32 = [⟨205,(17),[5,6],[174],720⟩,⟨205,(18),[1,2,5,6,13,14],[170],721⟩,⟨205,(18),[5,6],[174],721⟩,⟨205,(19),[1,2,5,6,13,14],[170],720⟩,⟨205,(19),[5,6],[174],720⟩,⟨205,(20),[1,2,5,6,13,14],[170],715⟩,⟨205,(20),[5,6],[174],715⟩,⟨205,(21),[1,2,5,6,13,14],[170],716⟩,⟨205,(21),[5,6],[174],716⟩,⟨205,(22),[1,2,5,6,13,14],[170],717⟩,⟨205,(22),[5,6],[174],717⟩,⟨205,(23),[1,2,5,6,13,14],[170],718⟩,⟨205,(23),[5,6],[174],718⟩,⟨205,(24),[1,2,5,6,13,14],[170],719⟩,⟨205,(24),[5,6],[174],719⟩,⟨207,(0),[1,2,5,6,13,14],[170],481⟩,⟨207,(0),[5,6],[174],1022⟩,⟨207,(1),[1,2,5,6,13,14],[170],482⟩,⟨207,(1),[5,6],[174],1023⟩,⟨207,(2),[1,2,5,6,13,14],[170],481⟩,⟨207,(2),[5,6],[174],1022⟩,⟨207,(3),[1,2,5,6,13,14],[170],483⟩,⟨207,(3),[5,6],[174],1024⟩,⟨207,(4),[1,2,5,6,13,14],[170],484⟩,⟨207,(4),[5,6],[174],1025⟩,⟨207,(5),[1,2,5,6,13,14],[170],481⟩,⟨207,(5),[5,6],[174],1022⟩,⟨207,(6),[1,2,5,6,13,14],[170],482⟩,⟨207,(6),[5,6],[174],1023⟩,⟨207,(7),[1,2,5,6,13,14],[170],481⟩,⟨207,(7),[5,6],[174],1022⟩,⟨207,(8),[1,2,5,6,13,14],[170],483⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2976
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2977
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2978
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2979
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2980
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2981
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2982
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2983
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2984
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2985
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2986
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2987
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2988
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2989
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2990
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2991
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2992
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2993
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2994
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2995
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2996
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2997
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2998
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2999
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3000
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3001
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3002
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3003
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3004
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3005
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3006
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3007
end Section14Records_6_2976_3008

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2976_3008

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2944).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2944 2976 3008 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2944_2976 hnum) (Freiman.workReverse20260919_s0006_records_2976_3008 hnum))

#print axioms solution
