-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3840_3904
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:32:50.551489+00:00
-- url     : https://prove2.me/submissions/bee51851-2fc7-4b2f-9ff9-59729233509c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3840_3872
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3840_3872
private theorem valid3840 : RecordDataValid section14Catalog 5 (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3841 : RecordDataValid section14Catalog 5 (⟨231,(0),[5,6],[174],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3842 : RecordDataValid section14Catalog 5 (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3843 : RecordDataValid section14Catalog 5 (⟨231,(1),[5,6],[174],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3844 : RecordDataValid section14Catalog 5 (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3845 : RecordDataValid section14Catalog 5 (⟨231,(2),[5,6],[174],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3846 : RecordDataValid section14Catalog 5 (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3847 : RecordDataValid section14Catalog 5 (⟨231,(3),[5,6],[174],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3848 : RecordDataValid section14Catalog 5 (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3849 : RecordDataValid section14Catalog 5 (⟨231,(4),[5,6],[174],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3850 : RecordDataValid section14Catalog 5 (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3851 : RecordDataValid section14Catalog 5 (⟨231,(5),[5,6],[174],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3852 : RecordDataValid section14Catalog 5 (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3853 : RecordDataValid section14Catalog 5 (⟨231,(6),[5,6],[174],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3854 : RecordDataValid section14Catalog 5 (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3855 : RecordDataValid section14Catalog 5 (⟨231,(7),[5,6],[174],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3856 : RecordDataValid section14Catalog 5 (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3857 : RecordDataValid section14Catalog 5 (⟨231,(8),[5,6],[174],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3858 : RecordDataValid section14Catalog 5 (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3859 : RecordDataValid section14Catalog 5 (⟨231,(9),[5,6],[174],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3860 : RecordDataValid section14Catalog 5 (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3861 : RecordDataValid section14Catalog 5 (⟨231,(10),[5,6],[174],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3862 : RecordDataValid section14Catalog 5 (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3863 : RecordDataValid section14Catalog 5 (⟨231,(11),[5,6],[174],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3864 : RecordDataValid section14Catalog 5 (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3865 : RecordDataValid section14Catalog 5 (⟨231,(12),[5,6],[174],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3866 : RecordDataValid section14Catalog 5 (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3867 : RecordDataValid section14Catalog 5 (⟨231,(13),[5,6],[174],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3868 : RecordDataValid section14Catalog 5 (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3869 : RecordDataValid section14Catalog 5 (⟨231,(14),[5,6],[174],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3870 : RecordDataValid section14Catalog 5 (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3871 : RecordDataValid section14Catalog 5 (⟨231,(15),[5,6],[174],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3840_3872 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3840).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3840).take 32 = [⟨231,(0),[1,2,5,6,13,14],[170],830⟩,⟨231,(0),[5,6],[174],830⟩,⟨231,(1),[1,2,5,6,13,14],[170],831⟩,⟨231,(1),[5,6],[174],831⟩,⟨231,(2),[1,2,5,6,13,14],[170],832⟩,⟨231,(2),[5,6],[174],832⟩,⟨231,(3),[1,2,5,6,13,14],[170],833⟩,⟨231,(3),[5,6],[174],833⟩,⟨231,(4),[1,2,5,6,13,14],[170],830⟩,⟨231,(4),[5,6],[174],830⟩,⟨231,(5),[1,2,5,6,13,14],[170],831⟩,⟨231,(5),[5,6],[174],831⟩,⟨231,(6),[1,2,5,6,13,14],[170],832⟩,⟨231,(6),[5,6],[174],832⟩,⟨231,(7),[1,2,5,6,13,14],[170],833⟩,⟨231,(7),[5,6],[174],833⟩,⟨231,(8),[1,2,5,6,13,14],[170],834⟩,⟨231,(8),[5,6],[174],834⟩,⟨231,(9),[1,2,5,6,13,14],[170],835⟩,⟨231,(9),[5,6],[174],835⟩,⟨231,(10),[1,2,5,6,13,14],[170],836⟩,⟨231,(10),[5,6],[174],836⟩,⟨231,(11),[1,2,5,6,13,14],[170],837⟩,⟨231,(11),[5,6],[174],837⟩,⟨231,(12),[1,2,5,6,13,14],[170],838⟩,⟨231,(12),[5,6],[174],838⟩,⟨231,(13),[1,2,5,6,13,14],[170],839⟩,⟨231,(13),[5,6],[174],839⟩,⟨231,(14),[1,2,5,6,13,14],[170],838⟩,⟨231,(14),[5,6],[174],838⟩,⟨231,(15),[1,2,5,6,13,14],[170],840⟩,⟨231,(15),[5,6],[174],840⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3840
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3841
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3842
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3843
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3844
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3845
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3846
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3847
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3848
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3849
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3850
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3851
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3852
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3853
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3854
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3855
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3856
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3857
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3858
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3859
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3860
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3861
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3862
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3863
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3864
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3865
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3866
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3867
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3868
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3869
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3870
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3871
end Section14Records_5_3840_3872

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3840_3872


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3872_3904
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3872_3904
private theorem valid3872 : RecordDataValid section14Catalog 5 (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3873 : RecordDataValid section14Catalog 5 (⟨231,(16),[5,6],[174],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3874 : RecordDataValid section14Catalog 5 (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3875 : RecordDataValid section14Catalog 5 (⟨231,(17),[5,6],[174],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3876 : RecordDataValid section14Catalog 5 (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3877 : RecordDataValid section14Catalog 5 (⟨231,(18),[5,6],[174],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3878 : RecordDataValid section14Catalog 5 (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3879 : RecordDataValid section14Catalog 5 (⟨231,(19),[5,6],[174],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3880 : RecordDataValid section14Catalog 5 (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3881 : RecordDataValid section14Catalog 5 (⟨232,(0),[5,6],[174],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3882 : RecordDataValid section14Catalog 5 (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3883 : RecordDataValid section14Catalog 5 (⟨232,(1),[5,6],[174],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3884 : RecordDataValid section14Catalog 5 (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3885 : RecordDataValid section14Catalog 5 (⟨232,(2),[5,6],[174],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3886 : RecordDataValid section14Catalog 5 (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3887 : RecordDataValid section14Catalog 5 (⟨232,(3),[5,6],[174],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3888 : RecordDataValid section14Catalog 5 (⟨232,(4),[1,5,6,13],[170],848⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3889 : RecordDataValid section14Catalog 5 (⟨232,(4),[5,6],[174],1069⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1069,[3,5,6,7],1073⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3890 : RecordDataValid section14Catalog 5 (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3891 : RecordDataValid section14Catalog 5 (⟨232,(5),[5,6],[174],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3892 : RecordDataValid section14Catalog 5 (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3893 : RecordDataValid section14Catalog 5 (⟨232,(6),[5,6],[174],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3894 : RecordDataValid section14Catalog 5 (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3895 : RecordDataValid section14Catalog 5 (⟨232,(7),[5,6],[174],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3896 : RecordDataValid section14Catalog 5 (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3897 : RecordDataValid section14Catalog 5 (⟨232,(8),[5,6],[174],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3898 : RecordDataValid section14Catalog 5 (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨853,[1,2,3,5,6,7,10,11,13,14,15],854⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3899 : RecordDataValid section14Catalog 5 (⟨232,(9),[5,6],[174],1070⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1070,[3,5,6,7],1074⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3900 : RecordDataValid section14Catalog 5 (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3901 : RecordDataValid section14Catalog 5 (⟨232,(10),[5,6],[174],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3902 : RecordDataValid section14Catalog 5 (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3903 : RecordDataValid section14Catalog 5 (⟨232,(11),[5,6],[174],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3872_3904 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3872).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3872).take 32 = [⟨231,(16),[1,2,5,6,13,14],[170],841⟩,⟨231,(16),[5,6],[174],841⟩,⟨231,(17),[1,2,5,6,13,14],[170],842⟩,⟨231,(17),[5,6],[174],842⟩,⟨231,(18),[1,2,5,6,13,14],[170],841⟩,⟨231,(18),[5,6],[174],841⟩,⟨231,(19),[1,2,5,6,13,14],[170],843⟩,⟨231,(19),[5,6],[174],843⟩,⟨232,(0),[1,2,5,6,13,14],[170],844⟩,⟨232,(0),[5,6],[174],844⟩,⟨232,(1),[1,2,5,6,13,14],[170],845⟩,⟨232,(1),[5,6],[174],845⟩,⟨232,(2),[1,2,5,6,13,14],[170],846⟩,⟨232,(2),[5,6],[174],846⟩,⟨232,(3),[1,2,5,6,13,14],[170],847⟩,⟨232,(3),[5,6],[174],847⟩,⟨232,(4),[1,5,6,13],[170],848⟩,⟨232,(4),[5,6],[174],1069⟩,⟨232,(5),[1,2,5,6,13,14],[170],849⟩,⟨232,(5),[5,6],[174],849⟩,⟨232,(6),[1,2,5,6,13,14],[170],850⟩,⟨232,(6),[5,6],[174],850⟩,⟨232,(7),[1,2,5,6,13,14],[170],851⟩,⟨232,(7),[5,6],[174],851⟩,⟨232,(8),[1,2,5,6,13,14],[170],852⟩,⟨232,(8),[5,6],[174],852⟩,⟨232,(9),[1,2,5,6,13,14],[170],853⟩,⟨232,(9),[5,6],[174],1070⟩,⟨232,(10),[1,2,5,6,13,14],[170],844⟩,⟨232,(10),[5,6],[174],844⟩,⟨232,(11),[1,2,5,6,13,14],[170],854⟩,⟨232,(11),[5,6],[174],854⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3872
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3873
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3874
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3875
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3876
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3877
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3878
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3879
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3880
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3881
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3882
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3883
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3884
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3885
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3886
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3887
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3888
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3889
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3890
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3891
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3892
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3893
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3894
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3895
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3896
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3897
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3898
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3899
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3900
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3901
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3902
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3903
end Section14Records_5_3872_3904

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3872_3904

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3840).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3840 3872 3904 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3840_3872 hnum) (Freiman.workReverse20260919_s0005_records_3872_3904 hnum))

#print axioms solution
