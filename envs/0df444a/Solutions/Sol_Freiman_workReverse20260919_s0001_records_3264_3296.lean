-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3264_3296
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:08:41.192462+00:00
-- url     : https://prove2.me/submissions/e3e71f88-7da7-43dd-a4a2-d465459819f8

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
namespace Section14Records_1_3264_3296
private theorem valid3264 : RecordDataValid section14Catalog 1 (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3265 : RecordDataValid section14Catalog 1 (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3266 : RecordDataValid section14Catalog 1 (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3267 : RecordDataValid section14Catalog 1 (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3268 : RecordDataValid section14Catalog 1 (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3269 : RecordDataValid section14Catalog 1 (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3270 : RecordDataValid section14Catalog 1 (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3271 : RecordDataValid section14Catalog 1 (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3272 : RecordDataValid section14Catalog 1 (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3273 : RecordDataValid section14Catalog 1 (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3274 : RecordDataValid section14Catalog 1 (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3275 : RecordDataValid section14Catalog 1 (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3276 : RecordDataValid section14Catalog 1 (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3277 : RecordDataValid section14Catalog 1 (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3278 : RecordDataValid section14Catalog 1 (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3279 : RecordDataValid section14Catalog 1 (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3280 : RecordDataValid section14Catalog 1 (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3281 : RecordDataValid section14Catalog 1 (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3282 : RecordDataValid section14Catalog 1 (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3283 : RecordDataValid section14Catalog 1 (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3284 : RecordDataValid section14Catalog 1 (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3285 : RecordDataValid section14Catalog 1 (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3286 : RecordDataValid section14Catalog 1 (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3287 : RecordDataValid section14Catalog 1 (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3288 : RecordDataValid section14Catalog 1 (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3289 : RecordDataValid section14Catalog 1 (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3290 : RecordDataValid section14Catalog 1 (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3291 : RecordDataValid section14Catalog 1 (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3292 : RecordDataValid section14Catalog 1 (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3293 : RecordDataValid section14Catalog 1 (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3294 : RecordDataValid section14Catalog 1 (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3295 : RecordDataValid section14Catalog 1 (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3264).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3264).take 32 = [⟨195,(2),[1,2,5,6,13,14],[170],698⟩,⟨195,(3),[1,2,5,6,13,14],[170],698⟩,⟨195,(4),[1,2,5,6,13,14],[170],699⟩,⟨195,(5),[1,2,5,6,13,14],[170],700⟩,⟨195,(6),[1,2,5,6,13,14],[170],699⟩,⟨195,(7),[1,2,5,6,13,14],[170],701⟩,⟨195,(8),[1,2,5,6,13,14],[170],702⟩,⟨195,(9),[1,2,5,6,13,14],[170],703⟩,⟨197,(0),[1,2,5,6,13,14],[170],453⟩,⟨197,(1),[1,2,5,6,13,14],[170],454⟩,⟨197,(2),[1,2,5,6,13,14],[170],453⟩,⟨197,(3),[1,2,5,6,13,14],[170],455⟩,⟨197,(4),[1,2,5,6,13,14],[170],456⟩,⟨197,(5),[1,2,5,6,13,14],[170],453⟩,⟨197,(6),[1,2,5,6,13,14],[170],454⟩,⟨197,(7),[1,2,5,6,13,14],[170],453⟩,⟨197,(8),[1,2,5,6,13,14],[170],455⟩,⟨197,(9),[1,2,5,6,13,14],[170],456⟩,⟨197,(10),[1,2,5,6,13,14],[170],457⟩,⟨197,(11),[1,2,5,6,13,14],[170],457⟩,⟨197,(12),[1,2,5,6,13,14],[170],457⟩,⟨197,(13),[1,2,5,6,13,14],[170],457⟩,⟨197,(14),[1,2,5,6,13,14],[170],456⟩,⟨197,(15),[1,2,5,6,13,14],[170],458⟩,⟨197,(16),[1,2,5,6,13,14],[170],458⟩,⟨197,(17),[1,2,5,6,13,14],[170],458⟩,⟨197,(18),[1,2,5,6,13,14],[170],458⟩,⟨197,(19),[1,2,5,6,13,14],[170],458⟩,⟨197,(20),[1,2,5,6,13,14],[170],459⟩,⟨197,(21),[1,2,5,6,13,14],[170],459⟩,⟨197,(22),[1,2,5,6,13,14],[170],459⟩,⟨197,(23),[1,2,5,6,13,14],[170],459⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3264
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3265
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3266
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3267
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3268
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3269
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3270
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3271
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3272
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3273
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3274
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3275
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3276
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3277
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3278
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3279
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3280
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3281
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3282
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3283
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3284
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3285
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3286
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3287
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3288
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3289
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3290
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3291
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3292
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3293
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3294
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3295
end Section14Records_1_3264_3296

#print axioms solution
