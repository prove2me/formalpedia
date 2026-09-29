-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3328_3392
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:19:47.389519+00:00
-- url     : https://prove2.me/submissions/7a352eef-133f-49e3-a3ce-442d5b6e3ed6

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3328_3360
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3328_3360
private theorem valid3328 : RecordDataValid section14Catalog 1 (⟨202,(6),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3329 : RecordDataValid section14Catalog 1 (⟨202,(7),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3330 : RecordDataValid section14Catalog 1 (⟨202,(8),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3331 : RecordDataValid section14Catalog 1 (⟨202,(9),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3332 : RecordDataValid section14Catalog 1 (⟨202,(10),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3333 : RecordDataValid section14Catalog 1 (⟨202,(11),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3334 : RecordDataValid section14Catalog 1 (⟨202,(12),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3335 : RecordDataValid section14Catalog 1 (⟨202,(13),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3336 : RecordDataValid section14Catalog 1 (⟨202,(14),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3337 : RecordDataValid section14Catalog 1 (⟨202,(15),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3338 : RecordDataValid section14Catalog 1 (⟨202,(16),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3339 : RecordDataValid section14Catalog 1 (⟨202,(17),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3340 : RecordDataValid section14Catalog 1 (⟨202,(18),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3341 : RecordDataValid section14Catalog 1 (⟨202,(19),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3342 : RecordDataValid section14Catalog 1 (⟨202,(20),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3343 : RecordDataValid section14Catalog 1 (⟨202,(21),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3344 : RecordDataValid section14Catalog 1 (⟨202,(22),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3345 : RecordDataValid section14Catalog 1 (⟨202,(23),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3346 : RecordDataValid section14Catalog 1 (⟨202,(24),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3347 : RecordDataValid section14Catalog 1 (⟨205,(0),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3348 : RecordDataValid section14Catalog 1 (⟨205,(1),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3349 : RecordDataValid section14Catalog 1 (⟨205,(2),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3350 : RecordDataValid section14Catalog 1 (⟨205,(3),[1,2,5,6,13,14],[170],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3351 : RecordDataValid section14Catalog 1 (⟨205,(4),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3352 : RecordDataValid section14Catalog 1 (⟨205,(5),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3353 : RecordDataValid section14Catalog 1 (⟨205,(6),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3354 : RecordDataValid section14Catalog 1 (⟨205,(7),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3355 : RecordDataValid section14Catalog 1 (⟨205,(8),[1,2,5,6,13,14],[170],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3356 : RecordDataValid section14Catalog 1 (⟨205,(9),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3357 : RecordDataValid section14Catalog 1 (⟨205,(10),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3358 : RecordDataValid section14Catalog 1 (⟨205,(11),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3359 : RecordDataValid section14Catalog 1 (⟨205,(12),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3328_3360 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3328).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3328).take 32 = [⟨202,(6),[1,2,5,6,13,14],[170],468⟩,⟨202,(7),[1,2,5,6,13,14],[170],467⟩,⟨202,(8),[1,2,5,6,13,14],[170],469⟩,⟨202,(9),[1,2,5,6,13,14],[170],470⟩,⟨202,(10),[1,2,5,6,13,14],[170],471⟩,⟨202,(11),[1,2,5,6,13,14],[170],471⟩,⟨202,(12),[1,2,5,6,13,14],[170],471⟩,⟨202,(13),[1,2,5,6,13,14],[170],471⟩,⟨202,(14),[1,2,5,6,13,14],[170],470⟩,⟨202,(15),[1,2,5,6,13,14],[170],472⟩,⟨202,(16),[1,2,5,6,13,14],[170],472⟩,⟨202,(17),[1,2,5,6,13,14],[170],472⟩,⟨202,(18),[1,2,5,6,13,14],[170],472⟩,⟨202,(19),[1,2,5,6,13,14],[170],472⟩,⟨202,(20),[1,2,5,6,13,14],[170],473⟩,⟨202,(21),[1,2,5,6,13,14],[170],473⟩,⟨202,(22),[1,2,5,6,13,14],[170],473⟩,⟨202,(23),[1,2,5,6,13,14],[170],473⟩,⟨202,(24),[1,2,5,6,13,14],[170],473⟩,⟨205,(0),[1,2,5,6,13,14],[170],711⟩,⟨205,(1),[1,2,5,6,13,14],[170],711⟩,⟨205,(2),[1,2,5,6,13,14],[170],711⟩,⟨205,(3),[1,2,5,6,13,14],[170],712⟩,⟨205,(4),[1,2,5,6,13,14],[170],711⟩,⟨205,(5),[1,2,5,6,13,14],[170],713⟩,⟨205,(6),[1,2,5,6,13,14],[170],713⟩,⟨205,(7),[1,2,5,6,13,14],[170],713⟩,⟨205,(8),[1,2,5,6,13,14],[170],714⟩,⟨205,(9),[1,2,5,6,13,14],[170],713⟩,⟨205,(10),[1,2,5,6,13,14],[170],715⟩,⟨205,(11),[1,2,5,6,13,14],[170],716⟩,⟨205,(12),[1,2,5,6,13,14],[170],717⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3328
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3329
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3330
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3331
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3332
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3333
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3334
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3335
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3336
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3337
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3338
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3339
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3340
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3341
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3342
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3343
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3344
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3345
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3346
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3347
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3348
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3349
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3350
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3351
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3352
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3353
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3354
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3355
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3356
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3357
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3358
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3359
end Section14Records_1_3328_3360

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3328_3360


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3360_3392
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3360_3392
private theorem valid3360 : RecordDataValid section14Catalog 1 (⟨205,(13),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3361 : RecordDataValid section14Catalog 1 (⟨205,(14),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3362 : RecordDataValid section14Catalog 1 (⟨205,(15),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3363 : RecordDataValid section14Catalog 1 (⟨205,(16),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3364 : RecordDataValid section14Catalog 1 (⟨205,(17),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3365 : RecordDataValid section14Catalog 1 (⟨205,(18),[1,2,5,6,13,14],[170],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3366 : RecordDataValid section14Catalog 1 (⟨205,(19),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3367 : RecordDataValid section14Catalog 1 (⟨205,(20),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3368 : RecordDataValid section14Catalog 1 (⟨205,(21),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3369 : RecordDataValid section14Catalog 1 (⟨205,(22),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3370 : RecordDataValid section14Catalog 1 (⟨205,(23),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3371 : RecordDataValid section14Catalog 1 (⟨205,(24),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3372 : RecordDataValid section14Catalog 1 (⟨207,(0),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3373 : RecordDataValid section14Catalog 1 (⟨207,(1),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3374 : RecordDataValid section14Catalog 1 (⟨207,(2),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3375 : RecordDataValid section14Catalog 1 (⟨207,(3),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3376 : RecordDataValid section14Catalog 1 (⟨207,(4),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3377 : RecordDataValid section14Catalog 1 (⟨207,(5),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3378 : RecordDataValid section14Catalog 1 (⟨207,(6),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3379 : RecordDataValid section14Catalog 1 (⟨207,(7),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3380 : RecordDataValid section14Catalog 1 (⟨207,(8),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3381 : RecordDataValid section14Catalog 1 (⟨207,(9),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3382 : RecordDataValid section14Catalog 1 (⟨207,(10),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3383 : RecordDataValid section14Catalog 1 (⟨207,(11),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3384 : RecordDataValid section14Catalog 1 (⟨207,(12),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3385 : RecordDataValid section14Catalog 1 (⟨207,(13),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3386 : RecordDataValid section14Catalog 1 (⟨207,(14),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3387 : RecordDataValid section14Catalog 1 (⟨207,(15),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3388 : RecordDataValid section14Catalog 1 (⟨207,(16),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3389 : RecordDataValid section14Catalog 1 (⟨207,(17),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3390 : RecordDataValid section14Catalog 1 (⟨207,(18),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3391 : RecordDataValid section14Catalog 1 (⟨207,(19),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3360_3392 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3360).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3360).take 32 = [⟨205,(13),[1,2,5,6,13,14],[170],718⟩,⟨205,(14),[1,2,5,6,13,14],[170],719⟩,⟨205,(15),[1,2,5,6,13,14],[170],715⟩,⟨205,(16),[1,2,5,6,13,14],[170],720⟩,⟨205,(17),[1,2,5,6,13,14],[170],720⟩,⟨205,(18),[1,2,5,6,13,14],[170],721⟩,⟨205,(19),[1,2,5,6,13,14],[170],720⟩,⟨205,(20),[1,2,5,6,13,14],[170],715⟩,⟨205,(21),[1,2,5,6,13,14],[170],716⟩,⟨205,(22),[1,2,5,6,13,14],[170],717⟩,⟨205,(23),[1,2,5,6,13,14],[170],718⟩,⟨205,(24),[1,2,5,6,13,14],[170],719⟩,⟨207,(0),[1,2,5,6,13,14],[170],481⟩,⟨207,(1),[1,2,5,6,13,14],[170],482⟩,⟨207,(2),[1,2,5,6,13,14],[170],481⟩,⟨207,(3),[1,2,5,6,13,14],[170],483⟩,⟨207,(4),[1,2,5,6,13,14],[170],484⟩,⟨207,(5),[1,2,5,6,13,14],[170],481⟩,⟨207,(6),[1,2,5,6,13,14],[170],482⟩,⟨207,(7),[1,2,5,6,13,14],[170],481⟩,⟨207,(8),[1,2,5,6,13,14],[170],483⟩,⟨207,(9),[1,2,5,6,13,14],[170],484⟩,⟨207,(10),[1,2,5,6,13,14],[170],485⟩,⟨207,(11),[1,2,5,6,13,14],[170],485⟩,⟨207,(12),[1,2,5,6,13,14],[170],485⟩,⟨207,(13),[1,2,5,6,13,14],[170],485⟩,⟨207,(14),[1,2,5,6,13,14],[170],484⟩,⟨207,(15),[1,2,5,6,13,14],[170],486⟩,⟨207,(16),[1,2,5,6,13,14],[170],486⟩,⟨207,(17),[1,2,5,6,13,14],[170],486⟩,⟨207,(18),[1,2,5,6,13,14],[170],486⟩,⟨207,(19),[1,2,5,6,13,14],[170],486⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3360
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3361
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3362
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3363
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3364
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3365
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3366
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3367
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3368
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3369
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3370
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3371
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3372
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3373
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3374
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3375
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3376
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3377
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3378
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3379
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3380
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3381
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3382
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3383
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3384
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3385
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3386
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3387
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3388
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3389
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3390
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3391
end Section14Records_1_3360_3392

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3360_3392

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3328).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3328 3360 3392 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3328_3360 hnum) (Freiman.workReverse20260919_s0001_records_3360_3392 hnum))

#print axioms solution
