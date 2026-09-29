-- Prove2me | solution 1 for Freiman.section14_s0002_records_0288_0320
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T05:56:07.160409+00:00
-- url     : https://prove2.me/submissions/efaf7274-69e1-459f-a013-b02fd776e256

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
namespace Section14Records_2_288_320
private theorem valid288 : RecordDataValid section14Catalog 2 (⟨18,(20),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid289 : RecordDataValid section14Catalog 2 (⟨18,(20),[2,6],[130],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid290 : RecordDataValid section14Catalog 2 (⟨18,(20),[2,14],[146,147],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid291 : RecordDataValid section14Catalog 2 (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid292 : RecordDataValid section14Catalog 2 (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid293 : RecordDataValid section14Catalog 2 (⟨18,(21),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid294 : RecordDataValid section14Catalog 2 (⟨18,(21),[2,6],[130],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid295 : RecordDataValid section14Catalog 2 (⟨18,(21),[2,14],[146,147],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid296 : RecordDataValid section14Catalog 2 (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid297 : RecordDataValid section14Catalog 2 (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid298 : RecordDataValid section14Catalog 2 (⟨18,(22),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid299 : RecordDataValid section14Catalog 2 (⟨18,(22),[2,6],[130],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid300 : RecordDataValid section14Catalog 2 (⟨18,(22),[2,14],[146,147],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid301 : RecordDataValid section14Catalog 2 (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid302 : RecordDataValid section14Catalog 2 (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid303 : RecordDataValid section14Catalog 2 (⟨18,(23),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid304 : RecordDataValid section14Catalog 2 (⟨18,(23),[2,6],[130],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid305 : RecordDataValid section14Catalog 2 (⟨18,(23),[2,14],[146,147],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid306 : RecordDataValid section14Catalog 2 (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid307 : RecordDataValid section14Catalog 2 (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨130,[1,2,5,6,13,14],130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid308 : RecordDataValid section14Catalog 2 (⟨18,(24),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid309 : RecordDataValid section14Catalog 2 (⟨18,(24),[2,6],[130],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid310 : RecordDataValid section14Catalog 2 (⟨18,(24),[2,14],[146,147],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid311 : RecordDataValid section14Catalog 2 (⟨20,(0),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid312 : RecordDataValid section14Catalog 2 (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid313 : RecordDataValid section14Catalog 2 (⟨20,(0),[1,2,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid314 : RecordDataValid section14Catalog 2 (⟨20,(0),[1,2,13,14],[190],209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨209,[1,2,3,4,13,14,15,16],209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid315 : RecordDataValid section14Catalog 2 (⟨20,(1),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid316 : RecordDataValid section14Catalog 2 (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid317 : RecordDataValid section14Catalog 2 (⟨20,(1),[1,2,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid318 : RecordDataValid section14Catalog 2 (⟨20,(1),[1,2,13,14],[190],210⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨210,[1,2,3,4,13,14,15,16],210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid319 : RecordDataValid section14Catalog 2 (⟨20,(2),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 288).take 32 = [⟨18,(20),[1,2,13,14],[190],3⟩,⟨18,(20),[2,6],[130],108⟩,⟨18,(20),[2,14],[146,147],108⟩,⟨18,(21),[1,2,5,6,13,14],[131],109⟩,⟨18,(21),[1,2,5,6,13,14],[150],128⟩,⟨18,(21),[1,2,13,14],[190],3⟩,⟨18,(21),[2,6],[130],109⟩,⟨18,(21),[2,14],[146,147],109⟩,⟨18,(22),[1,2,5,6,13,14],[131],110⟩,⟨18,(22),[1,2,5,6,13,14],[150],129⟩,⟨18,(22),[1,2,13,14],[190],3⟩,⟨18,(22),[2,6],[130],110⟩,⟨18,(22),[2,14],[146,147],110⟩,⟨18,(23),[1,2,5,6,13,14],[131],109⟩,⟨18,(23),[1,2,5,6,13,14],[150],128⟩,⟨18,(23),[1,2,13,14],[190],3⟩,⟨18,(23),[2,6],[130],109⟩,⟨18,(23),[2,14],[146,147],109⟩,⟨18,(24),[1,2,5,6,13,14],[131],111⟩,⟨18,(24),[1,2,5,6,13,14],[150],130⟩,⟨18,(24),[1,2,13,14],[190],3⟩,⟨18,(24),[2,6],[130],111⟩,⟨18,(24),[2,14],[146,147],111⟩,⟨20,(0),[1,2,5,6],[130],3⟩,⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(0),[1,2,13,14],[147],3⟩,⟨20,(0),[1,2,13,14],[190],209⟩,⟨20,(1),[1,2,5,6],[130],3⟩,⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(1),[1,2,13,14],[147],3⟩,⟨20,(1),[1,2,13,14],[190],210⟩,⟨20,(2),[1,2,5,6],[130],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid288
  · exact recordValid_of_data section14Catalog 2 _ hnum valid289
  · exact recordValid_of_data section14Catalog 2 _ hnum valid290
  · exact recordValid_of_data section14Catalog 2 _ hnum valid291
  · exact recordValid_of_data section14Catalog 2 _ hnum valid292
  · exact recordValid_of_data section14Catalog 2 _ hnum valid293
  · exact recordValid_of_data section14Catalog 2 _ hnum valid294
  · exact recordValid_of_data section14Catalog 2 _ hnum valid295
  · exact recordValid_of_data section14Catalog 2 _ hnum valid296
  · exact recordValid_of_data section14Catalog 2 _ hnum valid297
  · exact recordValid_of_data section14Catalog 2 _ hnum valid298
  · exact recordValid_of_data section14Catalog 2 _ hnum valid299
  · exact recordValid_of_data section14Catalog 2 _ hnum valid300
  · exact recordValid_of_data section14Catalog 2 _ hnum valid301
  · exact recordValid_of_data section14Catalog 2 _ hnum valid302
  · exact recordValid_of_data section14Catalog 2 _ hnum valid303
  · exact recordValid_of_data section14Catalog 2 _ hnum valid304
  · exact recordValid_of_data section14Catalog 2 _ hnum valid305
  · exact recordValid_of_data section14Catalog 2 _ hnum valid306
  · exact recordValid_of_data section14Catalog 2 _ hnum valid307
  · exact recordValid_of_data section14Catalog 2 _ hnum valid308
  · exact recordValid_of_data section14Catalog 2 _ hnum valid309
  · exact recordValid_of_data section14Catalog 2 _ hnum valid310
  · exact recordValid_of_data section14Catalog 2 _ hnum valid311
  · exact recordValid_of_data section14Catalog 2 _ hnum valid312
  · exact recordValid_of_data section14Catalog 2 _ hnum valid313
  · exact recordValid_of_data section14Catalog 2 _ hnum valid314
  · exact recordValid_of_data section14Catalog 2 _ hnum valid315
  · exact recordValid_of_data section14Catalog 2 _ hnum valid316
  · exact recordValid_of_data section14Catalog 2 _ hnum valid317
  · exact recordValid_of_data section14Catalog 2 _ hnum valid318
  · exact recordValid_of_data section14Catalog 2 _ hnum valid319
end Section14Records_2_288_320

#print axioms solution
