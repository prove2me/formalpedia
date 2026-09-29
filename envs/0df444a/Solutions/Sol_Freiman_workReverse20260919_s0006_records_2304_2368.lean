-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2304_2368
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:13:51.697918+00:00
-- url     : https://prove2.me/submissions/fb15b489-1de3-4667-9128-5897021026ee

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2304_2336
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2304_2336
private theorem valid2304 : RecordDataValid section14Catalog 6 (⟨157,(21),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2305 : RecordDataValid section14Catalog 6 (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2306 : RecordDataValid section14Catalog 6 (⟨157,(22),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2307 : RecordDataValid section14Catalog 6 (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2308 : RecordDataValid section14Catalog 6 (⟨157,(23),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2309 : RecordDataValid section14Catalog 6 (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2310 : RecordDataValid section14Catalog 6 (⟨157,(24),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2311 : RecordDataValid section14Catalog 6 (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2312 : RecordDataValid section14Catalog 6 (⟨160,(0),[5,6],[174],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2313 : RecordDataValid section14Catalog 6 (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2314 : RecordDataValid section14Catalog 6 (⟨160,(1),[5,6],[174],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2315 : RecordDataValid section14Catalog 6 (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2316 : RecordDataValid section14Catalog 6 (⟨160,(2),[5,6],[174],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2317 : RecordDataValid section14Catalog 6 (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2318 : RecordDataValid section14Catalog 6 (⟨160,(3),[5,6],[174],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2319 : RecordDataValid section14Catalog 6 (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2320 : RecordDataValid section14Catalog 6 (⟨160,(4),[5,6],[174],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2321 : RecordDataValid section14Catalog 6 (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2322 : RecordDataValid section14Catalog 6 (⟨160,(5),[5,6],[174],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2323 : RecordDataValid section14Catalog 6 (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2324 : RecordDataValid section14Catalog 6 (⟨160,(6),[5,6],[174],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2325 : RecordDataValid section14Catalog 6 (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2326 : RecordDataValid section14Catalog 6 (⟨160,(7),[5,6],[174],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2327 : RecordDataValid section14Catalog 6 (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2328 : RecordDataValid section14Catalog 6 (⟨160,(8),[5,6],[174],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2329 : RecordDataValid section14Catalog 6 (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2330 : RecordDataValid section14Catalog 6 (⟨160,(9),[5,6],[174],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2331 : RecordDataValid section14Catalog 6 (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2332 : RecordDataValid section14Catalog 6 (⟨160,(10),[5,6],[174],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2333 : RecordDataValid section14Catalog 6 (⟨160,(11),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2334 : RecordDataValid section14Catalog 6 (⟨160,(11),[5,6],[174],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2335 : RecordDataValid section14Catalog 6 (⟨160,(12),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2304_2336 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2304).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2304).take 32 = [⟨157,(21),[5,6],[174],294⟩,⟨157,(22),[1,2,5,6,13,14],[170],399⟩,⟨157,(22),[5,6],[174],294⟩,⟨157,(23),[1,2,5,6,13,14],[170],399⟩,⟨157,(23),[5,6],[174],294⟩,⟨157,(24),[1,2,5,6,13,14],[170],399⟩,⟨157,(24),[5,6],[174],294⟩,⟨160,(0),[1,2,5,6,13,14],[170],638⟩,⟨160,(0),[5,6],[174],638⟩,⟨160,(1),[1,2,5,6,13,14],[170],639⟩,⟨160,(1),[5,6],[174],639⟩,⟨160,(2),[1,2,5,6,13,14],[170],640⟩,⟨160,(2),[5,6],[174],640⟩,⟨160,(3),[1,2,5,6,13,14],[170],641⟩,⟨160,(3),[5,6],[174],641⟩,⟨160,(4),[1,2,5,6,13,14],[170],638⟩,⟨160,(4),[5,6],[174],638⟩,⟨160,(5),[1,2,5,6,13,14],[170],639⟩,⟨160,(5),[5,6],[174],639⟩,⟨160,(6),[1,2,5,6,13,14],[170],642⟩,⟨160,(6),[5,6],[174],642⟩,⟨160,(7),[1,2,5,6,13,14],[170],641⟩,⟨160,(7),[5,6],[174],641⟩,⟨160,(8),[1,2,5,6,13,14],[170],638⟩,⟨160,(8),[5,6],[174],638⟩,⟨160,(9),[1,2,5,6,13,14],[170],639⟩,⟨160,(9),[5,6],[174],639⟩,⟨160,(10),[1,2,5,6,13,14],[170],640⟩,⟨160,(10),[5,6],[174],640⟩,⟨160,(11),[1,2,5,6,13,14],[170],641⟩,⟨160,(11),[5,6],[174],641⟩,⟨160,(12),[1,2,5,6,13,14],[170],638⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2304
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2305
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2306
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2307
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2308
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2309
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2310
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2311
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2312
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2313
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2314
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2315
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2316
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2317
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2318
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2319
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2320
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2321
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2322
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2323
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2324
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2325
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2326
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2327
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2328
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2329
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2330
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2331
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2332
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2333
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2334
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2335
end Section14Records_6_2304_2336

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2304_2336


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2336_2368
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2336_2368
private theorem valid2336 : RecordDataValid section14Catalog 6 (⟨160,(12),[5,6],[174],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2337 : RecordDataValid section14Catalog 6 (⟨160,(13),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2338 : RecordDataValid section14Catalog 6 (⟨160,(13),[5,6],[174],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2339 : RecordDataValid section14Catalog 6 (⟨160,(14),[1,2,5,6,13,14],[170],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2340 : RecordDataValid section14Catalog 6 (⟨160,(14),[5,6],[174],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2341 : RecordDataValid section14Catalog 6 (⟨160,(15),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2342 : RecordDataValid section14Catalog 6 (⟨160,(15),[5,6],[174],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2343 : RecordDataValid section14Catalog 6 (⟨163,(0),[1,2,5,6,13,14],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2344 : RecordDataValid section14Catalog 6 (⟨163,(0),[5,6],[174],965⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨965,[3,5,6,7],969⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2345 : RecordDataValid section14Catalog 6 (⟨163,(1),[1,2,5,6,13,14],[170],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2346 : RecordDataValid section14Catalog 6 (⟨163,(1),[5,6],[174],966⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨966,[3,5,6,7],970⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2347 : RecordDataValid section14Catalog 6 (⟨163,(2),[1,2,5,6,13,14],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2348 : RecordDataValid section14Catalog 6 (⟨163,(2),[5,6],[174],965⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨965,[3,5,6,7],969⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2349 : RecordDataValid section14Catalog 6 (⟨163,(3),[1,2,5,6,13,14],[170],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2350 : RecordDataValid section14Catalog 6 (⟨163,(3),[5,6],[174],967⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨967,[3,5,6,7],971⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2351 : RecordDataValid section14Catalog 6 (⟨163,(4),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2352 : RecordDataValid section14Catalog 6 (⟨163,(4),[5,6],[174],968⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨968,[3,5,6,7],972⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2353 : RecordDataValid section14Catalog 6 (⟨163,(5),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2354 : RecordDataValid section14Catalog 6 (⟨163,(5),[5,6],[174],968⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨968,[3,5,6,7],972⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2355 : RecordDataValid section14Catalog 6 (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2356 : RecordDataValid section14Catalog 6 (⟨163,(6),[5,6],[174],968⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨968,[3,5,6,7],972⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2357 : RecordDataValid section14Catalog 6 (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2358 : RecordDataValid section14Catalog 6 (⟨163,(7),[5,6],[174],968⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨968,[3,5,6,7],972⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2359 : RecordDataValid section14Catalog 6 (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2360 : RecordDataValid section14Catalog 6 (⟨163,(8),[5,6],[174],969⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨969,[3,5,6,7],973⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2361 : RecordDataValid section14Catalog 6 (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2362 : RecordDataValid section14Catalog 6 (⟨163,(9),[5,6],[174],969⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨969,[3,5,6,7],973⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2363 : RecordDataValid section14Catalog 6 (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2364 : RecordDataValid section14Catalog 6 (⟨163,(10),[5,6],[174],969⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨969,[3,5,6,7],973⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2365 : RecordDataValid section14Catalog 6 (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2366 : RecordDataValid section14Catalog 6 (⟨163,(11),[5,6],[174],969⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨969,[3,5,6,7],973⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2367 : RecordDataValid section14Catalog 6 (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2336_2368 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2336).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2336).take 32 = [⟨160,(12),[5,6],[174],638⟩,⟨160,(13),[1,2,5,6,13,14],[170],639⟩,⟨160,(13),[5,6],[174],639⟩,⟨160,(14),[1,2,5,6,13,14],[170],643⟩,⟨160,(14),[5,6],[174],643⟩,⟨160,(15),[1,2,5,6,13,14],[170],641⟩,⟨160,(15),[5,6],[174],641⟩,⟨163,(0),[1,2,5,6,13,14],[170],406⟩,⟨163,(0),[5,6],[174],965⟩,⟨163,(1),[1,2,5,6,13,14],[170],407⟩,⟨163,(1),[5,6],[174],966⟩,⟨163,(2),[1,2,5,6,13,14],[170],406⟩,⟨163,(2),[5,6],[174],965⟩,⟨163,(3),[1,2,5,6,13,14],[170],408⟩,⟨163,(3),[5,6],[174],967⟩,⟨163,(4),[1,2,5,6,13,14],[170],409⟩,⟨163,(4),[5,6],[174],968⟩,⟨163,(5),[1,2,5,6,13,14],[170],409⟩,⟨163,(5),[5,6],[174],968⟩,⟨163,(6),[1,2,5,6,13,14],[170],409⟩,⟨163,(6),[5,6],[174],968⟩,⟨163,(7),[1,2,5,6,13,14],[170],409⟩,⟨163,(7),[5,6],[174],968⟩,⟨163,(8),[1,2,5,6,13,14],[170],410⟩,⟨163,(8),[5,6],[174],969⟩,⟨163,(9),[1,2,5,6,13,14],[170],410⟩,⟨163,(9),[5,6],[174],969⟩,⟨163,(10),[1,2,5,6,13,14],[170],410⟩,⟨163,(10),[5,6],[174],969⟩,⟨163,(11),[1,2,5,6,13,14],[170],410⟩,⟨163,(11),[5,6],[174],969⟩,⟨163,(12),[1,2,5,6,13,14],[170],411⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2336
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2337
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2338
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2339
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2340
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2341
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2342
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2343
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2344
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2345
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2346
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2347
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2348
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2349
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2350
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2351
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2352
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2353
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2354
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2355
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2356
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2357
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2358
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2359
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2360
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2361
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2362
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2363
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2364
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2365
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2366
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2367
end Section14Records_6_2336_2368

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2336_2368

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2304).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2304 2336 2368 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2304_2336 hnum) (Freiman.workReverse20260919_s0006_records_2336_2368 hnum))

#print axioms solution
