-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_2304_2432
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:40:07.887703+00:00
-- url     : https://prove2.me/submissions/1d18c1bd-0789-45d3-8ee3-2dd09d0b92db

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2304_2336
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2304_2336
private theorem valid2304 : RecordDataValid section14Catalog 1 (⟨79,(1),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2305 : RecordDataValid section14Catalog 1 (⟨79,(2),[1,2],[190],364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨364,[1,2,3,4,5,6,7,8,9,10,11,12],365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2306 : RecordDataValid section14Catalog 1 (⟨79,(2),[1,2,5,6],[150],364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨364,[1,2,3,4,5,6,7,8,9,10,11,12],365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2307 : RecordDataValid section14Catalog 1 (⟨79,(3),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2308 : RecordDataValid section14Catalog 1 (⟨79,(4),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2309 : RecordDataValid section14Catalog 1 (⟨79,(5),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2310 : RecordDataValid section14Catalog 1 (⟨79,(6),[1,2],[190],365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨365,[1,2,4,5,6,8,9,10,12],366⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2311 : RecordDataValid section14Catalog 1 (⟨79,(6),[1,2,5,6],[150],365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨365,[1,2,4,5,6,8,9,10,12],366⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2312 : RecordDataValid section14Catalog 1 (⟨79,(7),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2313 : RecordDataValid section14Catalog 1 (⟨79,(8),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2314 : RecordDataValid section14Catalog 1 (⟨79,(9),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2315 : RecordDataValid section14Catalog 1 (⟨79,(10),[1,2,5,6],[150,190],339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨339,[1,2,4,5,6,8,9,10,12],340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2316 : RecordDataValid section14Catalog 1 (⟨79,(11),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2317 : RecordDataValid section14Catalog 1 (⟨79,(12),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2318 : RecordDataValid section14Catalog 1 (⟨79,(13),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2319 : RecordDataValid section14Catalog 1 (⟨79,(14),[1,2,5,6],[150,190],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2320 : RecordDataValid section14Catalog 1 (⟨79,(15),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2321 : RecordDataValid section14Catalog 1 (⟨79,(16),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2322 : RecordDataValid section14Catalog 1 (⟨79,(17),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2323 : RecordDataValid section14Catalog 1 (⟨79,(18),[1,2,5,6],[150,190],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2324 : RecordDataValid section14Catalog 1 (⟨79,(19),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2325 : RecordDataValid section14Catalog 1 (⟨80,(5),[1,2,5,6],[150],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2326 : RecordDataValid section14Catalog 1 (⟨80,(5),[1,2,5,6,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2327 : RecordDataValid section14Catalog 1 (⟨80,(7),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2328 : RecordDataValid section14Catalog 1 (⟨80,(7),[1,2,6,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2329 : RecordDataValid section14Catalog 1 (⟨80,(8),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2330 : RecordDataValid section14Catalog 1 (⟨80,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2331 : RecordDataValid section14Catalog 1 (⟨80,(9),[1,2],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2332 : RecordDataValid section14Catalog 1 (⟨80,(9),[1,2,5,6],[150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2333 : RecordDataValid section14Catalog 1 (⟨80,(15),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2334 : RecordDataValid section14Catalog 1 (⟨80,(15),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2335 : RecordDataValid section14Catalog 1 (⟨80,(16),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2304_2336 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2304).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2304).take 32 = [⟨79,(1),[1,2,5,6],[150,190],2⟩,⟨79,(2),[1,2],[190],364⟩,⟨79,(2),[1,2,5,6],[150],364⟩,⟨79,(3),[1,2,5,6],[150,190],101⟩,⟨79,(4),[1,2,5,6],[150,190],2⟩,⟨79,(5),[1,2,5,6],[150,190],2⟩,⟨79,(6),[1,2],[190],365⟩,⟨79,(6),[1,2,5,6],[150],365⟩,⟨79,(7),[1,2,5,6],[150,190],101⟩,⟨79,(8),[1,2,5,6],[150,190],2⟩,⟨79,(9),[1,2,5,6],[150,190],2⟩,⟨79,(10),[1,2,5,6],[150,190],339⟩,⟨79,(11),[1,2,5,6],[150,190],101⟩,⟨79,(12),[1,2,5,6],[150,190],2⟩,⟨79,(13),[1,2,5,6],[150,190],2⟩,⟨79,(14),[1,2,5,6],[150,190],286⟩,⟨79,(15),[1,2,5,6],[150,190],101⟩,⟨79,(16),[1,2,5,6],[150,190],2⟩,⟨79,(17),[1,2,5,6],[150,190],2⟩,⟨79,(18),[1,2,5,6],[150,190],287⟩,⟨79,(19),[1,2,5,6],[150,190],101⟩,⟨80,(5),[1,2,5,6],[150],105⟩,⟨80,(5),[1,2,5,6,14],[190],3⟩,⟨80,(7),[1,2,5,6],[150],3⟩,⟨80,(7),[1,2,6,14],[190],3⟩,⟨80,(8),[1,2,5,6],[150],3⟩,⟨80,(8),[1,2,5,6,13,14],[190],3⟩,⟨80,(9),[1,2],[190],3⟩,⟨80,(9),[1,2,5,6],[150],143⟩,⟨80,(15),[1,2,5,6],[150],3⟩,⟨80,(15),[1,2,5,6,13,14],[190],3⟩,⟨80,(16),[1,2,5,6],[150],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2304
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2305
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2306
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2307
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2308
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2309
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2310
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2311
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2312
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2313
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2314
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2315
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2316
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2317
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2318
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2319
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2320
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2321
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2322
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2323
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2324
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2325
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2326
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2327
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2328
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2329
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2330
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2331
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2332
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2333
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2334
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2335
end Section14Records_1_2304_2336

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2304_2336


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2336_2368
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2336_2368
private theorem valid2336 : RecordDataValid section14Catalog 1 (⟨80,(16),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2337 : RecordDataValid section14Catalog 1 (⟨80,(17),[1,2,5,6,13,14],[190],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2338 : RecordDataValid section14Catalog 1 (⟨80,(17),[1,2,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2339 : RecordDataValid section14Catalog 1 (⟨80,(19),[1,2],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2340 : RecordDataValid section14Catalog 1 (⟨80,(19),[1,2,5,6,13,14],[190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2341 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2342 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2343 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,9,10,13,14],[5],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2344 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2345 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2346 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2347 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2348 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2349 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[130,134],389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2350 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[146],390⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨390,[1,2,3,5,6,7,13,14,15],391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2351 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2352 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[150],392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨392,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2353 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[174],628⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨628,[1,2,3,5,6,7,13,14,15],629⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2354 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[186],629⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨629,[1,2,4,5,6,8,9,10,12,13,14,16],630⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2355 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2356 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2357 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,2,13,14],[131,135],389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2358 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,3,5,7,9,11,13,15],[0],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2359 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,5,6,13],[194,198],630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2360 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,5,9,13],[4],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2361 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,5,13],[16,20,40,44,56,60],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2362 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,5,13],[190],628⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨628,[1,2,3,5,6,7,13,14,15],629⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2363 : RecordDataValid section14Catalog 1 (⟨82,(-1),[1,5,13],[195,199,211,215,235,239,251,255],630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2364 : RecordDataValid section14Catalog 1 (⟨84,(0),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2365 : RecordDataValid section14Catalog 1 (⟨84,(1),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2366 : RecordDataValid section14Catalog 1 (⟨84,(2),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2367 : RecordDataValid section14Catalog 1 (⟨84,(3),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2336_2368 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2336).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2336).take 32 = [⟨80,(16),[1,2,5,6,13,14],[190],3⟩,⟨80,(17),[1,2,5,6,13,14],[190],48⟩,⟨80,(17),[1,2,6],[150],3⟩,⟨80,(19),[1,2],[150],3⟩,⟨80,(19),[1,2,5,6,13,14],[190],143⟩,⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩,⟨82,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨82,(-1),[1,2,5,6,9,10,13,14],[5],386⟩,⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨82,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨82,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],386⟩,⟨82,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],387⟩,⟨82,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],388⟩,⟨82,(-1),[1,2,5,6,13,14],[130,134],389⟩,⟨82,(-1),[1,2,5,6,13,14],[146],390⟩,⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩,⟨82,(-1),[1,2,5,6,13,14],[150],392⟩,⟨82,(-1),[1,2,5,6,13,14],[174],628⟩,⟨82,(-1),[1,2,5,6,13,14],[186],629⟩,⟨82,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],630⟩,⟨82,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨82,(-1),[1,2,13,14],[131,135],389⟩,⟨82,(-1),[1,3,5,7,9,11,13,15],[0],386⟩,⟨82,(-1),[1,5,6,13],[194,198],630⟩,⟨82,(-1),[1,5,9,13],[4],386⟩,⟨82,(-1),[1,5,13],[16,20,40,44,56,60],386⟩,⟨82,(-1),[1,5,13],[190],628⟩,⟨82,(-1),[1,5,13],[195,199,211,215,235,239,251,255],630⟩,⟨84,(0),[1,5,6,13],[170],3⟩,⟨84,(1),[1,5,6,13],[170],3⟩,⟨84,(2),[1,5,6,13],[170],3⟩,⟨84,(3),[1,5,6,13],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2336
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2337
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2338
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2339
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2340
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2341
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2342
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2343
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2344
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2345
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2346
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2347
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2348
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2349
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2350
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2351
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2352
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2353
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2354
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2355
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2356
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2357
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2358
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2359
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2360
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2361
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2362
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2363
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2364
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2365
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2366
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2367
end Section14Records_1_2336_2368

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2336_2368


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2368_2400
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2368_2400
private theorem valid2368 : RecordDataValid section14Catalog 1 (⟨84,(4),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2369 : RecordDataValid section14Catalog 1 (⟨84,(5),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2370 : RecordDataValid section14Catalog 1 (⟨84,(6),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2371 : RecordDataValid section14Catalog 1 (⟨84,(7),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2372 : RecordDataValid section14Catalog 1 (⟨84,(8),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2373 : RecordDataValid section14Catalog 1 (⟨84,(9),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2374 : RecordDataValid section14Catalog 1 (⟨84,(10),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2375 : RecordDataValid section14Catalog 1 (⟨84,(11),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2376 : RecordDataValid section14Catalog 1 (⟨84,(12),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2377 : RecordDataValid section14Catalog 1 (⟨84,(13),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2378 : RecordDataValid section14Catalog 1 (⟨84,(14),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2379 : RecordDataValid section14Catalog 1 (⟨84,(15),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2380 : RecordDataValid section14Catalog 1 (⟨84,(16),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2381 : RecordDataValid section14Catalog 1 (⟨84,(17),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2382 : RecordDataValid section14Catalog 1 (⟨84,(18),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2383 : RecordDataValid section14Catalog 1 (⟨84,(19),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2384 : RecordDataValid section14Catalog 1 (⟨84,(20),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2385 : RecordDataValid section14Catalog 1 (⟨84,(21),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2386 : RecordDataValid section14Catalog 1 (⟨84,(22),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2387 : RecordDataValid section14Catalog 1 (⟨84,(23),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2388 : RecordDataValid section14Catalog 1 (⟨84,(24),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2389 : RecordDataValid section14Catalog 1 (⟨86,(0),[1,5,6,13],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2390 : RecordDataValid section14Catalog 1 (⟨86,(1),[1,5,6,13],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2391 : RecordDataValid section14Catalog 1 (⟨86,(2),[1,5,6,13],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2392 : RecordDataValid section14Catalog 1 (⟨86,(3),[1,5,6,13],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2393 : RecordDataValid section14Catalog 1 (⟨86,(4),[1,5,6,13],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2394 : RecordDataValid section14Catalog 1 (⟨86,(5),[1,5,6,13],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2395 : RecordDataValid section14Catalog 1 (⟨86,(6),[1,5,6,13],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2396 : RecordDataValid section14Catalog 1 (⟨86,(7),[1,5,6,13],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2397 : RecordDataValid section14Catalog 1 (⟨86,(8),[1,5,6,13],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2398 : RecordDataValid section14Catalog 1 (⟨86,(9),[1,5,6,13],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2399 : RecordDataValid section14Catalog 1 (⟨86,(10),[1,5,6,13],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2368_2400 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2368).take 32 = [⟨84,(4),[1,5,6,13],[170],3⟩,⟨84,(5),[1,5,6,13],[170],3⟩,⟨84,(6),[1,5,6,13],[170],3⟩,⟨84,(7),[1,5,6,13],[170],3⟩,⟨84,(8),[1,5,6,13],[170],3⟩,⟨84,(9),[1,5,6,13],[170],3⟩,⟨84,(10),[1,5,6,13],[170],3⟩,⟨84,(11),[1,5,6,13],[170],3⟩,⟨84,(12),[1,5,6,13],[170],3⟩,⟨84,(13),[1,5,6,13],[170],3⟩,⟨84,(14),[1,5,6,13],[170],3⟩,⟨84,(15),[1,5,6,13],[170],3⟩,⟨84,(16),[1,5,6,13],[170],3⟩,⟨84,(17),[1,5,6,13],[170],3⟩,⟨84,(18),[1,5,6,13],[170],3⟩,⟨84,(19),[1,5,6,13],[170],3⟩,⟨84,(20),[1,5,6,13],[170],3⟩,⟨84,(21),[1,5,6,13],[170],3⟩,⟨84,(22),[1,5,6,13],[170],3⟩,⟨84,(23),[1,5,6,13],[170],3⟩,⟨84,(24),[1,5,6,13],[170],3⟩,⟨86,(0),[1,5,6,13],[170],10⟩,⟨86,(1),[1,5,6,13],[170],393⟩,⟨86,(2),[1,5,6,13],[170],394⟩,⟨86,(3),[1,5,6,13],[170],395⟩,⟨86,(4),[1,5,6,13],[170],396⟩,⟨86,(5),[1,5,6,13],[170],10⟩,⟨86,(6),[1,5,6,13],[170],393⟩,⟨86,(7),[1,5,6,13],[170],394⟩,⟨86,(8),[1,5,6,13],[170],395⟩,⟨86,(9),[1,5,6,13],[170],396⟩,⟨86,(10),[1,5,6,13],[170],18⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2368
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2369
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2370
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2371
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2372
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2373
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2374
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2375
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2376
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2377
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2378
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2379
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2380
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2381
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2382
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2383
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2384
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2385
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2386
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2387
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2388
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2389
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2390
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2391
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2392
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2393
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2394
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2395
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2396
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2397
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2398
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2399
end Section14Records_1_2368_2400

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2368_2400


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2400_2432
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2400_2432
private theorem valid2400 : RecordDataValid section14Catalog 1 (⟨86,(11),[1,5,6,13],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2401 : RecordDataValid section14Catalog 1 (⟨86,(12),[1,5,6,13],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2402 : RecordDataValid section14Catalog 1 (⟨86,(13),[1,5,6,13],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2403 : RecordDataValid section14Catalog 1 (⟨86,(14),[1,5,6,13],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2404 : RecordDataValid section14Catalog 1 (⟨86,(15),[1,5,6,13],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2405 : RecordDataValid section14Catalog 1 (⟨86,(16),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2406 : RecordDataValid section14Catalog 1 (⟨86,(17),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2407 : RecordDataValid section14Catalog 1 (⟨86,(18),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2408 : RecordDataValid section14Catalog 1 (⟨86,(19),[1,5,6,13],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2409 : RecordDataValid section14Catalog 1 (⟨86,(20),[1,5,6,13],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2410 : RecordDataValid section14Catalog 1 (⟨86,(21),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2411 : RecordDataValid section14Catalog 1 (⟨86,(22),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2412 : RecordDataValid section14Catalog 1 (⟨86,(23),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2413 : RecordDataValid section14Catalog 1 (⟨86,(24),[1,5,6,13],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2414 : RecordDataValid section14Catalog 1 (⟨89,(0),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2415 : RecordDataValid section14Catalog 1 (⟨89,(1),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2416 : RecordDataValid section14Catalog 1 (⟨89,(2),[1,5,6,13],[170],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2417 : RecordDataValid section14Catalog 1 (⟨89,(3),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2418 : RecordDataValid section14Catalog 1 (⟨89,(4),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2419 : RecordDataValid section14Catalog 1 (⟨89,(5),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2420 : RecordDataValid section14Catalog 1 (⟨89,(6),[1,5,6,13],[170],404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨404,[1,4,5,6,8,9,10,12,13,16],405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2421 : RecordDataValid section14Catalog 1 (⟨89,(7),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2422 : RecordDataValid section14Catalog 1 (⟨89,(8),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2423 : RecordDataValid section14Catalog 1 (⟨89,(9),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2424 : RecordDataValid section14Catalog 1 (⟨89,(10),[1,5,6,13],[170],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2425 : RecordDataValid section14Catalog 1 (⟨89,(11),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2426 : RecordDataValid section14Catalog 1 (⟨89,(12),[1,5,6,13],[170],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2427 : RecordDataValid section14Catalog 1 (⟨89,(13),[1,5,6,13],[170],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2428 : RecordDataValid section14Catalog 1 (⟨89,(14),[1,5,6,13],[170],405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨405,[1,4,5,6,8,9,10,12,13,16],406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2429 : RecordDataValid section14Catalog 1 (⟨89,(15),[1,5,6,13],[170],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2430 : RecordDataValid section14Catalog 1 (⟨92,(0),[1,5,6,13],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2431 : RecordDataValid section14Catalog 1 (⟨92,(1),[1,5,6,13],[170],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2400_2432 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2400).take 32 = [⟨86,(11),[1,5,6,13],[170],397⟩,⟨86,(12),[1,5,6,13],[170],397⟩,⟨86,(13),[1,5,6,13],[170],397⟩,⟨86,(14),[1,5,6,13],[170],396⟩,⟨86,(15),[1,5,6,13],[170],21⟩,⟨86,(16),[1,5,6,13],[170],398⟩,⟨86,(17),[1,5,6,13],[170],398⟩,⟨86,(18),[1,5,6,13],[170],398⟩,⟨86,(19),[1,5,6,13],[170],398⟩,⟨86,(20),[1,5,6,13],[170],24⟩,⟨86,(21),[1,5,6,13],[170],399⟩,⟨86,(22),[1,5,6,13],[170],399⟩,⟨86,(23),[1,5,6,13],[170],399⟩,⟨86,(24),[1,5,6,13],[170],399⟩,⟨89,(0),[1,5,6,13],[170],400⟩,⟨89,(1),[1,5,6,13],[170],401⟩,⟨89,(2),[1,5,6,13],[170],402⟩,⟨89,(3),[1,5,6,13],[170],403⟩,⟨89,(4),[1,5,6,13],[170],400⟩,⟨89,(5),[1,5,6,13],[170],401⟩,⟨89,(6),[1,5,6,13],[170],404⟩,⟨89,(7),[1,5,6,13],[170],403⟩,⟨89,(8),[1,5,6,13],[170],400⟩,⟨89,(9),[1,5,6,13],[170],401⟩,⟨89,(10),[1,5,6,13],[170],402⟩,⟨89,(11),[1,5,6,13],[170],403⟩,⟨89,(12),[1,5,6,13],[170],400⟩,⟨89,(13),[1,5,6,13],[170],401⟩,⟨89,(14),[1,5,6,13],[170],405⟩,⟨89,(15),[1,5,6,13],[170],403⟩,⟨92,(0),[1,5,6,13],[170],406⟩,⟨92,(1),[1,5,6,13],[170],407⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2400
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2401
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2402
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2403
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2404
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2405
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2406
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2407
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2408
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2409
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2410
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2411
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2412
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2413
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2414
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2415
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2416
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2417
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2418
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2419
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2420
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2421
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2422
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2423
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2424
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2425
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2426
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2427
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2428
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2429
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2430
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2431
end Section14Records_1_2400_2432

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2400_2432

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2304).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 2304 2368 2432 (by decide) (by decide) (all_of_interval_split P xs 2304 2336 2368 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2304_2336 hnum) (Freiman.workReverse20260919_s0001_records_2336_2368 hnum)) (all_of_interval_split P xs 2368 2400 2432 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2368_2400 hnum) (Freiman.workReverse20260919_s0001_records_2400_2432 hnum)))

#print axioms solution
