-- Prove2me | solution 1 for Freiman.section14_s0008_records_2336_2368
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:59:38.761983+00:00
-- url     : https://prove2.me/submissions/ecb06d80-9129-4523-821e-cfb91f9a5a89

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
namespace Section14Records_8_2336_2368
private theorem valid2336 : RecordDataValid section14Catalog 8 (⟨317,(0),[8,12],[10],1211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1211,[3,5,7,8,9,11,12,15],1215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2337 : RecordDataValid section14Catalog 8 (⟨317,(1),[8,12],[10],1212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1212,[3,5,7,8,9,11,12,15],1216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2338 : RecordDataValid section14Catalog 8 (⟨317,(2),[8,12],[10],1213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1213,[3,5,7,8,9,11,12,15],1217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2339 : RecordDataValid section14Catalog 8 (⟨317,(3),[8,12],[10],1214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1214,[3,5,7,8,9,11,12,15],1218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2340 : RecordDataValid section14Catalog 8 (⟨317,(4),[8,12],[10],1215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1215,[3,5,7,8,9,11,12,15],1219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2341 : RecordDataValid section14Catalog 8 (⟨317,(5),[8,12],[10],1216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1216,[3,5,7,8,9,11,12,15],1220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2342 : RecordDataValid section14Catalog 8 (⟨317,(6),[8,12],[10],1217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1217,[3,5,7,8,9,11,12,15],1221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2343 : RecordDataValid section14Catalog 8 (⟨317,(7),[8,12],[10],1218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1218,[3,5,7,8,9,11,12,15],1222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2344 : RecordDataValid section14Catalog 8 (⟨317,(8),[8,12],[10],1492⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1492,[5,8,9,12],1497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2345 : RecordDataValid section14Catalog 8 (⟨317,(9),[8,12],[10],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2346 : RecordDataValid section14Catalog 8 (⟨317,(10),[8,12],[10],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2347 : RecordDataValid section14Catalog 8 (⟨317,(11),[8,12],[10],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2348 : RecordDataValid section14Catalog 8 (⟨317,(12),[8,12],[10],1496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1496,[5,8,9,12],1501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2349 : RecordDataValid section14Catalog 8 (⟨317,(13),[8,12],[10],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2350 : RecordDataValid section14Catalog 8 (⟨317,(14),[8,12],[10],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2351 : RecordDataValid section14Catalog 8 (⟨317,(15),[8,12],[10],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2352 : RecordDataValid section14Catalog 8 (⟨318,(0),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2353 : RecordDataValid section14Catalog 8 (⟨318,(1),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2354 : RecordDataValid section14Catalog 8 (⟨318,(2),[8,12],[10],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2355 : RecordDataValid section14Catalog 8 (⟨318,(3),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2356 : RecordDataValid section14Catalog 8 (⟨318,(4),[8,12],[10],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2357 : RecordDataValid section14Catalog 8 (⟨318,(5),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2358 : RecordDataValid section14Catalog 8 (⟨318,(6),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2359 : RecordDataValid section14Catalog 8 (⟨318,(7),[8,12],[10],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2360 : RecordDataValid section14Catalog 8 (⟨318,(8),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2361 : RecordDataValid section14Catalog 8 (⟨318,(9),[8,12],[10],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2362 : RecordDataValid section14Catalog 8 (⟨318,(10),[8,12],[10],1500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1500,[5,8,9,12],1505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2363 : RecordDataValid section14Catalog 8 (⟨318,(11),[8,12],[10],1501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1501,[5,8,9,12],1506⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2364 : RecordDataValid section14Catalog 8 (⟨318,(12),[8,12],[10],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2365 : RecordDataValid section14Catalog 8 (⟨318,(13),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2366 : RecordDataValid section14Catalog 8 (⟨318,(14),[8,12],[10],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2367 : RecordDataValid section14Catalog 8 (⟨318,(15),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2336).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2336).take 32 = [⟨317,(0),[8,12],[10],1211⟩,⟨317,(1),[8,12],[10],1212⟩,⟨317,(2),[8,12],[10],1213⟩,⟨317,(3),[8,12],[10],1214⟩,⟨317,(4),[8,12],[10],1215⟩,⟨317,(5),[8,12],[10],1216⟩,⟨317,(6),[8,12],[10],1217⟩,⟨317,(7),[8,12],[10],1218⟩,⟨317,(8),[8,12],[10],1492⟩,⟨317,(9),[8,12],[10],1493⟩,⟨317,(10),[8,12],[10],1494⟩,⟨317,(11),[8,12],[10],1495⟩,⟨317,(12),[8,12],[10],1496⟩,⟨317,(13),[8,12],[10],1493⟩,⟨317,(14),[8,12],[10],1494⟩,⟨317,(15),[8,12],[10],1495⟩,⟨318,(0),[8,12],[10],882⟩,⟨318,(1),[8,12],[10],1497⟩,⟨318,(2),[8,12],[10],1498⟩,⟨318,(3),[8,12],[10],101⟩,⟨318,(4),[8,12],[10],1498⟩,⟨318,(5),[8,12],[10],882⟩,⟨318,(6),[8,12],[10],1497⟩,⟨318,(7),[8,12],[10],1499⟩,⟨318,(8),[8,12],[10],101⟩,⟨318,(9),[8,12],[10],1499⟩,⟨318,(10),[8,12],[10],1500⟩,⟨318,(11),[8,12],[10],1501⟩,⟨318,(12),[8,12],[10],1502⟩,⟨318,(13),[8,12],[10],101⟩,⟨318,(14),[8,12],[10],1502⟩,⟨318,(15),[8,12],[10],882⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2336
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2337
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2338
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2339
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2340
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2341
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2342
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2343
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2344
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2345
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2346
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2347
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2348
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2349
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2350
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2351
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2352
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2353
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2354
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2355
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2356
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2357
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2358
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2359
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2360
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2361
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2362
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2363
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2364
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2365
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2366
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2367
end Section14Records_8_2336_2368

#print axioms solution
