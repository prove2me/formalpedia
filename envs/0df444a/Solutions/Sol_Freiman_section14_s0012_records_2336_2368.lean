-- Prove2me | solution 1 for Freiman.section14_s0012_records_2336_2368
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:30:30.970983+00:00
-- url     : https://prove2.me/submissions/1bb2ce94-b874-48aa-9396-df91bff46832

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
namespace Section14Records_12_2336_2368
private theorem valid2336 : RecordDataValid section14Catalog 12 (⟨500,(8),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2337 : RecordDataValid section14Catalog 12 (⟨500,(9),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2338 : RecordDataValid section14Catalog 12 (⟨500,(9),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2339 : RecordDataValid section14Catalog 12 (⟨503,(0),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2340 : RecordDataValid section14Catalog 12 (⟨503,(0),[8,12],[10],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2341 : RecordDataValid section14Catalog 12 (⟨503,(0),[12],[6],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2342 : RecordDataValid section14Catalog 12 (⟨503,(1),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2343 : RecordDataValid section14Catalog 12 (⟨503,(1),[12],[6],1258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1258,[4,8,12,16],1262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2344 : RecordDataValid section14Catalog 12 (⟨503,(2),[4,8,12,16],[14],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2345 : RecordDataValid section14Catalog 12 (⟨503,(2),[4,8,12,16],[10],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2346 : RecordDataValid section14Catalog 12 (⟨503,(2),[12],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2347 : RecordDataValid section14Catalog 12 (⟨503,(3),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2348 : RecordDataValid section14Catalog 12 (⟨503,(3),[4,8,12,16],[14],1264⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1264,[4,8,12,16],1268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2349 : RecordDataValid section14Catalog 12 (⟨503,(3),[12],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2350 : RecordDataValid section14Catalog 12 (⟨507,(0),[4,8,12],[6],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2351 : RecordDataValid section14Catalog 12 (⟨507,(0),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2352 : RecordDataValid section14Catalog 12 (⟨507,(1),[4,8,12],[6],1267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1267,[4,8,12],1271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2353 : RecordDataValid section14Catalog 12 (⟨507,(1),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2354 : RecordDataValid section14Catalog 12 (⟨507,(2),[4,8,12],[6],1268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1268,[4,8,12],1272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2355 : RecordDataValid section14Catalog 12 (⟨507,(2),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2356 : RecordDataValid section14Catalog 12 (⟨507,(3),[4,8,12],[6],1267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1267,[4,8,12],1271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2357 : RecordDataValid section14Catalog 12 (⟨507,(3),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2358 : RecordDataValid section14Catalog 12 (⟨507,(4),[4,8,12],[6],1269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1269,[4,8,12],1273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2359 : RecordDataValid section14Catalog 12 (⟨507,(4),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2360 : RecordDataValid section14Catalog 12 (⟨507,(5),[4,8,12],[6],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2361 : RecordDataValid section14Catalog 12 (⟨507,(5),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2362 : RecordDataValid section14Catalog 12 (⟨507,(6),[4,8,12],[6],1267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1267,[4,8,12],1271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2363 : RecordDataValid section14Catalog 12 (⟨507,(6),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2364 : RecordDataValid section14Catalog 12 (⟨507,(7),[4,8,12],[6],1268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1268,[4,8,12],1272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2365 : RecordDataValid section14Catalog 12 (⟨507,(7),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2366 : RecordDataValid section14Catalog 12 (⟨507,(8),[4,8,12],[6],1267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1267,[4,8,12],1271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2367 : RecordDataValid section14Catalog 12 (⟨507,(8),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2336).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2336).take 32 = [⟨500,(8),[12],[6],2⟩,⟨500,(9),[4,8,12,16],[10,14],2⟩,⟨500,(9),[12],[6],2⟩,⟨503,(0),[4,8,12,16],[14],3⟩,⟨503,(0),[8,12],[10],1266⟩,⟨503,(0),[12],[6],98⟩,⟨503,(1),[4,8,12,16],[10,14],3⟩,⟨503,(1),[12],[6],1258⟩,⟨503,(2),[4,8,12,16],[14],29⟩,⟨503,(2),[4,8,12,16],[10],1266⟩,⟨503,(2),[12],[6],3⟩,⟨503,(3),[4,8,12,16],[10],29⟩,⟨503,(3),[4,8,12,16],[14],1264⟩,⟨503,(3),[12],[6],3⟩,⟨507,(0),[4,8,12],[6],349⟩,⟨507,(0),[4,8,12,16],[14],3⟩,⟨507,(1),[4,8,12],[6],1267⟩,⟨507,(1),[4,8,12,16],[14],3⟩,⟨507,(2),[4,8,12],[6],1268⟩,⟨507,(2),[4,8,12,16],[14],3⟩,⟨507,(3),[4,8,12],[6],1267⟩,⟨507,(3),[4,8,12,16],[14],3⟩,⟨507,(4),[4,8,12],[6],1269⟩,⟨507,(4),[4,8,12,16],[14],3⟩,⟨507,(5),[4,8,12],[6],349⟩,⟨507,(5),[4,8,12,16],[14],3⟩,⟨507,(6),[4,8,12],[6],1267⟩,⟨507,(6),[4,8,12,16],[14],3⟩,⟨507,(7),[4,8,12],[6],1268⟩,⟨507,(7),[4,8,12,16],[14],3⟩,⟨507,(8),[4,8,12],[6],1267⟩,⟨507,(8),[4,8,12,16],[14],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2336
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2337
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2338
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2339
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2340
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2341
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2342
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2343
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2344
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2345
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2346
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2347
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2348
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2349
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2350
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2351
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2352
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2353
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2354
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2355
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2356
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2357
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2358
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2359
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2360
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2361
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2362
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2363
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2364
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2365
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2366
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2367
end Section14Records_12_2336_2368

#print axioms solution
