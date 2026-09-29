-- Prove2me | solution 1 for Freiman.section14_s0008_records_2368_2400
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T08:00:24.285982+00:00
-- url     : https://prove2.me/submissions/e307b7ac-ae50-426c-8bc4-ebeedaf2031f

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
namespace Section14Records_8_2368_2400
private theorem valid2368 : RecordDataValid section14Catalog 8 (⟨318,(16),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2369 : RecordDataValid section14Catalog 8 (⟨318,(17),[8,12],[10],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2370 : RecordDataValid section14Catalog 8 (⟨318,(18),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2371 : RecordDataValid section14Catalog 8 (⟨318,(19),[8,12],[10],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2372 : RecordDataValid section14Catalog 8 (⟨319,(0),[8,12],[10],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2373 : RecordDataValid section14Catalog 8 (⟨319,(1),[8,12],[10],1229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1229,[3,5,7,8,9,11,12,15],1233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2374 : RecordDataValid section14Catalog 8 (⟨319,(2),[8,12],[10],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2375 : RecordDataValid section14Catalog 8 (⟨319,(3),[8,12],[10],1230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1230,[3,5,7,8,9,11,12,15],1234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2376 : RecordDataValid section14Catalog 8 (⟨319,(4),[8,12],[10],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2377 : RecordDataValid section14Catalog 8 (⟨319,(5),[8,12],[10],1232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1232,[3,5,7,8,9,11,12,15],1236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2378 : RecordDataValid section14Catalog 8 (⟨319,(6),[8,12],[10],1504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1504,[5,8,9,12],1509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2379 : RecordDataValid section14Catalog 8 (⟨319,(7),[8,12],[10],1505⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1505,[5,8,9,12],1510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2380 : RecordDataValid section14Catalog 8 (⟨319,(8),[8,12],[10],1235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1235,[3,5,7,8,9,11,12,15],1239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2381 : RecordDataValid section14Catalog 8 (⟨319,(9),[8,12],[10],1236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1236,[3,5,7,8,9,11,12,15],1240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2382 : RecordDataValid section14Catalog 8 (⟨319,(10),[8,12],[10],1506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1506,[5,8,9,12],1511⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2383 : RecordDataValid section14Catalog 8 (⟨319,(11),[8,12],[10],1507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1507,[5,8,9,12],1512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2384 : RecordDataValid section14Catalog 8 (⟨319,(12),[8,12],[10],1239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1239,[3,5,7,8,9,11,12,15],1243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2385 : RecordDataValid section14Catalog 8 (⟨319,(13),[8,12],[10],1240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1240,[3,5,7,8,9,11,12,15],1244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2386 : RecordDataValid section14Catalog 8 (⟨319,(14),[8,12],[10],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2387 : RecordDataValid section14Catalog 8 (⟨319,(15),[8,12],[10],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2388 : RecordDataValid section14Catalog 8 (⟨319,(16),[8,12],[10],1242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1242,[3,5,7,8,9,11,12,15],1246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2389 : RecordDataValid section14Catalog 8 (⟨319,(17),[8,12],[10],1243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1243,[3,5,7,8,9,11,12,15],1247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2390 : RecordDataValid section14Catalog 8 (⟨319,(18),[8,12],[10],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2391 : RecordDataValid section14Catalog 8 (⟨319,(19),[8,12],[10],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2392 : RecordDataValid section14Catalog 8 (⟨321,(0),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2393 : RecordDataValid section14Catalog 8 (⟨321,(1),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2394 : RecordDataValid section14Catalog 8 (⟨321,(2),[8,12],[10],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2395 : RecordDataValid section14Catalog 8 (⟨321,(3),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2396 : RecordDataValid section14Catalog 8 (⟨321,(4),[8,12],[10],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2397 : RecordDataValid section14Catalog 8 (⟨321,(5),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2398 : RecordDataValid section14Catalog 8 (⟨321,(6),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2399 : RecordDataValid section14Catalog 8 (⟨321,(7),[8,12],[10],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2368).take 32 = [⟨318,(16),[8,12],[10],1497⟩,⟨318,(17),[8,12],[10],1503⟩,⟨318,(18),[8,12],[10],101⟩,⟨318,(19),[8,12],[10],1503⟩,⟨319,(0),[8,12],[10],1231⟩,⟨319,(1),[8,12],[10],1229⟩,⟨319,(2),[8,12],[10],1228⟩,⟨319,(3),[8,12],[10],1230⟩,⟨319,(4),[8,12],[10],1231⟩,⟨319,(5),[8,12],[10],1232⟩,⟨319,(6),[8,12],[10],1504⟩,⟨319,(7),[8,12],[10],1505⟩,⟨319,(8),[8,12],[10],1235⟩,⟨319,(9),[8,12],[10],1236⟩,⟨319,(10),[8,12],[10],1506⟩,⟨319,(11),[8,12],[10],1507⟩,⟨319,(12),[8,12],[10],1239⟩,⟨319,(13),[8,12],[10],1240⟩,⟨319,(14),[8,12],[10],1508⟩,⟨319,(15),[8,12],[10],1508⟩,⟨319,(16),[8,12],[10],1242⟩,⟨319,(17),[8,12],[10],1243⟩,⟨319,(18),[8,12],[10],1509⟩,⟨319,(19),[8,12],[10],1509⟩,⟨321,(0),[8,12],[10],882⟩,⟨321,(1),[8,12],[10],1497⟩,⟨321,(2),[8,12],[10],1245⟩,⟨321,(3),[8,12],[10],101⟩,⟨321,(4),[8,12],[10],1245⟩,⟨321,(5),[8,12],[10],882⟩,⟨321,(6),[8,12],[10],1497⟩,⟨321,(7),[8,12],[10],1510⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2368
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2369
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2370
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2371
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2372
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2373
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2374
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2375
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2376
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2377
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2378
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2379
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2380
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2381
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2382
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2383
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2384
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2385
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2386
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2387
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2388
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2389
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2390
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2391
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2392
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2393
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2394
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2395
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2396
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2397
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2398
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2399
end Section14Records_8_2368_2400

#print axioms solution
