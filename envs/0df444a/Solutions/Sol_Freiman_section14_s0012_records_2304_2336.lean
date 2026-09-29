-- Prove2me | solution 1 for Freiman.section14_s0012_records_2304_2336
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:30:29.791424+00:00
-- url     : https://prove2.me/submissions/10ea7c61-7e98-4188-a941-a26687a9fb16

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
namespace Section14Records_12_2304_2336
private theorem valid2304 : RecordDataValid section14Catalog 12 (⟨497,(2),[12],[6],1712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1712,[12],1717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2305 : RecordDataValid section14Catalog 12 (⟨497,(3),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2306 : RecordDataValid section14Catalog 12 (⟨497,(3),[12],[6],1711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1711,[12],1716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2307 : RecordDataValid section14Catalog 12 (⟨497,(4),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2308 : RecordDataValid section14Catalog 12 (⟨497,(4),[12],[6],1713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1713,[12],1718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2309 : RecordDataValid section14Catalog 12 (⟨497,(5),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2310 : RecordDataValid section14Catalog 12 (⟨497,(5),[12],[6],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2311 : RecordDataValid section14Catalog 12 (⟨497,(6),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2312 : RecordDataValid section14Catalog 12 (⟨497,(6),[12],[6],1711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1711,[12],1716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2313 : RecordDataValid section14Catalog 12 (⟨497,(7),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2314 : RecordDataValid section14Catalog 12 (⟨497,(7),[12],[6],1712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1712,[12],1717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2315 : RecordDataValid section14Catalog 12 (⟨497,(8),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2316 : RecordDataValid section14Catalog 12 (⟨497,(8),[12],[6],1711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1711,[12],1716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2317 : RecordDataValid section14Catalog 12 (⟨497,(9),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2318 : RecordDataValid section14Catalog 12 (⟨497,(9),[12],[6],1713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1713,[12],1718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2319 : RecordDataValid section14Catalog 12 (⟨500,(0),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2320 : RecordDataValid section14Catalog 12 (⟨500,(0),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2321 : RecordDataValid section14Catalog 12 (⟨500,(1),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2322 : RecordDataValid section14Catalog 12 (⟨500,(1),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2323 : RecordDataValid section14Catalog 12 (⟨500,(2),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2324 : RecordDataValid section14Catalog 12 (⟨500,(2),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2325 : RecordDataValid section14Catalog 12 (⟨500,(3),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2326 : RecordDataValid section14Catalog 12 (⟨500,(3),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2327 : RecordDataValid section14Catalog 12 (⟨500,(4),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2328 : RecordDataValid section14Catalog 12 (⟨500,(4),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2329 : RecordDataValid section14Catalog 12 (⟨500,(5),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2330 : RecordDataValid section14Catalog 12 (⟨500,(5),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2331 : RecordDataValid section14Catalog 12 (⟨500,(6),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2332 : RecordDataValid section14Catalog 12 (⟨500,(6),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2333 : RecordDataValid section14Catalog 12 (⟨500,(7),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2334 : RecordDataValid section14Catalog 12 (⟨500,(7),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2335 : RecordDataValid section14Catalog 12 (⟨500,(8),[4,8,12,16],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2304).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2304).take 32 = [⟨497,(2),[12],[6],1712⟩,⟨497,(3),[4,8,12,16],[10,14],3⟩,⟨497,(3),[12],[6],1711⟩,⟨497,(4),[4,8,12,16],[10,14],3⟩,⟨497,(4),[12],[6],1713⟩,⟨497,(5),[4,8,12,16],[10,14],3⟩,⟨497,(5),[12],[6],1534⟩,⟨497,(6),[4,8,12,16],[10,14],3⟩,⟨497,(6),[12],[6],1711⟩,⟨497,(7),[4,8,12,16],[10,14],3⟩,⟨497,(7),[12],[6],1712⟩,⟨497,(8),[4,8,12,16],[10,14],3⟩,⟨497,(8),[12],[6],1711⟩,⟨497,(9),[4,8,12,16],[10,14],3⟩,⟨497,(9),[12],[6],1713⟩,⟨500,(0),[4,8,12,16],[10,14],2⟩,⟨500,(0),[12],[6],2⟩,⟨500,(1),[4,8,12,16],[10,14],2⟩,⟨500,(1),[12],[6],2⟩,⟨500,(2),[4,8,12,16],[10,14],2⟩,⟨500,(2),[12],[6],2⟩,⟨500,(3),[4,8,12,16],[10,14],2⟩,⟨500,(3),[12],[6],2⟩,⟨500,(4),[4,8,12,16],[10,14],2⟩,⟨500,(4),[12],[6],2⟩,⟨500,(5),[4,8,12,16],[10,14],2⟩,⟨500,(5),[12],[6],2⟩,⟨500,(6),[4,8,12,16],[10,14],2⟩,⟨500,(6),[12],[6],2⟩,⟨500,(7),[4,8,12,16],[10,14],2⟩,⟨500,(7),[12],[6],2⟩,⟨500,(8),[4,8,12,16],[10,14],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2304
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2305
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2306
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2307
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2308
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2309
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2310
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2311
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2312
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2313
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2314
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2315
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2316
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2317
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2318
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2319
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2320
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2321
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2322
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2323
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2324
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2325
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2326
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2327
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2328
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2329
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2330
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2331
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2332
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2333
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2334
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2335
end Section14Records_12_2304_2336

#print axioms solution
