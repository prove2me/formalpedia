-- Prove2me | solution 1 for Freiman.section14_s0012_records_2272_2304
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:27:39.056983+00:00
-- url     : https://prove2.me/submissions/74f3c595-b4ac-4722-80ec-078e99a7a175

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
namespace Section14Records_12_2272_2304
private theorem valid2272 : RecordDataValid section14Catalog 12 (⟨489,(4),[12],[2],1709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1709,[12],1714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2273 : RecordDataValid section14Catalog 12 (⟨489,(5),[4,8,12],[6],1254⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1254,[4,8,12],1258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2274 : RecordDataValid section14Catalog 12 (⟨489,(5),[12],[2],1706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1706,[12],1711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2275 : RecordDataValid section14Catalog 12 (⟨489,(6),[4,8,12],[6],1255⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1255,[4,8,12],1259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2276 : RecordDataValid section14Catalog 12 (⟨489,(6),[12],[2],1707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1707,[12],1712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2277 : RecordDataValid section14Catalog 12 (⟨489,(7),[4,8,12],[6],1256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1256,[4,8,12],1260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2278 : RecordDataValid section14Catalog 12 (⟨489,(7),[12],[2],1708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1708,[12],1713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2279 : RecordDataValid section14Catalog 12 (⟨489,(8),[4,8,12],[6],1255⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1255,[4,8,12],1259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2280 : RecordDataValid section14Catalog 12 (⟨489,(8),[12],[2],1707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1707,[12],1712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2281 : RecordDataValid section14Catalog 12 (⟨489,(9),[4,8,12],[6],1257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1257,[4,8,12],1261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2282 : RecordDataValid section14Catalog 12 (⟨489,(9),[12],[2],1709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1709,[12],1714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2283 : RecordDataValid section14Catalog 12 (⟨492,(0),[4,8,12,16],[6],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2284 : RecordDataValid section14Catalog 12 (⟨492,(0),[12],[2],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2285 : RecordDataValid section14Catalog 12 (⟨492,(1),[4,8,12,16],[6],1258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1258,[4,8,12,16],1262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2286 : RecordDataValid section14Catalog 12 (⟨492,(1),[12],[2],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2287 : RecordDataValid section14Catalog 12 (⟨492,(2),[4,8,12,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2288 : RecordDataValid section14Catalog 12 (⟨492,(2),[12],[2],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2289 : RecordDataValid section14Catalog 12 (⟨492,(3),[4,8,12,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2290 : RecordDataValid section14Catalog 12 (⟨492,(3),[12],[2],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2291 : RecordDataValid section14Catalog 12 (⟨494,(0),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2292 : RecordDataValid section14Catalog 12 (⟨494,(0),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2293 : RecordDataValid section14Catalog 12 (⟨494,(1),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2294 : RecordDataValid section14Catalog 12 (⟨494,(1),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2295 : RecordDataValid section14Catalog 12 (⟨494,(2),[4,8,12],[6],1259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1259,[4,8,12],1263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2296 : RecordDataValid section14Catalog 12 (⟨494,(2),[12],[2],1710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1710,[12],1715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2297 : RecordDataValid section14Catalog 12 (⟨494,(3),[4,8,12],[6],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2298 : RecordDataValid section14Catalog 12 (⟨494,(3),[12],[2],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2299 : RecordDataValid section14Catalog 12 (⟨497,(0),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2300 : RecordDataValid section14Catalog 12 (⟨497,(0),[12],[6],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2301 : RecordDataValid section14Catalog 12 (⟨497,(1),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2302 : RecordDataValid section14Catalog 12 (⟨497,(1),[12],[6],1711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1711,[12],1716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2303 : RecordDataValid section14Catalog 12 (⟨497,(2),[4,8,12,16],[10,14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2272).take 32 = [⟨489,(4),[12],[2],1709⟩,⟨489,(5),[4,8,12],[6],1254⟩,⟨489,(5),[12],[2],1706⟩,⟨489,(6),[4,8,12],[6],1255⟩,⟨489,(6),[12],[2],1707⟩,⟨489,(7),[4,8,12],[6],1256⟩,⟨489,(7),[12],[2],1708⟩,⟨489,(8),[4,8,12],[6],1255⟩,⟨489,(8),[12],[2],1707⟩,⟨489,(9),[4,8,12],[6],1257⟩,⟨489,(9),[12],[2],1709⟩,⟨492,(0),[4,8,12,16],[6],98⟩,⟨492,(0),[12],[2],1266⟩,⟨492,(1),[4,8,12,16],[6],1258⟩,⟨492,(1),[12],[2],98⟩,⟨492,(2),[4,8,12,16],[6],3⟩,⟨492,(2),[12],[2],3⟩,⟨492,(3),[4,8,12,16],[6],3⟩,⟨492,(3),[12],[2],3⟩,⟨494,(0),[4,8,12],[6],2⟩,⟨494,(0),[12],[2],2⟩,⟨494,(1),[4,8,12],[6],2⟩,⟨494,(1),[12],[2],2⟩,⟨494,(2),[4,8,12],[6],1259⟩,⟨494,(2),[12],[2],1710⟩,⟨494,(3),[4,8,12],[6],101⟩,⟨494,(3),[12],[2],101⟩,⟨497,(0),[4,8,12,16],[10,14],3⟩,⟨497,(0),[12],[6],1534⟩,⟨497,(1),[4,8,12,16],[10,14],3⟩,⟨497,(1),[12],[6],1711⟩,⟨497,(2),[4,8,12,16],[10,14],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2272
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2273
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2274
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2275
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2276
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2277
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2278
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2279
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2280
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2281
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2282
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2283
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2284
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2285
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2286
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2287
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2288
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2289
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2290
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2291
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2292
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2293
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2294
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2295
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2296
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2297
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2298
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2299
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2300
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2301
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2302
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2303
end Section14Records_12_2272_2304

#print axioms solution
