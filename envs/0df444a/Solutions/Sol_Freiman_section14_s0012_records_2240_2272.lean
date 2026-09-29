-- Prove2me | solution 1 for Freiman.section14_s0012_records_2240_2272
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:26:59.318268+00:00
-- url     : https://prove2.me/submissions/2e90ca8d-6efa-4e90-8a4a-48117c79c581

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
namespace Section14Records_12_2240_2272
private theorem valid2240 : RecordDataValid section14Catalog 12 (⟨483,(8),[12],[2],1703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1703,[12],1708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2241 : RecordDataValid section14Catalog 12 (⟨483,(9),[4,8,12,16],[6],1253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1253,[4,8,12,16],1257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2242 : RecordDataValid section14Catalog 12 (⟨483,(9),[12],[2],1705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1705,[12],1710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2243 : RecordDataValid section14Catalog 12 (⟨486,(0),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2244 : RecordDataValid section14Catalog 12 (⟨486,(0),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2245 : RecordDataValid section14Catalog 12 (⟨486,(1),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2246 : RecordDataValid section14Catalog 12 (⟨486,(1),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2247 : RecordDataValid section14Catalog 12 (⟨486,(2),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2248 : RecordDataValid section14Catalog 12 (⟨486,(2),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2249 : RecordDataValid section14Catalog 12 (⟨486,(3),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2250 : RecordDataValid section14Catalog 12 (⟨486,(3),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2251 : RecordDataValid section14Catalog 12 (⟨486,(4),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2252 : RecordDataValid section14Catalog 12 (⟨486,(4),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2253 : RecordDataValid section14Catalog 12 (⟨486,(5),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2254 : RecordDataValid section14Catalog 12 (⟨486,(5),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2255 : RecordDataValid section14Catalog 12 (⟨486,(6),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2256 : RecordDataValid section14Catalog 12 (⟨486,(6),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2257 : RecordDataValid section14Catalog 12 (⟨486,(7),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2258 : RecordDataValid section14Catalog 12 (⟨486,(7),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2259 : RecordDataValid section14Catalog 12 (⟨486,(8),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2260 : RecordDataValid section14Catalog 12 (⟨486,(8),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2261 : RecordDataValid section14Catalog 12 (⟨486,(9),[4,8,12,16],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2262 : RecordDataValid section14Catalog 12 (⟨486,(9),[12],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2263 : RecordDataValid section14Catalog 12 (⟨489,(0),[4,8,12],[6],1254⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1254,[4,8,12],1258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2264 : RecordDataValid section14Catalog 12 (⟨489,(0),[12],[2],1706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1706,[12],1711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2265 : RecordDataValid section14Catalog 12 (⟨489,(1),[4,8,12],[6],1255⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1255,[4,8,12],1259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2266 : RecordDataValid section14Catalog 12 (⟨489,(1),[12],[2],1707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1707,[12],1712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2267 : RecordDataValid section14Catalog 12 (⟨489,(2),[4,8,12],[6],1256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1256,[4,8,12],1260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2268 : RecordDataValid section14Catalog 12 (⟨489,(2),[12],[2],1708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1708,[12],1713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2269 : RecordDataValid section14Catalog 12 (⟨489,(3),[4,8,12],[6],1255⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1255,[4,8,12],1259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2270 : RecordDataValid section14Catalog 12 (⟨489,(3),[12],[2],1707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1707,[12],1712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2271 : RecordDataValid section14Catalog 12 (⟨489,(4),[4,8,12],[6],1257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1257,[4,8,12],1261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2240).take 32 = [⟨483,(8),[12],[2],1703⟩,⟨483,(9),[4,8,12,16],[6],1253⟩,⟨483,(9),[12],[2],1705⟩,⟨486,(0),[4,8,12,16],[6],2⟩,⟨486,(0),[12],[2],2⟩,⟨486,(1),[4,8,12,16],[6],2⟩,⟨486,(1),[12],[2],2⟩,⟨486,(2),[4,8,12,16],[6],2⟩,⟨486,(2),[12],[2],2⟩,⟨486,(3),[4,8,12,16],[6],2⟩,⟨486,(3),[12],[2],2⟩,⟨486,(4),[4,8,12,16],[6],2⟩,⟨486,(4),[12],[2],2⟩,⟨486,(5),[4,8,12,16],[6],2⟩,⟨486,(5),[12],[2],2⟩,⟨486,(6),[4,8,12,16],[6],2⟩,⟨486,(6),[12],[2],2⟩,⟨486,(7),[4,8,12,16],[6],2⟩,⟨486,(7),[12],[2],2⟩,⟨486,(8),[4,8,12,16],[6],2⟩,⟨486,(8),[12],[2],2⟩,⟨486,(9),[4,8,12,16],[6],2⟩,⟨486,(9),[12],[2],2⟩,⟨489,(0),[4,8,12],[6],1254⟩,⟨489,(0),[12],[2],1706⟩,⟨489,(1),[4,8,12],[6],1255⟩,⟨489,(1),[12],[2],1707⟩,⟨489,(2),[4,8,12],[6],1256⟩,⟨489,(2),[12],[2],1708⟩,⟨489,(3),[4,8,12],[6],1255⟩,⟨489,(3),[12],[2],1707⟩,⟨489,(4),[4,8,12],[6],1257⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2240
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2241
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2242
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2243
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2244
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2245
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2246
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2247
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2248
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2249
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2250
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2251
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2252
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2253
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2254
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2255
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2256
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2257
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2258
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2259
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2260
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2261
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2262
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2263
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2264
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2265
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2266
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2267
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2268
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2269
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2270
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2271
end Section14Records_12_2240_2272

#print axioms solution
