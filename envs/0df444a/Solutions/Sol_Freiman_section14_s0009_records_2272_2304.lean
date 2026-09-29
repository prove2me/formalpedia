-- Prove2me | solution 1 for Freiman.section14_s0009_records_2272_2304
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:23:06.093532+00:00
-- url     : https://prove2.me/submissions/8e67e59a-f7a0-47c8-95c2-5855cdfe414d

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
namespace Section14Records_9_2272_2304
private theorem valid2272 : RecordDataValid section14Catalog 9 (⟨236,(3),[9,10],[42],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2273 : RecordDataValid section14Catalog 9 (⟨237,(0),[9,10],[42],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2274 : RecordDataValid section14Catalog 9 (⟨237,(1),[9,10],[42],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2275 : RecordDataValid section14Catalog 9 (⟨237,(2),[9,10],[42],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2276 : RecordDataValid section14Catalog 9 (⟨237,(3),[9],[42],1271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1271,[4,8,9,12,16],1275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2277 : RecordDataValid section14Catalog 9 (⟨237,(4),[9,10],[42],866⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2278 : RecordDataValid section14Catalog 9 (⟨237,(5),[9,10],[42],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2279 : RecordDataValid section14Catalog 9 (⟨237,(6),[9,10],[42],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2280 : RecordDataValid section14Catalog 9 (⟨237,(7),[9,10],[42],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2281 : RecordDataValid section14Catalog 9 (⟨237,(8),[9],[42],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2282 : RecordDataValid section14Catalog 9 (⟨237,(9),[9,10],[42],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2283 : RecordDataValid section14Catalog 9 (⟨237,(10),[9,10],[42],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2284 : RecordDataValid section14Catalog 9 (⟨237,(11),[9,10],[42],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2285 : RecordDataValid section14Catalog 9 (⟨237,(12),[9,10],[42],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2286 : RecordDataValid section14Catalog 9 (⟨237,(13),[9,10],[42],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2287 : RecordDataValid section14Catalog 9 (⟨237,(14),[9,10],[42],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2288 : RecordDataValid section14Catalog 9 (⟨237,(15),[9,10],[42],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2289 : RecordDataValid section14Catalog 9 (⟨238,(0),[9,10],[42],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2290 : RecordDataValid section14Catalog 9 (⟨238,(1),[9,10],[42],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2291 : RecordDataValid section14Catalog 9 (⟨238,(2),[9],[42],1390⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1390,[9],1395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2292 : RecordDataValid section14Catalog 9 (⟨238,(3),[9,10],[42],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2293 : RecordDataValid section14Catalog 9 (⟨238,(4),[9,10],[42],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2294 : RecordDataValid section14Catalog 9 (⟨238,(5),[9,10],[42],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2295 : RecordDataValid section14Catalog 9 (⟨238,(6),[9],[42],1391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1391,[4,8,9,12,16],1396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2296 : RecordDataValid section14Catalog 9 (⟨238,(7),[9,10],[42],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2297 : RecordDataValid section14Catalog 9 (⟨238,(8),[9,10],[42],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2298 : RecordDataValid section14Catalog 9 (⟨238,(9),[9,10],[42],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2299 : RecordDataValid section14Catalog 9 (⟨238,(10),[9],[42],1392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1392,[4,8,9,12,16],1397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2300 : RecordDataValid section14Catalog 9 (⟨238,(11),[9,10],[42],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2301 : RecordDataValid section14Catalog 9 (⟨238,(12),[9,10],[42],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2302 : RecordDataValid section14Catalog 9 (⟨238,(13),[9,10],[42],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2303 : RecordDataValid section14Catalog 9 (⟨238,(14),[9],[42],1393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1393,[4,8,9,12,16],1398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2272).take 32 = [⟨236,(3),[9,10],[42],864⟩,⟨237,(0),[9,10],[42],865⟩,⟨237,(1),[9,10],[42],594⟩,⟨237,(2),[9,10],[42],595⟩,⟨237,(3),[9],[42],1271⟩,⟨237,(4),[9,10],[42],866⟩,⟨237,(5),[9,10],[42],598⟩,⟨237,(6),[9,10],[42],599⟩,⟨237,(7),[9,10],[42],600⟩,⟨237,(8),[9],[42],865⟩,⟨237,(9),[9,10],[42],594⟩,⟨237,(10),[9,10],[42],595⟩,⟨237,(11),[9,10],[42],596⟩,⟨237,(12),[9,10],[42],868⟩,⟨237,(13),[9,10],[42],602⟩,⟨237,(14),[9,10],[42],603⟩,⟨237,(15),[9,10],[42],604⟩,⟨238,(0),[9,10],[42],869⟩,⟨238,(1),[9,10],[42],870⟩,⟨238,(2),[9],[42],1390⟩,⟨238,(3),[9,10],[42],871⟩,⟨238,(4),[9,10],[42],609⟩,⟨238,(5),[9,10],[42],610⟩,⟨238,(6),[9],[42],1391⟩,⟨238,(7),[9,10],[42],612⟩,⟨238,(8),[9,10],[42],613⟩,⟨238,(9),[9,10],[42],614⟩,⟨238,(10),[9],[42],1392⟩,⟨238,(11),[9,10],[42],616⟩,⟨238,(12),[9,10],[42],617⟩,⟨238,(13),[9,10],[42],618⟩,⟨238,(14),[9],[42],1393⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2272
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2273
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2274
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2275
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2276
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2277
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2278
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2279
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2280
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2281
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2282
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2283
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2284
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2285
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2286
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2287
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2288
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2289
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2290
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2291
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2292
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2293
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2294
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2295
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2296
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2297
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2298
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2299
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2300
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2301
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2302
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2303
end Section14Records_9_2272_2304

#print axioms solution
