-- Prove2me | solution 1 for Freiman.section14_s0007_records_2272_2304
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:39:01.173588+00:00
-- url     : https://prove2.me/submissions/e071bbc8-a1b7-4e95-919c-eac41b62356a

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
namespace Section14Records_7_2272_2304
private theorem valid2272 : RecordDataValid section14Catalog 7 (⟨417,(16),[3,7,15],[10],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2273 : RecordDataValid section14Catalog 7 (⟨417,(17),[3,7,15],[10],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2274 : RecordDataValid section14Catalog 7 (⟨417,(18),[3,7,15],[10],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2275 : RecordDataValid section14Catalog 7 (⟨417,(19),[3,7,15],[10],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2276 : RecordDataValid section14Catalog 7 (⟨417,(20),[3,7,15],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2277 : RecordDataValid section14Catalog 7 (⟨417,(21),[3,7,15],[10],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2278 : RecordDataValid section14Catalog 7 (⟨417,(22),[3,7,15],[10],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2279 : RecordDataValid section14Catalog 7 (⟨417,(23),[3,7,15],[10],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2280 : RecordDataValid section14Catalog 7 (⟨417,(24),[3,7,15],[10],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2281 : RecordDataValid section14Catalog 7 (⟨420,(0),[3,7,15],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2282 : RecordDataValid section14Catalog 7 (⟨420,(1),[3,7,15],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2283 : RecordDataValid section14Catalog 7 (⟨420,(2),[3,7,15],[10],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2284 : RecordDataValid section14Catalog 7 (⟨420,(3),[3,7,15],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2285 : RecordDataValid section14Catalog 7 (⟨420,(4),[3,7,15],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2286 : RecordDataValid section14Catalog 7 (⟨420,(5),[3,7,15],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2287 : RecordDataValid section14Catalog 7 (⟨420,(6),[3,7,15],[10],1090⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1090,[3,5,7,8,9,11,12,15],1094⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2288 : RecordDataValid section14Catalog 7 (⟨420,(7),[3,7,15],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2289 : RecordDataValid section14Catalog 7 (⟨420,(8),[3,7,15],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2290 : RecordDataValid section14Catalog 7 (⟨420,(9),[3,7,15],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2291 : RecordDataValid section14Catalog 7 (⟨420,(10),[3,7,15],[10],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2292 : RecordDataValid section14Catalog 7 (⟨420,(11),[3,7,15],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2293 : RecordDataValid section14Catalog 7 (⟨420,(12),[3,7,15],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2294 : RecordDataValid section14Catalog 7 (⟨420,(13),[3,7,15],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2295 : RecordDataValid section14Catalog 7 (⟨420,(14),[3,7,15],[10],1091⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1091,[3,5,7,8,9,11,12,15],1095⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2296 : RecordDataValid section14Catalog 7 (⟨420,(15),[3,7,15],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2297 : RecordDataValid section14Catalog 7 (⟨423,(0),[3,7,15],[10],1092⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1092,[3,7,11,15],1096⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2298 : RecordDataValid section14Catalog 7 (⟨423,(1),[3,7,15],[10],1093⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1093,[3,7,11,15],1097⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2299 : RecordDataValid section14Catalog 7 (⟨423,(2),[3,7,15],[10],1092⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1092,[3,7,11,15],1096⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2300 : RecordDataValid section14Catalog 7 (⟨423,(3),[3,7,15],[10],1094⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1094,[3,7,11,15],1098⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2301 : RecordDataValid section14Catalog 7 (⟨423,(4),[3,7,15],[10],1095⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1095,[3,7,11,15],1099⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2302 : RecordDataValid section14Catalog 7 (⟨423,(5),[3,7,15],[10],1095⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1095,[3,7,11,15],1099⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2303 : RecordDataValid section14Catalog 7 (⟨423,(6),[3,7,15],[10],1095⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1095,[3,7,11,15],1099⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2272).take 32 = [⟨417,(16),[3,7,15],[10],892⟩,⟨417,(17),[3,7,15],[10],892⟩,⟨417,(18),[3,7,15],[10],892⟩,⟨417,(19),[3,7,15],[10],892⟩,⟨417,(20),[3,7,15],[10],24⟩,⟨417,(21),[3,7,15],[10],893⟩,⟨417,(22),[3,7,15],[10],893⟩,⟨417,(23),[3,7,15],[10],893⟩,⟨417,(24),[3,7,15],[10],893⟩,⟨420,(0),[3,7,15],[10],1086⟩,⟨420,(1),[3,7,15],[10],1087⟩,⟨420,(2),[3,7,15],[10],1088⟩,⟨420,(3),[3,7,15],[10],1089⟩,⟨420,(4),[3,7,15],[10],1086⟩,⟨420,(5),[3,7,15],[10],1087⟩,⟨420,(6),[3,7,15],[10],1090⟩,⟨420,(7),[3,7,15],[10],1089⟩,⟨420,(8),[3,7,15],[10],1086⟩,⟨420,(9),[3,7,15],[10],1087⟩,⟨420,(10),[3,7,15],[10],1088⟩,⟨420,(11),[3,7,15],[10],1089⟩,⟨420,(12),[3,7,15],[10],1086⟩,⟨420,(13),[3,7,15],[10],1087⟩,⟨420,(14),[3,7,15],[10],1091⟩,⟨420,(15),[3,7,15],[10],1089⟩,⟨423,(0),[3,7,15],[10],1092⟩,⟨423,(1),[3,7,15],[10],1093⟩,⟨423,(2),[3,7,15],[10],1092⟩,⟨423,(3),[3,7,15],[10],1094⟩,⟨423,(4),[3,7,15],[10],1095⟩,⟨423,(5),[3,7,15],[10],1095⟩,⟨423,(6),[3,7,15],[10],1095⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2272
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2273
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2274
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2275
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2276
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2277
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2278
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2279
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2280
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2281
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2282
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2283
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2284
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2285
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2286
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2287
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2288
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2289
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2290
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2291
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2292
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2293
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2294
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2295
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2296
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2297
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2298
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2299
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2300
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2301
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2302
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2303
end Section14Records_7_2272_2304

#print axioms solution
