-- Prove2me | solution 1 for Freiman.section14_s0008_records_2240_2272
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:56:21.995843+00:00
-- url     : https://prove2.me/submissions/a1f5d82f-6eba-4e2c-982e-6aad7e22ecd7

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
namespace Section14Records_8_2240_2272
private theorem valid2240 : RecordDataValid section14Catalog 8 (⟨297,(13),[8,12],[10],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2241 : RecordDataValid section14Catalog 8 (⟨297,(14),[8,12],[10],1456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1456,[5,8,9,12],1461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2242 : RecordDataValid section14Catalog 8 (⟨297,(15),[8,12],[10],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2243 : RecordDataValid section14Catalog 8 (⟨300,(0),[8,12],[10],1457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1457,[5,8,9,12],1462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2244 : RecordDataValid section14Catalog 8 (⟨300,(1),[8,12],[10],1458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1458,[5,8,9,12],1463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2245 : RecordDataValid section14Catalog 8 (⟨300,(2),[8,12],[10],1457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1457,[5,8,9,12],1462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2246 : RecordDataValid section14Catalog 8 (⟨300,(3),[8,12],[10],1459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1459,[5,8,9,12],1464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2247 : RecordDataValid section14Catalog 8 (⟨300,(4),[8,12],[10],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2248 : RecordDataValid section14Catalog 8 (⟨300,(5),[8,12],[10],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2249 : RecordDataValid section14Catalog 8 (⟨300,(6),[8,12],[10],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2250 : RecordDataValid section14Catalog 8 (⟨300,(7),[8,12],[10],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2251 : RecordDataValid section14Catalog 8 (⟨300,(8),[8,12],[10],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2252 : RecordDataValid section14Catalog 8 (⟨300,(9),[8,12],[10],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2253 : RecordDataValid section14Catalog 8 (⟨300,(10),[8,12],[10],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2254 : RecordDataValid section14Catalog 8 (⟨300,(11),[8,12],[10],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2255 : RecordDataValid section14Catalog 8 (⟨300,(12),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2256 : RecordDataValid section14Catalog 8 (⟨300,(13),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2257 : RecordDataValid section14Catalog 8 (⟨300,(14),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2258 : RecordDataValid section14Catalog 8 (⟨300,(15),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2259 : RecordDataValid section14Catalog 8 (⟨302,(0),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2260 : RecordDataValid section14Catalog 8 (⟨302,(1),[8,12],[10],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2261 : RecordDataValid section14Catalog 8 (⟨302,(2),[8,12],[10],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2262 : RecordDataValid section14Catalog 8 (⟨302,(3),[8,12],[10],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2263 : RecordDataValid section14Catalog 8 (⟨302,(4),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2264 : RecordDataValid section14Catalog 8 (⟨302,(5),[8,12],[10],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2265 : RecordDataValid section14Catalog 8 (⟨302,(6),[8,12],[10],1467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1467,[5,8,9,12],1472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2266 : RecordDataValid section14Catalog 8 (⟨302,(7),[8,12],[10],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2267 : RecordDataValid section14Catalog 8 (⟨302,(8),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2268 : RecordDataValid section14Catalog 8 (⟨302,(9),[8,12],[10],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2269 : RecordDataValid section14Catalog 8 (⟨302,(10),[8,12],[10],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2270 : RecordDataValid section14Catalog 8 (⟨302,(11),[8,12],[10],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2271 : RecordDataValid section14Catalog 8 (⟨302,(12),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2240).take 32 = [⟨297,(13),[8,12],[10],1452⟩,⟨297,(14),[8,12],[10],1456⟩,⟨297,(15),[8,12],[10],1454⟩,⟨300,(0),[8,12],[10],1457⟩,⟨300,(1),[8,12],[10],1458⟩,⟨300,(2),[8,12],[10],1457⟩,⟨300,(3),[8,12],[10],1459⟩,⟨300,(4),[8,12],[10],1460⟩,⟨300,(5),[8,12],[10],1460⟩,⟨300,(6),[8,12],[10],1460⟩,⟨300,(7),[8,12],[10],1460⟩,⟨300,(8),[8,12],[10],1461⟩,⟨300,(9),[8,12],[10],1461⟩,⟨300,(10),[8,12],[10],1461⟩,⟨300,(11),[8,12],[10],1461⟩,⟨300,(12),[8,12],[10],1462⟩,⟨300,(13),[8,12],[10],1462⟩,⟨300,(14),[8,12],[10],1462⟩,⟨300,(15),[8,12],[10],1462⟩,⟨302,(0),[8,12],[10],1463⟩,⟨302,(1),[8,12],[10],1464⟩,⟨302,(2),[8,12],[10],1465⟩,⟨302,(3),[8,12],[10],1466⟩,⟨302,(4),[8,12],[10],1463⟩,⟨302,(5),[8,12],[10],1464⟩,⟨302,(6),[8,12],[10],1467⟩,⟨302,(7),[8,12],[10],1466⟩,⟨302,(8),[8,12],[10],1463⟩,⟨302,(9),[8,12],[10],1464⟩,⟨302,(10),[8,12],[10],1465⟩,⟨302,(11),[8,12],[10],1466⟩,⟨302,(12),[8,12],[10],1463⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2240
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2241
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2242
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2243
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2244
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2245
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2246
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2247
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2248
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2249
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2250
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2251
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2252
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2253
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2254
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2255
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2256
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2257
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2258
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2259
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2260
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2261
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2262
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2263
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2264
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2265
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2266
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2267
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2268
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2269
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2270
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2271
end Section14Records_8_2240_2272

#print axioms solution
