-- Prove2me | solution 1 for Freiman.section14_s0009_records_2240_2272
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:21:11.563628+00:00
-- url     : https://prove2.me/submissions/c748c0e3-029e-498f-b708-a9f4ed6a76c4

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
namespace Section14Records_9_2240_2272
private theorem valid2240 : RecordDataValid section14Catalog 9 (⟨234,(3),[9],[42],1383⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1383,[4,8,9,12,16],1387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2241 : RecordDataValid section14Catalog 9 (⟨234,(4),[9,10],[42],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2242 : RecordDataValid section14Catalog 9 (⟨234,(5),[9],[42],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2243 : RecordDataValid section14Catalog 9 (⟨234,(6),[9],[42],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2244 : RecordDataValid section14Catalog 9 (⟨234,(7),[9],[42],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2245 : RecordDataValid section14Catalog 9 (⟨234,(8),[9,10],[42],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2246 : RecordDataValid section14Catalog 9 (⟨234,(9),[9],[42],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2247 : RecordDataValid section14Catalog 9 (⟨234,(10),[9],[42],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2248 : RecordDataValid section14Catalog 9 (⟨234,(11),[9],[42],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2249 : RecordDataValid section14Catalog 9 (⟨234,(12),[9,10],[42],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2250 : RecordDataValid section14Catalog 9 (⟨234,(13),[9],[42],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2251 : RecordDataValid section14Catalog 9 (⟨234,(14),[9],[42],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2252 : RecordDataValid section14Catalog 9 (⟨234,(15),[9],[42],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2253 : RecordDataValid section14Catalog 9 (⟨235,(0),[9,10],[42],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2254 : RecordDataValid section14Catalog 9 (⟨235,(1),[9,10],[42],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2255 : RecordDataValid section14Catalog 9 (⟨235,(2),[9],[42],1387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1387,[4,8,9,12,16],1391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2256 : RecordDataValid section14Catalog 9 (⟨235,(3),[9,10],[42],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2257 : RecordDataValid section14Catalog 9 (⟨235,(4),[9,10],[42],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2258 : RecordDataValid section14Catalog 9 (⟨235,(5),[9,10],[42],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2259 : RecordDataValid section14Catalog 9 (⟨235,(6),[9],[42],1388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1388,[4,8,9,12,16],1392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2260 : RecordDataValid section14Catalog 9 (⟨235,(7),[9,10],[42],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2261 : RecordDataValid section14Catalog 9 (⟨235,(8),[9,10],[42],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2262 : RecordDataValid section14Catalog 9 (⟨235,(9),[9,10],[42],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2263 : RecordDataValid section14Catalog 9 (⟨235,(10),[9],[42],1387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1387,[4,8,9,12,16],1391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2264 : RecordDataValid section14Catalog 9 (⟨235,(11),[9,10],[42],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2265 : RecordDataValid section14Catalog 9 (⟨235,(12),[9,10],[42],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2266 : RecordDataValid section14Catalog 9 (⟨235,(13),[9,10],[42],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2267 : RecordDataValid section14Catalog 9 (⟨235,(14),[9],[42],1389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1389,[4,8,9,12,16],1393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2268 : RecordDataValid section14Catalog 9 (⟨235,(15),[9,10],[42],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2269 : RecordDataValid section14Catalog 9 (⟨236,(0),[9,10],[42],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2270 : RecordDataValid section14Catalog 9 (⟨236,(1),[9,10],[42],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2271 : RecordDataValid section14Catalog 9 (⟨236,(2),[9],[42],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2240).take 32 = [⟨234,(3),[9],[42],1383⟩,⟨234,(4),[9,10],[42],572⟩,⟨234,(5),[9],[42],1384⟩,⟨234,(6),[9],[42],1384⟩,⟨234,(7),[9],[42],1384⟩,⟨234,(8),[9,10],[42],574⟩,⟨234,(9),[9],[42],1385⟩,⟨234,(10),[9],[42],1385⟩,⟨234,(11),[9],[42],1385⟩,⟨234,(12),[9,10],[42],576⟩,⟨234,(13),[9],[42],1386⟩,⟨234,(14),[9],[42],1386⟩,⟨234,(15),[9],[42],1386⟩,⟨235,(0),[9,10],[42],578⟩,⟨235,(1),[9,10],[42],579⟩,⟨235,(2),[9],[42],1387⟩,⟨235,(3),[9,10],[42],581⟩,⟨235,(4),[9,10],[42],582⟩,⟨235,(5),[9,10],[42],583⟩,⟨235,(6),[9],[42],1388⟩,⟨235,(7),[9,10],[42],585⟩,⟨235,(8),[9,10],[42],578⟩,⟨235,(9),[9,10],[42],579⟩,⟨235,(10),[9],[42],1387⟩,⟨235,(11),[9,10],[42],581⟩,⟨235,(12),[9,10],[42],586⟩,⟨235,(13),[9,10],[42],587⟩,⟨235,(14),[9],[42],1389⟩,⟨235,(15),[9,10],[42],589⟩,⟨236,(0),[9,10],[42],861⟩,⟨236,(1),[9,10],[42],862⟩,⟨236,(2),[9],[42],861⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2240
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2241
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2242
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2243
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2244
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2245
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2246
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2247
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2248
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2249
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2250
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2251
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2252
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2253
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2254
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2255
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2256
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2257
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2258
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2259
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2260
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2261
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2262
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2263
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2264
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2265
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2266
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2267
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2268
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2269
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2270
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2271
end Section14Records_9_2240_2272

#print axioms solution
