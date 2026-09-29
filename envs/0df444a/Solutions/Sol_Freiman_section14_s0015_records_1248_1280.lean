-- Prove2me | solution 1 for Freiman.section14_s0015_records_1248_1280
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:19:16.650685+00:00
-- url     : https://prove2.me/submissions/5617080b-e4dd-4f60-bac1-dd2dc979cc98

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
namespace Section14Records_15_1248_1280
private theorem valid1248 : RecordDataValid section14Catalog 15 (⟨399,(1),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1249 : RecordDataValid section14Catalog 15 (⟨399,(2),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1250 : RecordDataValid section14Catalog 15 (⟨399,(3),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1251 : RecordDataValid section14Catalog 15 (⟨399,(4),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1252 : RecordDataValid section14Catalog 15 (⟨399,(5),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1253 : RecordDataValid section14Catalog 15 (⟨399,(6),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1254 : RecordDataValid section14Catalog 15 (⟨399,(7),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1255 : RecordDataValid section14Catalog 15 (⟨399,(8),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1256 : RecordDataValid section14Catalog 15 (⟨399,(9),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1257 : RecordDataValid section14Catalog 15 (⟨403,(0),[3,15],[10],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1258 : RecordDataValid section14Catalog 15 (⟨403,(1),[3,15],[10],951⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨951,[3,7,11,15],955⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1259 : RecordDataValid section14Catalog 15 (⟨403,(2),[3,15],[10],952⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨952,[3,7,11,15],956⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1260 : RecordDataValid section14Catalog 15 (⟨403,(3),[3,15],[10],953⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨953,[3,7,11,15],957⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1261 : RecordDataValid section14Catalog 15 (⟨408,(0),[3,15],[10],957⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨957,[3,7,11,15],961⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1262 : RecordDataValid section14Catalog 15 (⟨408,(1),[3,7,15],[10],958⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨958,[3,7,11,15],962⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1263 : RecordDataValid section14Catalog 15 (⟨408,(2),[3,7,15],[10],959⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨959,[3,7,11,15],963⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1264 : RecordDataValid section14Catalog 15 (⟨408,(3),[3,7,15],[10],960⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨960,[3,7,11,15],964⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1265 : RecordDataValid section14Catalog 15 (⟨408,(4),[3,7,15],[10],961⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨961,[3,7,11,15],965⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1266 : RecordDataValid section14Catalog 15 (⟨413,(-1),[3,7,11,15],[0],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1267 : RecordDataValid section14Catalog 15 (⟨413,(-1),[3,7,15],[1,2,3],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1268 : RecordDataValid section14Catalog 15 (⟨413,(-1),[3,7,15],[4,5,6,7],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1269 : RecordDataValid section14Catalog 15 (⟨413,(-1),[3,7,15],[8],885⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨885,[1,2,3,5,6,7,13,14,15],887⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1270 : RecordDataValid section14Catalog 15 (⟨413,(-1),[3,7,15],[9],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1271 : RecordDataValid section14Catalog 15 (⟨413,(-1),[3,7,15],[11],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1272 : RecordDataValid section14Catalog 15 (⟨413,(-1),[3,7,15],[12,13,14,15],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1273 : RecordDataValid section14Catalog 15 (⟨415,(0),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1274 : RecordDataValid section14Catalog 15 (⟨415,(1),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1275 : RecordDataValid section14Catalog 15 (⟨415,(2),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1276 : RecordDataValid section14Catalog 15 (⟨415,(3),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1277 : RecordDataValid section14Catalog 15 (⟨415,(4),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1278 : RecordDataValid section14Catalog 15 (⟨415,(5),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1279 : RecordDataValid section14Catalog 15 (⟨415,(6),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1248).take 32 = [⟨399,(1),[3,7,15],[10],3⟩,⟨399,(2),[3,7,15],[10],3⟩,⟨399,(3),[3,7,15],[10],3⟩,⟨399,(4),[3,7,15],[10],3⟩,⟨399,(5),[3,7,15],[10],3⟩,⟨399,(6),[3,7,15],[10],3⟩,⟨399,(7),[3,7,15],[10],3⟩,⟨399,(8),[3,7,15],[10],3⟩,⟨399,(9),[3,7,15],[10],3⟩,⟨403,(0),[3,15],[10],711⟩,⟨403,(1),[3,15],[10],951⟩,⟨403,(2),[3,15],[10],952⟩,⟨403,(3),[3,15],[10],953⟩,⟨408,(0),[3,15],[10],957⟩,⟨408,(1),[3,7,15],[10],958⟩,⟨408,(2),[3,7,15],[10],959⟩,⟨408,(3),[3,7,15],[10],960⟩,⟨408,(4),[3,7,15],[10],961⟩,⟨413,(-1),[3,7,11,15],[0],881⟩,⟨413,(-1),[3,7,15],[1,2,3],881⟩,⟨413,(-1),[3,7,15],[4,5,6,7],883⟩,⟨413,(-1),[3,7,15],[8],885⟩,⟨413,(-1),[3,7,15],[9],887⟩,⟨413,(-1),[3,7,15],[11],908⟩,⟨413,(-1),[3,7,15],[12,13,14,15],910⟩,⟨415,(0),[3,7,15],[10],3⟩,⟨415,(1),[3,7,15],[10],3⟩,⟨415,(2),[3,7,15],[10],3⟩,⟨415,(3),[3,7,15],[10],3⟩,⟨415,(4),[3,7,15],[10],3⟩,⟨415,(5),[3,7,15],[10],3⟩,⟨415,(6),[3,7,15],[10],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1248
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1249
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1250
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1251
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1252
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1253
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1254
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1255
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1256
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1257
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1258
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1259
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1260
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1261
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1262
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1263
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1264
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1265
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1266
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1267
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1268
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1269
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1270
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1271
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1272
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1273
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1274
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1275
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1276
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1277
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1278
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1279
end Section14Records_15_1248_1280

#print axioms solution
