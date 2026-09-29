-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_0256_0384
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:46:32.480048+00:00
-- url     : https://prove2.me/submissions/93c6e41a-d8a7-4aa4-9fd4-5b4ec57406a5

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0256_0288
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_256_288
private theorem valid256 : RecordDataValid section14Catalog 6 (⟨18,(16),[6],[146],1519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1519,[6],1524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid257 : RecordDataValid section14Catalog 6 (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid258 : RecordDataValid section14Catalog 6 (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid259 : RecordDataValid section14Catalog 6 (⟨18,(17),[2,6],[130],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid260 : RecordDataValid section14Catalog 6 (⟨18,(17),[6],[146],1519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1519,[6],1524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid261 : RecordDataValid section14Catalog 6 (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid262 : RecordDataValid section14Catalog 6 (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid263 : RecordDataValid section14Catalog 6 (⟨18,(18),[2,6],[130],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid264 : RecordDataValid section14Catalog 6 (⟨18,(18),[6],[146],1519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1519,[6],1524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid265 : RecordDataValid section14Catalog 6 (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid266 : RecordDataValid section14Catalog 6 (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid267 : RecordDataValid section14Catalog 6 (⟨18,(19),[2,6],[130],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid268 : RecordDataValid section14Catalog 6 (⟨18,(19),[6],[146],1519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1519,[6],1524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid269 : RecordDataValid section14Catalog 6 (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid270 : RecordDataValid section14Catalog 6 (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid271 : RecordDataValid section14Catalog 6 (⟨18,(20),[2,6],[130],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid272 : RecordDataValid section14Catalog 6 (⟨18,(20),[6],[146],1515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1515,[6],1520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid273 : RecordDataValid section14Catalog 6 (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid274 : RecordDataValid section14Catalog 6 (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid275 : RecordDataValid section14Catalog 6 (⟨18,(21),[2,6],[130],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid276 : RecordDataValid section14Catalog 6 (⟨18,(21),[6],[146],1516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1516,[6],1521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid277 : RecordDataValid section14Catalog 6 (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid278 : RecordDataValid section14Catalog 6 (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid279 : RecordDataValid section14Catalog 6 (⟨18,(22),[2,6],[130],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid280 : RecordDataValid section14Catalog 6 (⟨18,(22),[6],[146],1517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1517,[6],1522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid281 : RecordDataValid section14Catalog 6 (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid282 : RecordDataValid section14Catalog 6 (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid283 : RecordDataValid section14Catalog 6 (⟨18,(23),[2,6],[130],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid284 : RecordDataValid section14Catalog 6 (⟨18,(23),[6],[146],1516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1516,[6],1521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid285 : RecordDataValid section14Catalog 6 (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid286 : RecordDataValid section14Catalog 6 (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨130,[1,2,5,6,13,14],130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid287 : RecordDataValid section14Catalog 6 (⟨18,(24),[2,6],[130],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0256_0288 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 256).take 32 = [⟨18,(16),[6],[146],1519⟩,⟨18,(17),[1,2,5,6,13,14],[131],112⟩,⟨18,(17),[1,2,5,6,13,14],[150],131⟩,⟨18,(17),[2,6],[130],112⟩,⟨18,(17),[6],[146],1519⟩,⟨18,(18),[1,2,5,6,13,14],[131],112⟩,⟨18,(18),[1,2,5,6,13,14],[150],131⟩,⟨18,(18),[2,6],[130],112⟩,⟨18,(18),[6],[146],1519⟩,⟨18,(19),[1,2,5,6,13,14],[131],112⟩,⟨18,(19),[1,2,5,6,13,14],[150],131⟩,⟨18,(19),[2,6],[130],112⟩,⟨18,(19),[6],[146],1519⟩,⟨18,(20),[1,2,5,6,13,14],[131],108⟩,⟨18,(20),[1,2,5,6,13,14],[150],127⟩,⟨18,(20),[2,6],[130],108⟩,⟨18,(20),[6],[146],1515⟩,⟨18,(21),[1,2,5,6,13,14],[131],109⟩,⟨18,(21),[1,2,5,6,13,14],[150],128⟩,⟨18,(21),[2,6],[130],109⟩,⟨18,(21),[6],[146],1516⟩,⟨18,(22),[1,2,5,6,13,14],[131],110⟩,⟨18,(22),[1,2,5,6,13,14],[150],129⟩,⟨18,(22),[2,6],[130],110⟩,⟨18,(22),[6],[146],1517⟩,⟨18,(23),[1,2,5,6,13,14],[131],109⟩,⟨18,(23),[1,2,5,6,13,14],[150],128⟩,⟨18,(23),[2,6],[130],109⟩,⟨18,(23),[6],[146],1516⟩,⟨18,(24),[1,2,5,6,13,14],[131],111⟩,⟨18,(24),[1,2,5,6,13,14],[150],130⟩,⟨18,(24),[2,6],[130],111⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid256
  · exact recordValid_of_data section14Catalog 6 _ hnum valid257
  · exact recordValid_of_data section14Catalog 6 _ hnum valid258
  · exact recordValid_of_data section14Catalog 6 _ hnum valid259
  · exact recordValid_of_data section14Catalog 6 _ hnum valid260
  · exact recordValid_of_data section14Catalog 6 _ hnum valid261
  · exact recordValid_of_data section14Catalog 6 _ hnum valid262
  · exact recordValid_of_data section14Catalog 6 _ hnum valid263
  · exact recordValid_of_data section14Catalog 6 _ hnum valid264
  · exact recordValid_of_data section14Catalog 6 _ hnum valid265
  · exact recordValid_of_data section14Catalog 6 _ hnum valid266
  · exact recordValid_of_data section14Catalog 6 _ hnum valid267
  · exact recordValid_of_data section14Catalog 6 _ hnum valid268
  · exact recordValid_of_data section14Catalog 6 _ hnum valid269
  · exact recordValid_of_data section14Catalog 6 _ hnum valid270
  · exact recordValid_of_data section14Catalog 6 _ hnum valid271
  · exact recordValid_of_data section14Catalog 6 _ hnum valid272
  · exact recordValid_of_data section14Catalog 6 _ hnum valid273
  · exact recordValid_of_data section14Catalog 6 _ hnum valid274
  · exact recordValid_of_data section14Catalog 6 _ hnum valid275
  · exact recordValid_of_data section14Catalog 6 _ hnum valid276
  · exact recordValid_of_data section14Catalog 6 _ hnum valid277
  · exact recordValid_of_data section14Catalog 6 _ hnum valid278
  · exact recordValid_of_data section14Catalog 6 _ hnum valid279
  · exact recordValid_of_data section14Catalog 6 _ hnum valid280
  · exact recordValid_of_data section14Catalog 6 _ hnum valid281
  · exact recordValid_of_data section14Catalog 6 _ hnum valid282
  · exact recordValid_of_data section14Catalog 6 _ hnum valid283
  · exact recordValid_of_data section14Catalog 6 _ hnum valid284
  · exact recordValid_of_data section14Catalog 6 _ hnum valid285
  · exact recordValid_of_data section14Catalog 6 _ hnum valid286
  · exact recordValid_of_data section14Catalog 6 _ hnum valid287
end Section14Records_6_256_288

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0256_0288


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0288_0320
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_288_320
private theorem valid288 : RecordDataValid section14Catalog 6 (⟨18,(24),[6],[146],1518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1518,[6],1523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid289 : RecordDataValid section14Catalog 6 (⟨20,(0),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid290 : RecordDataValid section14Catalog 6 (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid291 : RecordDataValid section14Catalog 6 (⟨20,(1),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid292 : RecordDataValid section14Catalog 6 (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid293 : RecordDataValid section14Catalog 6 (⟨20,(2),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid294 : RecordDataValid section14Catalog 6 (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid295 : RecordDataValid section14Catalog 6 (⟨20,(3),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid296 : RecordDataValid section14Catalog 6 (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid297 : RecordDataValid section14Catalog 6 (⟨20,(4),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid298 : RecordDataValid section14Catalog 6 (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid299 : RecordDataValid section14Catalog 6 (⟨20,(5),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid300 : RecordDataValid section14Catalog 6 (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid301 : RecordDataValid section14Catalog 6 (⟨20,(6),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid302 : RecordDataValid section14Catalog 6 (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid303 : RecordDataValid section14Catalog 6 (⟨20,(7),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid304 : RecordDataValid section14Catalog 6 (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid305 : RecordDataValid section14Catalog 6 (⟨20,(8),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid306 : RecordDataValid section14Catalog 6 (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid307 : RecordDataValid section14Catalog 6 (⟨20,(9),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid308 : RecordDataValid section14Catalog 6 (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid309 : RecordDataValid section14Catalog 6 (⟨20,(10),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid310 : RecordDataValid section14Catalog 6 (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid311 : RecordDataValid section14Catalog 6 (⟨20,(11),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid312 : RecordDataValid section14Catalog 6 (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid313 : RecordDataValid section14Catalog 6 (⟨20,(12),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid314 : RecordDataValid section14Catalog 6 (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid315 : RecordDataValid section14Catalog 6 (⟨20,(13),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid316 : RecordDataValid section14Catalog 6 (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid317 : RecordDataValid section14Catalog 6 (⟨20,(14),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid318 : RecordDataValid section14Catalog 6 (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid319 : RecordDataValid section14Catalog 6 (⟨20,(15),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0288_0320 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 288).take 32 = [⟨18,(24),[6],[146],1518⟩,⟨20,(0),[1,2,5,6],[130],3⟩,⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(1),[1,2,5,6],[130],3⟩,⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(2),[1,2,5,6],[130],3⟩,⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(3),[1,2,5,6],[130],3⟩,⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(4),[1,2,5,6],[130],3⟩,⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(5),[1,2,5,6],[130],3⟩,⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(6),[1,2,5,6],[130],3⟩,⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(7),[1,2,5,6],[130],3⟩,⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(8),[1,2,5,6],[130],3⟩,⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(9),[1,2,5,6],[130],3⟩,⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(10),[1,2,5,6],[130],3⟩,⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(11),[1,2,5,6],[130],3⟩,⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(12),[1,2,5,6],[130],3⟩,⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(13),[1,2,5,6],[130],3⟩,⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(14),[1,2,5,6],[130],3⟩,⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(15),[1,2,5,6],[130],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid288
  · exact recordValid_of_data section14Catalog 6 _ hnum valid289
  · exact recordValid_of_data section14Catalog 6 _ hnum valid290
  · exact recordValid_of_data section14Catalog 6 _ hnum valid291
  · exact recordValid_of_data section14Catalog 6 _ hnum valid292
  · exact recordValid_of_data section14Catalog 6 _ hnum valid293
  · exact recordValid_of_data section14Catalog 6 _ hnum valid294
  · exact recordValid_of_data section14Catalog 6 _ hnum valid295
  · exact recordValid_of_data section14Catalog 6 _ hnum valid296
  · exact recordValid_of_data section14Catalog 6 _ hnum valid297
  · exact recordValid_of_data section14Catalog 6 _ hnum valid298
  · exact recordValid_of_data section14Catalog 6 _ hnum valid299
  · exact recordValid_of_data section14Catalog 6 _ hnum valid300
  · exact recordValid_of_data section14Catalog 6 _ hnum valid301
  · exact recordValid_of_data section14Catalog 6 _ hnum valid302
  · exact recordValid_of_data section14Catalog 6 _ hnum valid303
  · exact recordValid_of_data section14Catalog 6 _ hnum valid304
  · exact recordValid_of_data section14Catalog 6 _ hnum valid305
  · exact recordValid_of_data section14Catalog 6 _ hnum valid306
  · exact recordValid_of_data section14Catalog 6 _ hnum valid307
  · exact recordValid_of_data section14Catalog 6 _ hnum valid308
  · exact recordValid_of_data section14Catalog 6 _ hnum valid309
  · exact recordValid_of_data section14Catalog 6 _ hnum valid310
  · exact recordValid_of_data section14Catalog 6 _ hnum valid311
  · exact recordValid_of_data section14Catalog 6 _ hnum valid312
  · exact recordValid_of_data section14Catalog 6 _ hnum valid313
  · exact recordValid_of_data section14Catalog 6 _ hnum valid314
  · exact recordValid_of_data section14Catalog 6 _ hnum valid315
  · exact recordValid_of_data section14Catalog 6 _ hnum valid316
  · exact recordValid_of_data section14Catalog 6 _ hnum valid317
  · exact recordValid_of_data section14Catalog 6 _ hnum valid318
  · exact recordValid_of_data section14Catalog 6 _ hnum valid319
end Section14Records_6_288_320

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0288_0320


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0320_0352
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_320_352
private theorem valid320 : RecordDataValid section14Catalog 6 (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid321 : RecordDataValid section14Catalog 6 (⟨20,(16),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid322 : RecordDataValid section14Catalog 6 (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid323 : RecordDataValid section14Catalog 6 (⟨20,(17),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid324 : RecordDataValid section14Catalog 6 (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid325 : RecordDataValid section14Catalog 6 (⟨20,(18),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid326 : RecordDataValid section14Catalog 6 (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid327 : RecordDataValid section14Catalog 6 (⟨20,(19),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid328 : RecordDataValid section14Catalog 6 (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid329 : RecordDataValid section14Catalog 6 (⟨20,(20),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid330 : RecordDataValid section14Catalog 6 (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid331 : RecordDataValid section14Catalog 6 (⟨20,(21),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid332 : RecordDataValid section14Catalog 6 (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid333 : RecordDataValid section14Catalog 6 (⟨20,(22),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid334 : RecordDataValid section14Catalog 6 (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid335 : RecordDataValid section14Catalog 6 (⟨20,(23),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid336 : RecordDataValid section14Catalog 6 (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid337 : RecordDataValid section14Catalog 6 (⟨20,(24),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid338 : RecordDataValid section14Catalog 6 (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid339 : RecordDataValid section14Catalog 6 (⟨23,(0),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid340 : RecordDataValid section14Catalog 6 (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid341 : RecordDataValid section14Catalog 6 (⟨23,(1),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid342 : RecordDataValid section14Catalog 6 (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid343 : RecordDataValid section14Catalog 6 (⟨23,(2),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid344 : RecordDataValid section14Catalog 6 (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid345 : RecordDataValid section14Catalog 6 (⟨23,(3),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid346 : RecordDataValid section14Catalog 6 (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid347 : RecordDataValid section14Catalog 6 (⟨23,(4),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid348 : RecordDataValid section14Catalog 6 (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid349 : RecordDataValid section14Catalog 6 (⟨23,(5),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid350 : RecordDataValid section14Catalog 6 (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid351 : RecordDataValid section14Catalog 6 (⟨23,(6),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0320_0352 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 320).take 32 = [⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(16),[1,2,5,6],[130],3⟩,⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(17),[1,2,5,6],[130],3⟩,⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(18),[1,2,5,6],[130],3⟩,⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(19),[1,2,5,6],[130],3⟩,⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(20),[1,2,5,6],[130],3⟩,⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(21),[1,2,5,6],[130],3⟩,⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(22),[1,2,5,6],[130],3⟩,⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(23),[1,2,5,6],[130],3⟩,⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩,⟨20,(24),[1,2,5,6],[130],3⟩,⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩,⟨23,(0),[1,2,5,6],[130],2⟩,⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(1),[1,2,5,6],[130],2⟩,⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(2),[1,2,5,6],[130],2⟩,⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(3),[1,2,5,6],[130],2⟩,⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(4),[1,2,5,6],[130],2⟩,⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(5),[1,2,5,6],[130],2⟩,⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(6),[1,2,5,6],[130],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid320
  · exact recordValid_of_data section14Catalog 6 _ hnum valid321
  · exact recordValid_of_data section14Catalog 6 _ hnum valid322
  · exact recordValid_of_data section14Catalog 6 _ hnum valid323
  · exact recordValid_of_data section14Catalog 6 _ hnum valid324
  · exact recordValid_of_data section14Catalog 6 _ hnum valid325
  · exact recordValid_of_data section14Catalog 6 _ hnum valid326
  · exact recordValid_of_data section14Catalog 6 _ hnum valid327
  · exact recordValid_of_data section14Catalog 6 _ hnum valid328
  · exact recordValid_of_data section14Catalog 6 _ hnum valid329
  · exact recordValid_of_data section14Catalog 6 _ hnum valid330
  · exact recordValid_of_data section14Catalog 6 _ hnum valid331
  · exact recordValid_of_data section14Catalog 6 _ hnum valid332
  · exact recordValid_of_data section14Catalog 6 _ hnum valid333
  · exact recordValid_of_data section14Catalog 6 _ hnum valid334
  · exact recordValid_of_data section14Catalog 6 _ hnum valid335
  · exact recordValid_of_data section14Catalog 6 _ hnum valid336
  · exact recordValid_of_data section14Catalog 6 _ hnum valid337
  · exact recordValid_of_data section14Catalog 6 _ hnum valid338
  · exact recordValid_of_data section14Catalog 6 _ hnum valid339
  · exact recordValid_of_data section14Catalog 6 _ hnum valid340
  · exact recordValid_of_data section14Catalog 6 _ hnum valid341
  · exact recordValid_of_data section14Catalog 6 _ hnum valid342
  · exact recordValid_of_data section14Catalog 6 _ hnum valid343
  · exact recordValid_of_data section14Catalog 6 _ hnum valid344
  · exact recordValid_of_data section14Catalog 6 _ hnum valid345
  · exact recordValid_of_data section14Catalog 6 _ hnum valid346
  · exact recordValid_of_data section14Catalog 6 _ hnum valid347
  · exact recordValid_of_data section14Catalog 6 _ hnum valid348
  · exact recordValid_of_data section14Catalog 6 _ hnum valid349
  · exact recordValid_of_data section14Catalog 6 _ hnum valid350
  · exact recordValid_of_data section14Catalog 6 _ hnum valid351
end Section14Records_6_320_352

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0320_0352


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0352_0384
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_352_384
private theorem valid352 : RecordDataValid section14Catalog 6 (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid353 : RecordDataValid section14Catalog 6 (⟨23,(7),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid354 : RecordDataValid section14Catalog 6 (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid355 : RecordDataValid section14Catalog 6 (⟨23,(8),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid356 : RecordDataValid section14Catalog 6 (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid357 : RecordDataValid section14Catalog 6 (⟨23,(9),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid358 : RecordDataValid section14Catalog 6 (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid359 : RecordDataValid section14Catalog 6 (⟨23,(10),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid360 : RecordDataValid section14Catalog 6 (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid361 : RecordDataValid section14Catalog 6 (⟨23,(11),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid362 : RecordDataValid section14Catalog 6 (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid363 : RecordDataValid section14Catalog 6 (⟨23,(12),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid364 : RecordDataValid section14Catalog 6 (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid365 : RecordDataValid section14Catalog 6 (⟨23,(13),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid366 : RecordDataValid section14Catalog 6 (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid367 : RecordDataValid section14Catalog 6 (⟨23,(14),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid368 : RecordDataValid section14Catalog 6 (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid369 : RecordDataValid section14Catalog 6 (⟨23,(15),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid370 : RecordDataValid section14Catalog 6 (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid371 : RecordDataValid section14Catalog 6 (⟨23,(16),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid372 : RecordDataValid section14Catalog 6 (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid373 : RecordDataValid section14Catalog 6 (⟨23,(17),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid374 : RecordDataValid section14Catalog 6 (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid375 : RecordDataValid section14Catalog 6 (⟨23,(18),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid376 : RecordDataValid section14Catalog 6 (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid377 : RecordDataValid section14Catalog 6 (⟨23,(19),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid378 : RecordDataValid section14Catalog 6 (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid379 : RecordDataValid section14Catalog 6 (⟨23,(20),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid380 : RecordDataValid section14Catalog 6 (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid381 : RecordDataValid section14Catalog 6 (⟨23,(21),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid382 : RecordDataValid section14Catalog 6 (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid383 : RecordDataValid section14Catalog 6 (⟨23,(22),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0352_0384 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 352).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 352).take 32 = [⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(7),[1,2,5,6],[130],2⟩,⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(8),[1,2,5,6],[130],2⟩,⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(9),[1,2,5,6],[130],2⟩,⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(10),[1,2,5,6],[130],2⟩,⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(11),[1,2,5,6],[130],2⟩,⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(12),[1,2,5,6],[130],2⟩,⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(13),[1,2,5,6],[130],2⟩,⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(14),[1,2,5,6],[130],2⟩,⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(15),[1,2,5,6],[130],2⟩,⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(16),[1,2,5,6],[130],2⟩,⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(17),[1,2,5,6],[130],2⟩,⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(18),[1,2,5,6],[130],2⟩,⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(19),[1,2,5,6],[130],2⟩,⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(20),[1,2,5,6],[130],2⟩,⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(21),[1,2,5,6],[130],2⟩,⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(22),[1,2,5,6],[130],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid352
  · exact recordValid_of_data section14Catalog 6 _ hnum valid353
  · exact recordValid_of_data section14Catalog 6 _ hnum valid354
  · exact recordValid_of_data section14Catalog 6 _ hnum valid355
  · exact recordValid_of_data section14Catalog 6 _ hnum valid356
  · exact recordValid_of_data section14Catalog 6 _ hnum valid357
  · exact recordValid_of_data section14Catalog 6 _ hnum valid358
  · exact recordValid_of_data section14Catalog 6 _ hnum valid359
  · exact recordValid_of_data section14Catalog 6 _ hnum valid360
  · exact recordValid_of_data section14Catalog 6 _ hnum valid361
  · exact recordValid_of_data section14Catalog 6 _ hnum valid362
  · exact recordValid_of_data section14Catalog 6 _ hnum valid363
  · exact recordValid_of_data section14Catalog 6 _ hnum valid364
  · exact recordValid_of_data section14Catalog 6 _ hnum valid365
  · exact recordValid_of_data section14Catalog 6 _ hnum valid366
  · exact recordValid_of_data section14Catalog 6 _ hnum valid367
  · exact recordValid_of_data section14Catalog 6 _ hnum valid368
  · exact recordValid_of_data section14Catalog 6 _ hnum valid369
  · exact recordValid_of_data section14Catalog 6 _ hnum valid370
  · exact recordValid_of_data section14Catalog 6 _ hnum valid371
  · exact recordValid_of_data section14Catalog 6 _ hnum valid372
  · exact recordValid_of_data section14Catalog 6 _ hnum valid373
  · exact recordValid_of_data section14Catalog 6 _ hnum valid374
  · exact recordValid_of_data section14Catalog 6 _ hnum valid375
  · exact recordValid_of_data section14Catalog 6 _ hnum valid376
  · exact recordValid_of_data section14Catalog 6 _ hnum valid377
  · exact recordValid_of_data section14Catalog 6 _ hnum valid378
  · exact recordValid_of_data section14Catalog 6 _ hnum valid379
  · exact recordValid_of_data section14Catalog 6 _ hnum valid380
  · exact recordValid_of_data section14Catalog 6 _ hnum valid381
  · exact recordValid_of_data section14Catalog 6 _ hnum valid382
  · exact recordValid_of_data section14Catalog 6 _ hnum valid383
end Section14Records_6_352_384

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0352_0384

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 256).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 256 320 384 (by decide) (by decide) (all_of_interval_split P xs 256 288 320 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0256_0288 hnum) (Freiman.workReverse20260919_s0006_records_0288_0320 hnum)) (all_of_interval_split P xs 320 352 384 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0320_0352 hnum) (Freiman.workReverse20260919_s0006_records_0352_0384 hnum)))

#print axioms solution
