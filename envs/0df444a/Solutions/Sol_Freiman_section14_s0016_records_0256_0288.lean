-- Prove2me | solution 1 for Freiman.section14_s0016_records_0256_0288
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T22:42:23.947034+00:00
-- url     : https://prove2.me/submissions/dd225980-1922-44a6-a036-0171e5c8c85d

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
namespace Section14Records_16_256_288
private theorem valid256 : RecordDataValid section14Catalog 16 (⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid257 : RecordDataValid section14Catalog 16 (⟨47,(10),[4,8,12,16],[14],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid258 : RecordDataValid section14Catalog 16 (⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid259 : RecordDataValid section14Catalog 16 (⟨47,(11),[4,8,12,16],[14],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid260 : RecordDataValid section14Catalog 16 (⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid261 : RecordDataValid section14Catalog 16 (⟨47,(12),[4,8,12,16],[14],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid262 : RecordDataValid section14Catalog 16 (⟨47,(13),[3,4,7,15,16],[10],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid263 : RecordDataValid section14Catalog 16 (⟨47,(13),[4,8,12,16],[14],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid264 : RecordDataValid section14Catalog 16 (⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid265 : RecordDataValid section14Catalog 16 (⟨47,(14),[4,8,12,16],[14],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid266 : RecordDataValid section14Catalog 16 (⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid267 : RecordDataValid section14Catalog 16 (⟨47,(15),[4,8,12,16],[14],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid268 : RecordDataValid section14Catalog 16 (⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid269 : RecordDataValid section14Catalog 16 (⟨47,(16),[4,8,12,16],[14],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid270 : RecordDataValid section14Catalog 16 (⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid271 : RecordDataValid section14Catalog 16 (⟨47,(17),[4,8,12,16],[14],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid272 : RecordDataValid section14Catalog 16 (⟨47,(18),[3,4,7,15,16],[10],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid273 : RecordDataValid section14Catalog 16 (⟨47,(18),[4,8,12,16],[14],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid274 : RecordDataValid section14Catalog 16 (⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid275 : RecordDataValid section14Catalog 16 (⟨47,(19),[4,8,12,16],[14],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid276 : RecordDataValid section14Catalog 16 (⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid277 : RecordDataValid section14Catalog 16 (⟨47,(20),[4,8,12,16],[14],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid278 : RecordDataValid section14Catalog 16 (⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid279 : RecordDataValid section14Catalog 16 (⟨47,(21),[4,8,12,16],[14],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid280 : RecordDataValid section14Catalog 16 (⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid281 : RecordDataValid section14Catalog 16 (⟨47,(22),[4,8,12,16],[14],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid282 : RecordDataValid section14Catalog 16 (⟨47,(23),[3,4,7,15,16],[10],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid283 : RecordDataValid section14Catalog 16 (⟨47,(23),[4,8,12,16],[14],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid284 : RecordDataValid section14Catalog 16 (⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid285 : RecordDataValid section14Catalog 16 (⟨47,(24),[4,8,12,16],[14],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid286 : RecordDataValid section14Catalog 16 (⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨342,[1,2,4,5,6,8,9,10,12,13,14,16],343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid287 : RecordDataValid section14Catalog 16 (⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 256).take 32 = [⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩,⟨47,(10),[4,8,12,16],[14],194⟩,⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩,⟨47,(11),[4,8,12,16],[14],267⟩,⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩,⟨47,(12),[4,8,12,16],[14],322⟩,⟨47,(13),[3,4,7,15,16],[10],268⟩,⟨47,(13),[4,8,12,16],[14],322⟩,⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩,⟨47,(14),[4,8,12,16],[14],321⟩,⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩,⟨47,(15),[4,8,12,16],[14],196⟩,⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩,⟨47,(16),[4,8,12,16],[14],269⟩,⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩,⟨47,(17),[4,8,12,16],[14],323⟩,⟨47,(18),[3,4,7,15,16],[10],270⟩,⟨47,(18),[4,8,12,16],[14],323⟩,⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩,⟨47,(19),[4,8,12,16],[14],323⟩,⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩,⟨47,(20),[4,8,12,16],[14],198⟩,⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩,⟨47,(21),[4,8,12,16],[14],271⟩,⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩,⟨47,(22),[4,8,12,16],[14],324⟩,⟨47,(23),[3,4,7,15,16],[10],272⟩,⟨47,(23),[4,8,12,16],[14],324⟩,⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩,⟨47,(24),[4,8,12,16],[14],324⟩,⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩,⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid256
  · exact recordValid_of_data section14Catalog 16 _ hnum valid257
  · exact recordValid_of_data section14Catalog 16 _ hnum valid258
  · exact recordValid_of_data section14Catalog 16 _ hnum valid259
  · exact recordValid_of_data section14Catalog 16 _ hnum valid260
  · exact recordValid_of_data section14Catalog 16 _ hnum valid261
  · exact recordValid_of_data section14Catalog 16 _ hnum valid262
  · exact recordValid_of_data section14Catalog 16 _ hnum valid263
  · exact recordValid_of_data section14Catalog 16 _ hnum valid264
  · exact recordValid_of_data section14Catalog 16 _ hnum valid265
  · exact recordValid_of_data section14Catalog 16 _ hnum valid266
  · exact recordValid_of_data section14Catalog 16 _ hnum valid267
  · exact recordValid_of_data section14Catalog 16 _ hnum valid268
  · exact recordValid_of_data section14Catalog 16 _ hnum valid269
  · exact recordValid_of_data section14Catalog 16 _ hnum valid270
  · exact recordValid_of_data section14Catalog 16 _ hnum valid271
  · exact recordValid_of_data section14Catalog 16 _ hnum valid272
  · exact recordValid_of_data section14Catalog 16 _ hnum valid273
  · exact recordValid_of_data section14Catalog 16 _ hnum valid274
  · exact recordValid_of_data section14Catalog 16 _ hnum valid275
  · exact recordValid_of_data section14Catalog 16 _ hnum valid276
  · exact recordValid_of_data section14Catalog 16 _ hnum valid277
  · exact recordValid_of_data section14Catalog 16 _ hnum valid278
  · exact recordValid_of_data section14Catalog 16 _ hnum valid279
  · exact recordValid_of_data section14Catalog 16 _ hnum valid280
  · exact recordValid_of_data section14Catalog 16 _ hnum valid281
  · exact recordValid_of_data section14Catalog 16 _ hnum valid282
  · exact recordValid_of_data section14Catalog 16 _ hnum valid283
  · exact recordValid_of_data section14Catalog 16 _ hnum valid284
  · exact recordValid_of_data section14Catalog 16 _ hnum valid285
  · exact recordValid_of_data section14Catalog 16 _ hnum valid286
  · exact recordValid_of_data section14Catalog 16 _ hnum valid287
end Section14Records_16_256_288

#print axioms solution
