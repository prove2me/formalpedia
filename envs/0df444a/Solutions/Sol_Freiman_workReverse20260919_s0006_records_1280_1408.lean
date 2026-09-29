-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_1280_1408
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:49:06.934249+00:00
-- url     : https://prove2.me/submissions/583bafeb-bb47-45e4-930e-c99528fcea2a

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1280_1312
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1280_1312
private theorem valid1280 : RecordDataValid section14Catalog 6 (⟨62,(10),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1281 : RecordDataValid section14Catalog 6 (⟨62,(11),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1282 : RecordDataValid section14Catalog 6 (⟨62,(11),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1283 : RecordDataValid section14Catalog 6 (⟨62,(12),[1,2,5,6],[150],351⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨351,[1,2,3,5,6,7,9,10,11],352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1284 : RecordDataValid section14Catalog 6 (⟨62,(12),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1285 : RecordDataValid section14Catalog 6 (⟨62,(13),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1286 : RecordDataValid section14Catalog 6 (⟨62,(13),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1287 : RecordDataValid section14Catalog 6 (⟨62,(14),[1,2,5,6],[150],352⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨352,[1,2,5,6,9,10],353⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1288 : RecordDataValid section14Catalog 6 (⟨62,(14),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1289 : RecordDataValid section14Catalog 6 (⟨62,(15),[1,2,5,6],[150],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1290 : RecordDataValid section14Catalog 6 (⟨62,(15),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1291 : RecordDataValid section14Catalog 6 (⟨62,(16),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1292 : RecordDataValid section14Catalog 6 (⟨62,(16),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1293 : RecordDataValid section14Catalog 6 (⟨62,(17),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1294 : RecordDataValid section14Catalog 6 (⟨62,(17),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1295 : RecordDataValid section14Catalog 6 (⟨62,(18),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1296 : RecordDataValid section14Catalog 6 (⟨62,(18),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1297 : RecordDataValid section14Catalog 6 (⟨62,(19),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1298 : RecordDataValid section14Catalog 6 (⟨62,(19),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1299 : RecordDataValid section14Catalog 6 (⟨62,(20),[1,2,5,6],[150],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1300 : RecordDataValid section14Catalog 6 (⟨62,(20),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1301 : RecordDataValid section14Catalog 6 (⟨62,(21),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1302 : RecordDataValid section14Catalog 6 (⟨62,(21),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1303 : RecordDataValid section14Catalog 6 (⟨62,(22),[1,2,5,6],[150],351⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨351,[1,2,3,5,6,7,9,10,11],352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1304 : RecordDataValid section14Catalog 6 (⟨62,(22),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1305 : RecordDataValid section14Catalog 6 (⟨62,(23),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1306 : RecordDataValid section14Catalog 6 (⟨62,(23),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1307 : RecordDataValid section14Catalog 6 (⟨62,(24),[1,2,5,6],[150],352⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨352,[1,2,5,6,9,10],353⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1308 : RecordDataValid section14Catalog 6 (⟨62,(24),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1309 : RecordDataValid section14Catalog 6 (⟨64,(0),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1310 : RecordDataValid section14Catalog 6 (⟨64,(0),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1311 : RecordDataValid section14Catalog 6 (⟨64,(1),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1280_1312 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1280).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1280).take 32 = [⟨62,(10),[1,2,5,6,13,14],[190],3⟩,⟨62,(11),[1,2,5,6],[150],350⟩,⟨62,(11),[1,2,5,6,13,14],[190],3⟩,⟨62,(12),[1,2,5,6],[150],351⟩,⟨62,(12),[1,2,5,6,13,14],[190],3⟩,⟨62,(13),[1,2,5,6],[150],350⟩,⟨62,(13),[1,2,5,6,13,14],[190],3⟩,⟨62,(14),[1,2,5,6],[150],352⟩,⟨62,(14),[1,2,5,6,13,14],[190],3⟩,⟨62,(15),[1,2,5,6],[150],349⟩,⟨62,(15),[1,2,5,6,13,14],[190],3⟩,⟨62,(16),[1,2,5,6],[150],353⟩,⟨62,(16),[1,2,5,6,13,14],[190],3⟩,⟨62,(17),[1,2,5,6],[150],353⟩,⟨62,(17),[1,2,5,6,13,14],[190],3⟩,⟨62,(18),[1,2,5,6],[150],353⟩,⟨62,(18),[1,2,5,6,13,14],[190],3⟩,⟨62,(19),[1,2,5,6],[150],353⟩,⟨62,(19),[1,2,5,6,13,14],[190],3⟩,⟨62,(20),[1,2,5,6],[150],349⟩,⟨62,(20),[1,2,5,6,13,14],[190],3⟩,⟨62,(21),[1,2,5,6],[150],350⟩,⟨62,(21),[1,2,5,6,13,14],[190],3⟩,⟨62,(22),[1,2,5,6],[150],351⟩,⟨62,(22),[1,2,5,6,13,14],[190],3⟩,⟨62,(23),[1,2,5,6],[150],350⟩,⟨62,(23),[1,2,5,6,13,14],[190],3⟩,⟨62,(24),[1,2,5,6],[150],352⟩,⟨62,(24),[1,2,5,6,13,14],[190],3⟩,⟨64,(0),[1,2,5,6],[150],3⟩,⟨64,(0),[1,2,5,6,13,14],[190],368⟩,⟨64,(1),[1,2,5,6],[150],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1280
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1281
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1282
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1283
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1284
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1285
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1286
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1287
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1288
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1289
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1290
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1291
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1292
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1293
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1294
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1295
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1296
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1297
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1298
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1299
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1300
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1301
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1302
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1303
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1304
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1305
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1306
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1307
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1308
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1309
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1310
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1311
end Section14Records_6_1280_1312

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1280_1312


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1312_1344
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1312_1344
private theorem valid1312 : RecordDataValid section14Catalog 6 (⟨64,(1),[1,2,5,6,13,14],[190],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1313 : RecordDataValid section14Catalog 6 (⟨64,(2),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1314 : RecordDataValid section14Catalog 6 (⟨64,(2),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1315 : RecordDataValid section14Catalog 6 (⟨64,(3),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1316 : RecordDataValid section14Catalog 6 (⟨64,(3),[1,2,5,6,13,14],[190],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1317 : RecordDataValid section14Catalog 6 (⟨64,(4),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1318 : RecordDataValid section14Catalog 6 (⟨64,(4),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1319 : RecordDataValid section14Catalog 6 (⟨64,(5),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1320 : RecordDataValid section14Catalog 6 (⟨64,(5),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1321 : RecordDataValid section14Catalog 6 (⟨64,(6),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1322 : RecordDataValid section14Catalog 6 (⟨64,(6),[1,2,5,6,13,14],[190],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1323 : RecordDataValid section14Catalog 6 (⟨64,(7),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1324 : RecordDataValid section14Catalog 6 (⟨64,(7),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1325 : RecordDataValid section14Catalog 6 (⟨64,(8),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1326 : RecordDataValid section14Catalog 6 (⟨64,(8),[1,2,5,6,13,14],[190],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1327 : RecordDataValid section14Catalog 6 (⟨64,(9),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1328 : RecordDataValid section14Catalog 6 (⟨64,(9),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1329 : RecordDataValid section14Catalog 6 (⟨64,(10),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1330 : RecordDataValid section14Catalog 6 (⟨64,(10),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1331 : RecordDataValid section14Catalog 6 (⟨64,(11),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1332 : RecordDataValid section14Catalog 6 (⟨64,(11),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1333 : RecordDataValid section14Catalog 6 (⟨64,(12),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1334 : RecordDataValid section14Catalog 6 (⟨64,(12),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1335 : RecordDataValid section14Catalog 6 (⟨64,(13),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1336 : RecordDataValid section14Catalog 6 (⟨64,(13),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1337 : RecordDataValid section14Catalog 6 (⟨64,(14),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1338 : RecordDataValid section14Catalog 6 (⟨64,(14),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1339 : RecordDataValid section14Catalog 6 (⟨64,(15),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1340 : RecordDataValid section14Catalog 6 (⟨64,(15),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1341 : RecordDataValid section14Catalog 6 (⟨64,(16),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1342 : RecordDataValid section14Catalog 6 (⟨64,(16),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1343 : RecordDataValid section14Catalog 6 (⟨64,(17),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1312_1344 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1312).take 32 = [⟨64,(1),[1,2,5,6,13,14],[190],369⟩,⟨64,(2),[1,2,5,6],[150],3⟩,⟨64,(2),[1,2,5,6,13,14],[190],368⟩,⟨64,(3),[1,2,5,6],[150],3⟩,⟨64,(3),[1,2,5,6,13,14],[190],370⟩,⟨64,(4),[1,2,5,6],[150],3⟩,⟨64,(4),[1,2,5,6,13,14],[190],371⟩,⟨64,(5),[1,2,5,6],[150],3⟩,⟨64,(5),[1,2,5,6,13,14],[190],368⟩,⟨64,(6),[1,2,5,6],[150],3⟩,⟨64,(6),[1,2,5,6,13,14],[190],369⟩,⟨64,(7),[1,2,5,6],[150],3⟩,⟨64,(7),[1,2,5,6,13,14],[190],368⟩,⟨64,(8),[1,2,5,6],[150],3⟩,⟨64,(8),[1,2,5,6,13,14],[190],370⟩,⟨64,(9),[1,2,5,6],[150],3⟩,⟨64,(9),[1,2,5,6,13,14],[190],371⟩,⟨64,(10),[1,2,5,6],[150],3⟩,⟨64,(10),[1,2,5,6,13,14],[190],372⟩,⟨64,(11),[1,2,5,6],[150],3⟩,⟨64,(11),[1,2,5,6,13,14],[190],372⟩,⟨64,(12),[1,2,5,6],[150],3⟩,⟨64,(12),[1,2,5,6,13,14],[190],372⟩,⟨64,(13),[1,2,5,6],[150],3⟩,⟨64,(13),[1,2,5,6,13,14],[190],372⟩,⟨64,(14),[1,2,5,6],[150],3⟩,⟨64,(14),[1,2,5,6,13,14],[190],371⟩,⟨64,(15),[1,2,5,6],[150],3⟩,⟨64,(15),[1,2,5,6,13,14],[190],373⟩,⟨64,(16),[1,2,5,6],[150],3⟩,⟨64,(16),[1,2,5,6,13,14],[190],373⟩,⟨64,(17),[1,2,5,6],[150],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1312
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1313
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1314
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1315
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1316
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1317
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1318
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1319
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1320
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1321
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1322
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1323
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1324
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1325
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1326
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1327
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1328
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1329
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1330
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1331
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1332
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1333
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1334
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1335
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1336
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1337
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1338
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1339
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1340
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1341
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1342
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1343
end Section14Records_6_1312_1344

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1312_1344


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1344_1376
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1344_1376
private theorem valid1344 : RecordDataValid section14Catalog 6 (⟨64,(17),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1345 : RecordDataValid section14Catalog 6 (⟨64,(18),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1346 : RecordDataValid section14Catalog 6 (⟨64,(18),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1347 : RecordDataValid section14Catalog 6 (⟨64,(19),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1348 : RecordDataValid section14Catalog 6 (⟨64,(19),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1349 : RecordDataValid section14Catalog 6 (⟨64,(20),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1350 : RecordDataValid section14Catalog 6 (⟨64,(20),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1351 : RecordDataValid section14Catalog 6 (⟨64,(21),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1352 : RecordDataValid section14Catalog 6 (⟨64,(21),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1353 : RecordDataValid section14Catalog 6 (⟨64,(22),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1354 : RecordDataValid section14Catalog 6 (⟨64,(22),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1355 : RecordDataValid section14Catalog 6 (⟨64,(23),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1356 : RecordDataValid section14Catalog 6 (⟨64,(23),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1357 : RecordDataValid section14Catalog 6 (⟨64,(24),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1358 : RecordDataValid section14Catalog 6 (⟨64,(24),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1359 : RecordDataValid section14Catalog 6 (⟨67,(0),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1360 : RecordDataValid section14Catalog 6 (⟨67,(0),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1361 : RecordDataValid section14Catalog 6 (⟨67,(1),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1362 : RecordDataValid section14Catalog 6 (⟨67,(1),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1363 : RecordDataValid section14Catalog 6 (⟨67,(2),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1364 : RecordDataValid section14Catalog 6 (⟨67,(2),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1365 : RecordDataValid section14Catalog 6 (⟨67,(3),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1366 : RecordDataValid section14Catalog 6 (⟨67,(3),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1367 : RecordDataValid section14Catalog 6 (⟨67,(4),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1368 : RecordDataValid section14Catalog 6 (⟨67,(4),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1369 : RecordDataValid section14Catalog 6 (⟨67,(5),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1370 : RecordDataValid section14Catalog 6 (⟨67,(5),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1371 : RecordDataValid section14Catalog 6 (⟨67,(6),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1372 : RecordDataValid section14Catalog 6 (⟨67,(6),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1373 : RecordDataValid section14Catalog 6 (⟨67,(7),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1374 : RecordDataValid section14Catalog 6 (⟨67,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1375 : RecordDataValid section14Catalog 6 (⟨67,(8),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1344_1376 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1344).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1344).take 32 = [⟨64,(17),[1,2,5,6,13,14],[190],373⟩,⟨64,(18),[1,2,5,6],[150],3⟩,⟨64,(18),[1,2,5,6,13,14],[190],373⟩,⟨64,(19),[1,2,5,6],[150],3⟩,⟨64,(19),[1,2,5,6,13,14],[190],373⟩,⟨64,(20),[1,2,5,6],[150],3⟩,⟨64,(20),[1,2,5,6,13,14],[190],374⟩,⟨64,(21),[1,2,5,6],[150],3⟩,⟨64,(21),[1,2,5,6,13,14],[190],374⟩,⟨64,(22),[1,2,5,6],[150],3⟩,⟨64,(22),[1,2,5,6,13,14],[190],374⟩,⟨64,(23),[1,2,5,6],[150],3⟩,⟨64,(23),[1,2,5,6,13,14],[190],374⟩,⟨64,(24),[1,2,5,6],[150],3⟩,⟨64,(24),[1,2,5,6,13,14],[190],374⟩,⟨67,(0),[1,2,5,6],[150],2⟩,⟨67,(0),[1,2,5,6,13,14],[190],2⟩,⟨67,(1),[1,2,5,6],[150],2⟩,⟨67,(1),[1,2,5,6,13,14],[190],2⟩,⟨67,(2),[1,2,5,6],[150],2⟩,⟨67,(2),[1,2,5,6,13,14],[190],2⟩,⟨67,(3),[1,2,5,6],[150],2⟩,⟨67,(3),[1,2,5,6,13,14],[190],2⟩,⟨67,(4),[1,2,5,6],[150],2⟩,⟨67,(4),[1,2,5,6,13,14],[190],2⟩,⟨67,(5),[1,2,5,6],[150],2⟩,⟨67,(5),[1,2,5,6,13,14],[190],2⟩,⟨67,(6),[1,2,5,6],[150],2⟩,⟨67,(6),[1,2,5,6,13,14],[190],2⟩,⟨67,(7),[1,2,5,6],[150],2⟩,⟨67,(7),[1,2,5,6,13,14],[190],2⟩,⟨67,(8),[1,2,5,6],[150],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1344
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1345
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1346
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1347
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1348
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1349
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1350
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1351
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1352
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1353
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1354
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1355
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1356
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1357
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1358
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1359
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1360
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1361
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1362
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1363
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1364
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1365
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1366
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1367
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1368
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1369
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1370
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1371
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1372
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1373
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1374
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1375
end Section14Records_6_1344_1376

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1344_1376


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1376_1408
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1376_1408
private theorem valid1376 : RecordDataValid section14Catalog 6 (⟨67,(8),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1377 : RecordDataValid section14Catalog 6 (⟨67,(9),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1378 : RecordDataValid section14Catalog 6 (⟨67,(9),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1379 : RecordDataValid section14Catalog 6 (⟨67,(10),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1380 : RecordDataValid section14Catalog 6 (⟨67,(10),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1381 : RecordDataValid section14Catalog 6 (⟨67,(11),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1382 : RecordDataValid section14Catalog 6 (⟨67,(11),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1383 : RecordDataValid section14Catalog 6 (⟨67,(12),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1384 : RecordDataValid section14Catalog 6 (⟨67,(12),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1385 : RecordDataValid section14Catalog 6 (⟨67,(13),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1386 : RecordDataValid section14Catalog 6 (⟨67,(13),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1387 : RecordDataValid section14Catalog 6 (⟨67,(14),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1388 : RecordDataValid section14Catalog 6 (⟨67,(14),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1389 : RecordDataValid section14Catalog 6 (⟨67,(15),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1390 : RecordDataValid section14Catalog 6 (⟨67,(15),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1391 : RecordDataValid section14Catalog 6 (⟨67,(16),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1392 : RecordDataValid section14Catalog 6 (⟨67,(16),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1393 : RecordDataValid section14Catalog 6 (⟨67,(17),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1394 : RecordDataValid section14Catalog 6 (⟨67,(17),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1395 : RecordDataValid section14Catalog 6 (⟨67,(18),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1396 : RecordDataValid section14Catalog 6 (⟨67,(18),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1397 : RecordDataValid section14Catalog 6 (⟨67,(19),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1398 : RecordDataValid section14Catalog 6 (⟨67,(19),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1399 : RecordDataValid section14Catalog 6 (⟨67,(20),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1400 : RecordDataValid section14Catalog 6 (⟨67,(20),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1401 : RecordDataValid section14Catalog 6 (⟨67,(21),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1402 : RecordDataValid section14Catalog 6 (⟨67,(21),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1403 : RecordDataValid section14Catalog 6 (⟨67,(22),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1404 : RecordDataValid section14Catalog 6 (⟨67,(22),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1405 : RecordDataValid section14Catalog 6 (⟨67,(23),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1406 : RecordDataValid section14Catalog 6 (⟨67,(23),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1407 : RecordDataValid section14Catalog 6 (⟨67,(24),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1376_1408 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1376).take 32 = [⟨67,(8),[1,2,5,6,13,14],[190],2⟩,⟨67,(9),[1,2,5,6],[150],2⟩,⟨67,(9),[1,2,5,6,13,14],[190],2⟩,⟨67,(10),[1,2,5,6],[150],2⟩,⟨67,(10),[1,2,5,6,13,14],[190],2⟩,⟨67,(11),[1,2,5,6],[150],2⟩,⟨67,(11),[1,2,5,6,13,14],[190],2⟩,⟨67,(12),[1,2,5,6],[150],2⟩,⟨67,(12),[1,2,5,6,13,14],[190],2⟩,⟨67,(13),[1,2,5,6],[150],2⟩,⟨67,(13),[1,2,5,6,13,14],[190],2⟩,⟨67,(14),[1,2,5,6],[150],2⟩,⟨67,(14),[1,2,5,6,13,14],[190],2⟩,⟨67,(15),[1,2,5,6],[150],2⟩,⟨67,(15),[1,2,5,6,13,14],[190],2⟩,⟨67,(16),[1,2,5,6],[150],2⟩,⟨67,(16),[1,2,5,6,13,14],[190],2⟩,⟨67,(17),[1,2,5,6],[150],2⟩,⟨67,(17),[1,2,5,6,13,14],[190],2⟩,⟨67,(18),[1,2,5,6],[150],2⟩,⟨67,(18),[1,2,5,6,13,14],[190],2⟩,⟨67,(19),[1,2,5,6],[150],2⟩,⟨67,(19),[1,2,5,6,13,14],[190],2⟩,⟨67,(20),[1,2,5,6],[150],2⟩,⟨67,(20),[1,2,5,6,13,14],[190],2⟩,⟨67,(21),[1,2,5,6],[150],2⟩,⟨67,(21),[1,2,5,6,13,14],[190],2⟩,⟨67,(22),[1,2,5,6],[150],2⟩,⟨67,(22),[1,2,5,6,13,14],[190],2⟩,⟨67,(23),[1,2,5,6],[150],2⟩,⟨67,(23),[1,2,5,6,13,14],[190],2⟩,⟨67,(24),[1,2,5,6],[150],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1376
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1377
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1378
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1379
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1380
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1381
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1382
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1383
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1384
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1385
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1386
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1387
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1388
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1389
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1390
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1391
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1392
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1393
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1394
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1395
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1396
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1397
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1398
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1399
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1400
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1401
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1402
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1403
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1404
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1405
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1406
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1407
end Section14Records_6_1376_1408

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1376_1408

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1280).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 1280 1344 1408 (by decide) (by decide) (all_of_interval_split P xs 1280 1312 1344 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1280_1312 hnum) (Freiman.workReverse20260919_s0006_records_1312_1344 hnum)) (all_of_interval_split P xs 1344 1376 1408 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1344_1376 hnum) (Freiman.workReverse20260919_s0006_records_1376_1408 hnum)))

#print axioms solution
