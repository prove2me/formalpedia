-- Prove2me | solution 1 for Freiman.section14_s0013_records_1312_1344
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T12:17:44.574264+00:00
-- url     : https://prove2.me/submissions/6d552c26-bc1f-42e6-a840-59f8e1eb2f81

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
namespace Section14Records_13_1312_1344
private theorem valid1312 : RecordDataValid section14Catalog 13 (⟨67,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1313 : RecordDataValid section14Catalog 13 (⟨67,(8),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1314 : RecordDataValid section14Catalog 13 (⟨67,(9),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1315 : RecordDataValid section14Catalog 13 (⟨67,(10),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1316 : RecordDataValid section14Catalog 13 (⟨67,(11),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1317 : RecordDataValid section14Catalog 13 (⟨67,(12),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1318 : RecordDataValid section14Catalog 13 (⟨67,(13),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1319 : RecordDataValid section14Catalog 13 (⟨67,(14),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1320 : RecordDataValid section14Catalog 13 (⟨67,(15),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1321 : RecordDataValid section14Catalog 13 (⟨67,(16),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1322 : RecordDataValid section14Catalog 13 (⟨67,(17),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1323 : RecordDataValid section14Catalog 13 (⟨67,(18),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1324 : RecordDataValid section14Catalog 13 (⟨67,(19),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1325 : RecordDataValid section14Catalog 13 (⟨67,(20),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1326 : RecordDataValid section14Catalog 13 (⟨67,(21),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1327 : RecordDataValid section14Catalog 13 (⟨67,(22),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1328 : RecordDataValid section14Catalog 13 (⟨67,(23),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1329 : RecordDataValid section14Catalog 13 (⟨67,(24),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1330 : RecordDataValid section14Catalog 13 (⟨69,(0),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1331 : RecordDataValid section14Catalog 13 (⟨69,(1),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1332 : RecordDataValid section14Catalog 13 (⟨69,(2),[1,5,6,13],[190],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1333 : RecordDataValid section14Catalog 13 (⟨69,(3),[1,5,6,13],[190],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1334 : RecordDataValid section14Catalog 13 (⟨69,(4),[1,5,6,13],[190],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1335 : RecordDataValid section14Catalog 13 (⟨69,(5),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1336 : RecordDataValid section14Catalog 13 (⟨69,(6),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1337 : RecordDataValid section14Catalog 13 (⟨69,(7),[1,2,5,6,13,14],[190],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1338 : RecordDataValid section14Catalog 13 (⟨69,(8),[1,2,5,6,13,14],[190],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1339 : RecordDataValid section14Catalog 13 (⟨69,(9),[1,2,5,6,13,14],[190],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1340 : RecordDataValid section14Catalog 13 (⟨69,(10),[1,2,5,6,13,14],[190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1341 : RecordDataValid section14Catalog 13 (⟨69,(11),[1,2,5,6,13,14],[190],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1342 : RecordDataValid section14Catalog 13 (⟨69,(12),[1,2,5,6,13,14],[190],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1343 : RecordDataValid section14Catalog 13 (⟨69,(13),[1,2,5,6,13,14],[190],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1312).take 32 = [⟨67,(7),[1,2,5,6,13,14],[190],2⟩,⟨67,(8),[1,2,5,6,13,14],[190],2⟩,⟨67,(9),[1,2,5,6,13,14],[190],2⟩,⟨67,(10),[1,2,5,6,13,14],[190],2⟩,⟨67,(11),[1,2,5,6,13,14],[190],2⟩,⟨67,(12),[1,2,5,6,13,14],[190],2⟩,⟨67,(13),[1,2,5,6,13,14],[190],2⟩,⟨67,(14),[1,2,5,6,13,14],[190],2⟩,⟨67,(15),[1,2,5,6,13,14],[190],2⟩,⟨67,(16),[1,2,5,6,13,14],[190],2⟩,⟨67,(17),[1,2,5,6,13,14],[190],2⟩,⟨67,(18),[1,2,5,6,13,14],[190],2⟩,⟨67,(19),[1,2,5,6,13,14],[190],2⟩,⟨67,(20),[1,2,5,6,13,14],[190],2⟩,⟨67,(21),[1,2,5,6,13,14],[190],2⟩,⟨67,(22),[1,2,5,6,13,14],[190],2⟩,⟨67,(23),[1,2,5,6,13,14],[190],2⟩,⟨67,(24),[1,2,5,6,13,14],[190],2⟩,⟨69,(0),[1,2,5,6,13,14],[190],189⟩,⟨69,(1),[1,2,5,6,13,14],[190],260⟩,⟨69,(2),[1,5,6,13],[190],375⟩,⟨69,(3),[1,5,6,13],[190],376⟩,⟨69,(4),[1,5,6,13],[190],377⟩,⟨69,(5),[1,2,5,6,13,14],[190],189⟩,⟨69,(6),[1,2,5,6,13,14],[190],260⟩,⟨69,(7),[1,2,5,6,13,14],[190],375⟩,⟨69,(8),[1,2,5,6,13,14],[190],376⟩,⟨69,(9),[1,2,5,6,13,14],[190],377⟩,⟨69,(10),[1,2,5,6,13,14],[190],194⟩,⟨69,(11),[1,2,5,6,13,14],[190],267⟩,⟨69,(12),[1,2,5,6,13,14],[190],378⟩,⟨69,(13),[1,2,5,6,13,14],[190],378⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1312
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1313
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1314
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1315
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1316
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1317
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1318
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1319
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1320
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1321
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1322
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1323
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1324
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1325
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1326
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1327
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1328
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1329
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1330
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1331
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1332
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1333
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1334
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1335
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1336
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1337
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1338
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1339
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1340
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1341
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1342
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1343
end Section14Records_13_1312_1344

#print axioms solution
