-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3200_3264
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:28:35.448113+00:00
-- url     : https://prove2.me/submissions/3209b59a-c6f0-488e-ab0c-a62fb7db221f

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3200_3232
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3200_3232
private theorem valid3200 : RecordDataValid section14Catalog 6 (⟨221,(7),[5,6],[174],1037⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1037,[3,5,6,7],1041⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3201 : RecordDataValid section14Catalog 6 (⟨221,(8),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3202 : RecordDataValid section14Catalog 6 (⟨221,(8),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3203 : RecordDataValid section14Catalog 6 (⟨221,(9),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3204 : RecordDataValid section14Catalog 6 (⟨221,(9),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3205 : RecordDataValid section14Catalog 6 (⟨221,(10),[1,2,5,6,13,14],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3206 : RecordDataValid section14Catalog 6 (⟨221,(10),[5,6],[174],1040⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1040,[3,5,6,7],1044⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3207 : RecordDataValid section14Catalog 6 (⟨221,(11),[1,2,5,6,13,14],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3208 : RecordDataValid section14Catalog 6 (⟨221,(11),[5,6],[174],1040⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1040,[3,5,6,7],1044⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3209 : RecordDataValid section14Catalog 6 (⟨221,(12),[1,2,5,6,13,14],[170],520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨520,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3210 : RecordDataValid section14Catalog 6 (⟨221,(12),[5,6],[174],1041⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1041,[3,5,6,7],1045⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3211 : RecordDataValid section14Catalog 6 (⟨221,(13),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3212 : RecordDataValid section14Catalog 6 (⟨221,(13),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3213 : RecordDataValid section14Catalog 6 (⟨221,(14),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3214 : RecordDataValid section14Catalog 6 (⟨221,(14),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3215 : RecordDataValid section14Catalog 6 (⟨221,(15),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3216 : RecordDataValid section14Catalog 6 (⟨221,(15),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3217 : RecordDataValid section14Catalog 6 (⟨221,(16),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3218 : RecordDataValid section14Catalog 6 (⟨221,(16),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3219 : RecordDataValid section14Catalog 6 (⟨221,(17),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3220 : RecordDataValid section14Catalog 6 (⟨221,(17),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3221 : RecordDataValid section14Catalog 6 (⟨221,(18),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3222 : RecordDataValid section14Catalog 6 (⟨221,(18),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3223 : RecordDataValid section14Catalog 6 (⟨221,(19),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3224 : RecordDataValid section14Catalog 6 (⟨221,(19),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3225 : RecordDataValid section14Catalog 6 (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3226 : RecordDataValid section14Catalog 6 (⟨221,(20),[5,6],[174],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3227 : RecordDataValid section14Catalog 6 (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3228 : RecordDataValid section14Catalog 6 (⟨221,(21),[5,6],[174],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3229 : RecordDataValid section14Catalog 6 (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3230 : RecordDataValid section14Catalog 6 (⟨221,(22),[5,6],[174],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3231 : RecordDataValid section14Catalog 6 (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3200_3232 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3200).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3200).take 32 = [⟨221,(7),[5,6],[174],1037⟩,⟨221,(8),[1,2,5,6,13,14],[170],517⟩,⟨221,(8),[5,6],[174],1038⟩,⟨221,(9),[1,2,5,6,13,14],[170],518⟩,⟨221,(9),[5,6],[174],1039⟩,⟨221,(10),[1,2,5,6,13,14],[170],519⟩,⟨221,(10),[5,6],[174],1040⟩,⟨221,(11),[1,2,5,6,13,14],[170],519⟩,⟨221,(11),[5,6],[174],1040⟩,⟨221,(12),[1,2,5,6,13,14],[170],520⟩,⟨221,(12),[5,6],[174],1041⟩,⟨221,(13),[1,2,5,6,13,14],[170],517⟩,⟨221,(13),[5,6],[174],1038⟩,⟨221,(14),[1,2,5,6,13,14],[170],518⟩,⟨221,(14),[5,6],[174],1039⟩,⟨221,(15),[1,2,5,6,13,14],[170],521⟩,⟨221,(15),[5,6],[174],1042⟩,⟨221,(16),[1,2,5,6,13,14],[170],521⟩,⟨221,(16),[5,6],[174],1042⟩,⟨221,(17),[1,2,5,6,13,14],[170],521⟩,⟨221,(17),[5,6],[174],1042⟩,⟨221,(18),[1,2,5,6,13,14],[170],517⟩,⟨221,(18),[5,6],[174],1038⟩,⟨221,(19),[1,2,5,6,13,14],[170],521⟩,⟨221,(19),[5,6],[174],1042⟩,⟨221,(20),[1,2,5,6,13,14],[170],522⟩,⟨221,(20),[5,6],[174],1043⟩,⟨221,(21),[1,2,5,6,13,14],[170],522⟩,⟨221,(21),[5,6],[174],1043⟩,⟨221,(22),[1,2,5,6,13,14],[170],522⟩,⟨221,(22),[5,6],[174],1043⟩,⟨221,(23),[1,2,5,6,13,14],[170],517⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3200
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3201
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3202
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3203
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3204
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3205
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3206
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3207
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3208
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3209
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3210
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3211
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3212
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3213
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3214
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3215
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3216
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3217
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3218
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3219
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3220
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3221
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3222
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3223
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3224
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3225
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3226
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3227
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3228
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3229
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3230
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3231
end Section14Records_6_3200_3232

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3200_3232


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3232_3264
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3232_3264
private theorem valid3232 : RecordDataValid section14Catalog 6 (⟨221,(23),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3233 : RecordDataValid section14Catalog 6 (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3234 : RecordDataValid section14Catalog 6 (⟨221,(24),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3235 : RecordDataValid section14Catalog 6 (⟨222,(0),[1,2,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3236 : RecordDataValid section14Catalog 6 (⟨222,(0),[6],[174],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3237 : RecordDataValid section14Catalog 6 (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3238 : RecordDataValid section14Catalog 6 (⟨222,(1),[5,6],[174],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3239 : RecordDataValid section14Catalog 6 (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3240 : RecordDataValid section14Catalog 6 (⟨222,(2),[5,6],[174],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3241 : RecordDataValid section14Catalog 6 (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3242 : RecordDataValid section14Catalog 6 (⟨222,(3),[5,6],[174],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3243 : RecordDataValid section14Catalog 6 (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3244 : RecordDataValid section14Catalog 6 (⟨222,(4),[5,6],[174],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3245 : RecordDataValid section14Catalog 6 (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3246 : RecordDataValid section14Catalog 6 (⟨222,(5),[5,6],[174],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3247 : RecordDataValid section14Catalog 6 (⟨222,(6),[1,2,6,13,14],[170],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3248 : RecordDataValid section14Catalog 6 (⟨222,(6),[6],[174],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3249 : RecordDataValid section14Catalog 6 (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3250 : RecordDataValid section14Catalog 6 (⟨222,(7),[5,6],[174],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3251 : RecordDataValid section14Catalog 6 (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3252 : RecordDataValid section14Catalog 6 (⟨222,(8),[5,6],[174],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3253 : RecordDataValid section14Catalog 6 (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3254 : RecordDataValid section14Catalog 6 (⟨222,(9),[5,6],[174],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3255 : RecordDataValid section14Catalog 6 (⟨222,(10),[1,2,6,13,14],[170],741⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨741,[1,2,3,6,7,10,11,13,14,15],742⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3256 : RecordDataValid section14Catalog 6 (⟨222,(10),[6],[174],741⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨741,[1,2,3,6,7,10,11,13,14,15],742⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3257 : RecordDataValid section14Catalog 6 (⟨222,(11),[1,2,6,13,14],[170],742⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨742,[1,2,3,6,7,10,11,13,14,15],743⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3258 : RecordDataValid section14Catalog 6 (⟨222,(11),[6],[174],742⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨742,[1,2,3,6,7,10,11,13,14,15],743⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3259 : RecordDataValid section14Catalog 6 (⟨222,(12),[1,2,6,13,14],[170],743⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨743,[1,2,3,6,7,11,13,14,15],744⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3260 : RecordDataValid section14Catalog 6 (⟨222,(12),[6],[174],743⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨743,[1,2,3,6,7,11,13,14,15],744⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3261 : RecordDataValid section14Catalog 6 (⟨222,(13),[1,2,6,13,14],[170],744⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨744,[1,2,3,6,7,10,11,13,14,15],745⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3262 : RecordDataValid section14Catalog 6 (⟨222,(13),[6],[174],744⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨744,[1,2,3,6,7,10,11,13,14,15],745⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3263 : RecordDataValid section14Catalog 6 (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3232_3264 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3232).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3232).take 32 = [⟨221,(23),[5,6],[174],1038⟩,⟨221,(24),[1,2,5,6,13,14],[170],518⟩,⟨221,(24),[5,6],[174],1039⟩,⟨222,(0),[1,2,6,13,14],[170],735⟩,⟨222,(0),[6],[174],735⟩,⟨222,(1),[1,2,5,6,13,14],[170],736⟩,⟨222,(1),[5,6],[174],736⟩,⟨222,(2),[1,2,5,6,13,14],[170],737⟩,⟨222,(2),[5,6],[174],737⟩,⟨222,(3),[1,2,5,6,13,14],[170],736⟩,⟨222,(3),[5,6],[174],736⟩,⟨222,(4),[1,2,5,6,13,14],[170],525⟩,⟨222,(4),[5,6],[174],525⟩,⟨222,(5),[1,2,5,6,13,14],[170],735⟩,⟨222,(5),[5,6],[174],735⟩,⟨222,(6),[1,2,6,13,14],[170],738⟩,⟨222,(6),[6],[174],738⟩,⟨222,(7),[1,2,5,6,13,14],[170],739⟩,⟨222,(7),[5,6],[174],739⟩,⟨222,(8),[1,2,5,6,13,14],[170],740⟩,⟨222,(8),[5,6],[174],740⟩,⟨222,(9),[1,2,5,6,13,14],[170],528⟩,⟨222,(9),[5,6],[174],528⟩,⟨222,(10),[1,2,6,13,14],[170],741⟩,⟨222,(10),[6],[174],741⟩,⟨222,(11),[1,2,6,13,14],[170],742⟩,⟨222,(11),[6],[174],742⟩,⟨222,(12),[1,2,6,13,14],[170],743⟩,⟨222,(12),[6],[174],743⟩,⟨222,(13),[1,2,6,13,14],[170],744⟩,⟨222,(13),[6],[174],744⟩,⟨222,(14),[1,2,5,6,13,14],[170],531⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3232
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3233
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3234
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3235
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3236
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3237
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3238
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3239
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3240
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3241
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3242
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3243
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3244
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3245
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3246
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3247
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3248
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3249
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3250
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3251
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3252
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3253
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3254
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3255
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3256
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3257
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3258
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3259
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3260
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3261
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3262
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3263
end Section14Records_6_3232_3264

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3232_3264

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3200).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3200 3232 3264 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3200_3232 hnum) (Freiman.workReverse20260919_s0006_records_3232_3264 hnum))

#print axioms solution
