-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3264_3296
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:56:28.737355+00:00
-- url     : https://prove2.me/submissions/0424d940-cae2-4f69-8d38-afd6cc0e24a9

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
namespace Section14Records_5_3264_3296
private theorem valid3264 : RecordDataValid section14Catalog 5 (⟨205,(16),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3265 : RecordDataValid section14Catalog 5 (⟨205,(16),[5,6],[174],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3266 : RecordDataValid section14Catalog 5 (⟨205,(17),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3267 : RecordDataValid section14Catalog 5 (⟨205,(17),[5,6],[174],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3268 : RecordDataValid section14Catalog 5 (⟨205,(18),[1,2,5,6,13,14],[170],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3269 : RecordDataValid section14Catalog 5 (⟨205,(18),[5,6],[174],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3270 : RecordDataValid section14Catalog 5 (⟨205,(19),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3271 : RecordDataValid section14Catalog 5 (⟨205,(19),[5,6],[174],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3272 : RecordDataValid section14Catalog 5 (⟨205,(20),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3273 : RecordDataValid section14Catalog 5 (⟨205,(20),[5,6],[174],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3274 : RecordDataValid section14Catalog 5 (⟨205,(21),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3275 : RecordDataValid section14Catalog 5 (⟨205,(21),[5,6],[174],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3276 : RecordDataValid section14Catalog 5 (⟨205,(22),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3277 : RecordDataValid section14Catalog 5 (⟨205,(22),[5,6],[174],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3278 : RecordDataValid section14Catalog 5 (⟨205,(23),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3279 : RecordDataValid section14Catalog 5 (⟨205,(23),[5,6],[174],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3280 : RecordDataValid section14Catalog 5 (⟨205,(24),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3281 : RecordDataValid section14Catalog 5 (⟨205,(24),[5,6],[174],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3282 : RecordDataValid section14Catalog 5 (⟨207,(0),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3283 : RecordDataValid section14Catalog 5 (⟨207,(0),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3284 : RecordDataValid section14Catalog 5 (⟨207,(1),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3285 : RecordDataValid section14Catalog 5 (⟨207,(1),[5,6],[174],1023⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1023,[3,5,6,7],1027⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3286 : RecordDataValid section14Catalog 5 (⟨207,(2),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3287 : RecordDataValid section14Catalog 5 (⟨207,(2),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3288 : RecordDataValid section14Catalog 5 (⟨207,(3),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3289 : RecordDataValid section14Catalog 5 (⟨207,(3),[5,6],[174],1024⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1024,[3,5,6,7],1028⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3290 : RecordDataValid section14Catalog 5 (⟨207,(4),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3291 : RecordDataValid section14Catalog 5 (⟨207,(4),[5,6],[174],1025⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1025,[3,5,6,7],1029⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3292 : RecordDataValid section14Catalog 5 (⟨207,(5),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3293 : RecordDataValid section14Catalog 5 (⟨207,(5),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3294 : RecordDataValid section14Catalog 5 (⟨207,(6),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3295 : RecordDataValid section14Catalog 5 (⟨207,(6),[5,6],[174],1023⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1023,[3,5,6,7],1027⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3264).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3264).take 32 = [⟨205,(16),[1,2,5,6,13,14],[170],720⟩,⟨205,(16),[5,6],[174],720⟩,⟨205,(17),[1,2,5,6,13,14],[170],720⟩,⟨205,(17),[5,6],[174],720⟩,⟨205,(18),[1,2,5,6,13,14],[170],721⟩,⟨205,(18),[5,6],[174],721⟩,⟨205,(19),[1,2,5,6,13,14],[170],720⟩,⟨205,(19),[5,6],[174],720⟩,⟨205,(20),[1,2,5,6,13,14],[170],715⟩,⟨205,(20),[5,6],[174],715⟩,⟨205,(21),[1,2,5,6,13,14],[170],716⟩,⟨205,(21),[5,6],[174],716⟩,⟨205,(22),[1,2,5,6,13,14],[170],717⟩,⟨205,(22),[5,6],[174],717⟩,⟨205,(23),[1,2,5,6,13,14],[170],718⟩,⟨205,(23),[5,6],[174],718⟩,⟨205,(24),[1,2,5,6,13,14],[170],719⟩,⟨205,(24),[5,6],[174],719⟩,⟨207,(0),[1,2,5,6,13,14],[170],481⟩,⟨207,(0),[5,6],[174],1022⟩,⟨207,(1),[1,2,5,6,13,14],[170],482⟩,⟨207,(1),[5,6],[174],1023⟩,⟨207,(2),[1,2,5,6,13,14],[170],481⟩,⟨207,(2),[5,6],[174],1022⟩,⟨207,(3),[1,2,5,6,13,14],[170],483⟩,⟨207,(3),[5,6],[174],1024⟩,⟨207,(4),[1,2,5,6,13,14],[170],484⟩,⟨207,(4),[5,6],[174],1025⟩,⟨207,(5),[1,2,5,6,13,14],[170],481⟩,⟨207,(5),[5,6],[174],1022⟩,⟨207,(6),[1,2,5,6,13,14],[170],482⟩,⟨207,(6),[5,6],[174],1023⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3264
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3265
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3266
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3267
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3268
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3269
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3270
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3271
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3272
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3273
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3274
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3275
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3276
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3277
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3278
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3279
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3280
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3281
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3282
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3283
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3284
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3285
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3286
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3287
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3288
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3289
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3290
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3291
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3292
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3293
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3294
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3295
end Section14Records_5_3264_3296

#print axioms solution
