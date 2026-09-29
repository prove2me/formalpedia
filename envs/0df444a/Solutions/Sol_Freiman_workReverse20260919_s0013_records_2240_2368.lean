-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2240_2368
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:58:32.063571+00:00
-- url     : https://prove2.me/submissions/c47a549b-b968-4e11-9e1d-e17b837dcc02

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2240_2272
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2240_2272
private theorem valid2240 : RecordDataValid section14Catalog 13 (⟨192,(8),[1,2,5,6,13,14],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2241 : RecordDataValid section14Catalog 13 (⟨192,(9),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2242 : RecordDataValid section14Catalog 13 (⟨192,(10),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2243 : RecordDataValid section14Catalog 13 (⟨192,(11),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2244 : RecordDataValid section14Catalog 13 (⟨192,(12),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2245 : RecordDataValid section14Catalog 13 (⟨192,(13),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2246 : RecordDataValid section14Catalog 13 (⟨192,(14),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2247 : RecordDataValid section14Catalog 13 (⟨192,(15),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2248 : RecordDataValid section14Catalog 13 (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2249 : RecordDataValid section14Catalog 13 (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2250 : RecordDataValid section14Catalog 13 (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2251 : RecordDataValid section14Catalog 13 (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2252 : RecordDataValid section14Catalog 13 (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2253 : RecordDataValid section14Catalog 13 (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2254 : RecordDataValid section14Catalog 13 (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2255 : RecordDataValid section14Catalog 13 (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2256 : RecordDataValid section14Catalog 13 (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2257 : RecordDataValid section14Catalog 13 (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2258 : RecordDataValid section14Catalog 13 (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2259 : RecordDataValid section14Catalog 13 (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2260 : RecordDataValid section14Catalog 13 (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2261 : RecordDataValid section14Catalog 13 (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2262 : RecordDataValid section14Catalog 13 (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2263 : RecordDataValid section14Catalog 13 (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2264 : RecordDataValid section14Catalog 13 (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2265 : RecordDataValid section14Catalog 13 (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2266 : RecordDataValid section14Catalog 13 (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2267 : RecordDataValid section14Catalog 13 (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2268 : RecordDataValid section14Catalog 13 (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2269 : RecordDataValid section14Catalog 13 (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2270 : RecordDataValid section14Catalog 13 (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2271 : RecordDataValid section14Catalog 13 (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2240_2272 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2240).take 32 = [⟨192,(8),[1,2,5,6,13,14],[170],443⟩,⟨192,(9),[1,2,5,6,13,14],[170],444⟩,⟨192,(10),[1,2,5,6,13,14],[170],445⟩,⟨192,(11),[1,2,5,6,13,14],[170],445⟩,⟨192,(12),[1,2,5,6,13,14],[170],445⟩,⟨192,(13),[1,2,5,6,13,14],[170],445⟩,⟨192,(14),[1,2,5,6,13,14],[170],444⟩,⟨192,(15),[1,2,5,6,13,14],[170],446⟩,⟨192,(16),[1,2,5,6,13,14],[170],446⟩,⟨192,(17),[1,2,5,6,13,14],[170],446⟩,⟨192,(18),[1,2,5,6,13,14],[170],446⟩,⟨192,(19),[1,2,5,6,13,14],[170],446⟩,⟨192,(20),[1,2,5,6,13,14],[170],447⟩,⟨192,(21),[1,2,5,6,13,14],[170],447⟩,⟨192,(22),[1,2,5,6,13,14],[170],447⟩,⟨192,(23),[1,2,5,6,13,14],[170],447⟩,⟨192,(24),[1,2,5,6,13,14],[170],447⟩,⟨195,(0),[1,2,5,6,13,14],[170],697⟩,⟨195,(1),[1,2,5,6,13,14],[170],697⟩,⟨195,(2),[1,2,5,6,13,14],[170],698⟩,⟨195,(3),[1,2,5,6,13,14],[170],698⟩,⟨195,(4),[1,2,5,6,13,14],[170],699⟩,⟨195,(5),[1,2,5,6,13,14],[170],700⟩,⟨195,(6),[1,2,5,6,13,14],[170],699⟩,⟨195,(7),[1,2,5,6,13,14],[170],701⟩,⟨195,(8),[1,2,5,6,13,14],[170],702⟩,⟨195,(9),[1,2,5,6,13,14],[170],703⟩,⟨197,(0),[1,2,5,6,13,14],[170],453⟩,⟨197,(1),[1,2,5,6,13,14],[170],454⟩,⟨197,(2),[1,2,5,6,13,14],[170],453⟩,⟨197,(3),[1,2,5,6,13,14],[170],455⟩,⟨197,(4),[1,2,5,6,13,14],[170],456⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2240
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2241
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2242
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2243
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2244
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2245
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2246
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2247
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2248
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2249
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2250
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2251
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2252
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2253
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2254
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2255
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2256
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2257
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2258
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2259
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2260
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2261
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2262
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2263
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2264
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2265
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2266
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2267
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2268
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2269
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2270
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2271
end Section14Records_13_2240_2272

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2240_2272


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2272_2304
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2272_2304
private theorem valid2272 : RecordDataValid section14Catalog 13 (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2273 : RecordDataValid section14Catalog 13 (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2274 : RecordDataValid section14Catalog 13 (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2275 : RecordDataValid section14Catalog 13 (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2276 : RecordDataValid section14Catalog 13 (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2277 : RecordDataValid section14Catalog 13 (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2278 : RecordDataValid section14Catalog 13 (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2279 : RecordDataValid section14Catalog 13 (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2280 : RecordDataValid section14Catalog 13 (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2281 : RecordDataValid section14Catalog 13 (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2282 : RecordDataValid section14Catalog 13 (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2283 : RecordDataValid section14Catalog 13 (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2284 : RecordDataValid section14Catalog 13 (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2285 : RecordDataValid section14Catalog 13 (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2286 : RecordDataValid section14Catalog 13 (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2287 : RecordDataValid section14Catalog 13 (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2288 : RecordDataValid section14Catalog 13 (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2289 : RecordDataValid section14Catalog 13 (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2290 : RecordDataValid section14Catalog 13 (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2291 : RecordDataValid section14Catalog 13 (⟨197,(24),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2292 : RecordDataValid section14Catalog 13 (⟨200,(0),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2293 : RecordDataValid section14Catalog 13 (⟨200,(1),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2294 : RecordDataValid section14Catalog 13 (⟨200,(2),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2295 : RecordDataValid section14Catalog 13 (⟨200,(3),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2296 : RecordDataValid section14Catalog 13 (⟨200,(4),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2297 : RecordDataValid section14Catalog 13 (⟨200,(5),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2298 : RecordDataValid section14Catalog 13 (⟨200,(6),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2299 : RecordDataValid section14Catalog 13 (⟨200,(7),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2300 : RecordDataValid section14Catalog 13 (⟨200,(8),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2301 : RecordDataValid section14Catalog 13 (⟨200,(9),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2302 : RecordDataValid section14Catalog 13 (⟨200,(10),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2303 : RecordDataValid section14Catalog 13 (⟨200,(11),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2272_2304 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2272).take 32 = [⟨197,(5),[1,2,5,6,13,14],[170],453⟩,⟨197,(6),[1,2,5,6,13,14],[170],454⟩,⟨197,(7),[1,2,5,6,13,14],[170],453⟩,⟨197,(8),[1,2,5,6,13,14],[170],455⟩,⟨197,(9),[1,2,5,6,13,14],[170],456⟩,⟨197,(10),[1,2,5,6,13,14],[170],457⟩,⟨197,(11),[1,2,5,6,13,14],[170],457⟩,⟨197,(12),[1,2,5,6,13,14],[170],457⟩,⟨197,(13),[1,2,5,6,13,14],[170],457⟩,⟨197,(14),[1,2,5,6,13,14],[170],456⟩,⟨197,(15),[1,2,5,6,13,14],[170],458⟩,⟨197,(16),[1,2,5,6,13,14],[170],458⟩,⟨197,(17),[1,2,5,6,13,14],[170],458⟩,⟨197,(18),[1,2,5,6,13,14],[170],458⟩,⟨197,(19),[1,2,5,6,13,14],[170],458⟩,⟨197,(20),[1,2,5,6,13,14],[170],459⟩,⟨197,(21),[1,2,5,6,13,14],[170],459⟩,⟨197,(22),[1,2,5,6,13,14],[170],459⟩,⟨197,(23),[1,2,5,6,13,14],[170],459⟩,⟨197,(24),[1,2,5,6,13,14],[170],459⟩,⟨200,(0),[1,2,5,6,13,14],[170],704⟩,⟨200,(1),[1,2,5,6,13,14],[170],704⟩,⟨200,(2),[1,2,5,6,13,14],[170],704⟩,⟨200,(3),[1,2,5,6,13,14],[170],704⟩,⟨200,(4),[1,2,5,6,13,14],[170],704⟩,⟨200,(5),[1,2,5,6,13,14],[170],705⟩,⟨200,(6),[1,2,5,6,13,14],[170],705⟩,⟨200,(7),[1,2,5,6,13,14],[170],705⟩,⟨200,(8),[1,2,5,6,13,14],[170],705⟩,⟨200,(9),[1,2,5,6,13,14],[170],705⟩,⟨200,(10),[1,2,5,6,13,14],[170],706⟩,⟨200,(11),[1,2,5,6,13,14],[170],707⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2272
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2273
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2274
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2275
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2276
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2277
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2278
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2279
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2280
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2281
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2282
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2283
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2284
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2285
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2286
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2287
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2288
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2289
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2290
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2291
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2292
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2293
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2294
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2295
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2296
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2297
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2298
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2299
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2300
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2301
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2302
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2303
end Section14Records_13_2272_2304

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2272_2304


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2304_2336
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2304_2336
private theorem valid2304 : RecordDataValid section14Catalog 13 (⟨200,(12),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2305 : RecordDataValid section14Catalog 13 (⟨200,(13),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2306 : RecordDataValid section14Catalog 13 (⟨200,(14),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2307 : RecordDataValid section14Catalog 13 (⟨200,(15),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2308 : RecordDataValid section14Catalog 13 (⟨200,(16),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2309 : RecordDataValid section14Catalog 13 (⟨200,(17),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2310 : RecordDataValid section14Catalog 13 (⟨200,(18),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2311 : RecordDataValid section14Catalog 13 (⟨200,(19),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2312 : RecordDataValid section14Catalog 13 (⟨200,(20),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2313 : RecordDataValid section14Catalog 13 (⟨200,(21),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2314 : RecordDataValid section14Catalog 13 (⟨200,(22),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2315 : RecordDataValid section14Catalog 13 (⟨200,(23),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2316 : RecordDataValid section14Catalog 13 (⟨200,(24),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2317 : RecordDataValid section14Catalog 13 (⟨202,(0),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2318 : RecordDataValid section14Catalog 13 (⟨202,(1),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2319 : RecordDataValid section14Catalog 13 (⟨202,(2),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2320 : RecordDataValid section14Catalog 13 (⟨202,(3),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2321 : RecordDataValid section14Catalog 13 (⟨202,(4),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2322 : RecordDataValid section14Catalog 13 (⟨202,(5),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2323 : RecordDataValid section14Catalog 13 (⟨202,(6),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2324 : RecordDataValid section14Catalog 13 (⟨202,(7),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2325 : RecordDataValid section14Catalog 13 (⟨202,(8),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2326 : RecordDataValid section14Catalog 13 (⟨202,(9),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2327 : RecordDataValid section14Catalog 13 (⟨202,(10),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2328 : RecordDataValid section14Catalog 13 (⟨202,(11),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2329 : RecordDataValid section14Catalog 13 (⟨202,(12),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2330 : RecordDataValid section14Catalog 13 (⟨202,(13),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2331 : RecordDataValid section14Catalog 13 (⟨202,(14),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2332 : RecordDataValid section14Catalog 13 (⟨202,(15),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2333 : RecordDataValid section14Catalog 13 (⟨202,(16),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2334 : RecordDataValid section14Catalog 13 (⟨202,(17),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2335 : RecordDataValid section14Catalog 13 (⟨202,(18),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2304_2336 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2304).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2304).take 32 = [⟨200,(12),[1,2,5,6,13,14],[170],708⟩,⟨200,(13),[1,2,5,6,13,14],[170],707⟩,⟨200,(14),[1,2,5,6,13,14],[170],709⟩,⟨200,(15),[1,2,5,6,13,14],[170],706⟩,⟨200,(16),[1,2,5,6,13,14],[170],710⟩,⟨200,(17),[1,2,5,6,13,14],[170],710⟩,⟨200,(18),[1,2,5,6,13,14],[170],710⟩,⟨200,(19),[1,2,5,6,13,14],[170],710⟩,⟨200,(20),[1,2,5,6,13,14],[170],706⟩,⟨200,(21),[1,2,5,6,13,14],[170],707⟩,⟨200,(22),[1,2,5,6,13,14],[170],708⟩,⟨200,(23),[1,2,5,6,13,14],[170],707⟩,⟨200,(24),[1,2,5,6,13,14],[170],709⟩,⟨202,(0),[1,2,5,6,13,14],[170],467⟩,⟨202,(1),[1,2,5,6,13,14],[170],468⟩,⟨202,(2),[1,2,5,6,13,14],[170],467⟩,⟨202,(3),[1,2,5,6,13,14],[170],469⟩,⟨202,(4),[1,2,5,6,13,14],[170],470⟩,⟨202,(5),[1,2,5,6,13,14],[170],467⟩,⟨202,(6),[1,2,5,6,13,14],[170],468⟩,⟨202,(7),[1,2,5,6,13,14],[170],467⟩,⟨202,(8),[1,2,5,6,13,14],[170],469⟩,⟨202,(9),[1,2,5,6,13,14],[170],470⟩,⟨202,(10),[1,2,5,6,13,14],[170],471⟩,⟨202,(11),[1,2,5,6,13,14],[170],471⟩,⟨202,(12),[1,2,5,6,13,14],[170],471⟩,⟨202,(13),[1,2,5,6,13,14],[170],471⟩,⟨202,(14),[1,2,5,6,13,14],[170],470⟩,⟨202,(15),[1,2,5,6,13,14],[170],472⟩,⟨202,(16),[1,2,5,6,13,14],[170],472⟩,⟨202,(17),[1,2,5,6,13,14],[170],472⟩,⟨202,(18),[1,2,5,6,13,14],[170],472⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2304
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2305
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2306
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2307
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2308
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2309
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2310
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2311
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2312
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2313
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2314
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2315
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2316
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2317
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2318
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2319
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2320
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2321
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2322
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2323
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2324
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2325
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2326
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2327
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2328
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2329
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2330
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2331
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2332
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2333
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2334
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2335
end Section14Records_13_2304_2336

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2304_2336


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2336_2368
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2336_2368
private theorem valid2336 : RecordDataValid section14Catalog 13 (⟨202,(19),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2337 : RecordDataValid section14Catalog 13 (⟨202,(20),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2338 : RecordDataValid section14Catalog 13 (⟨202,(21),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2339 : RecordDataValid section14Catalog 13 (⟨202,(22),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2340 : RecordDataValid section14Catalog 13 (⟨202,(23),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2341 : RecordDataValid section14Catalog 13 (⟨202,(24),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2342 : RecordDataValid section14Catalog 13 (⟨205,(0),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2343 : RecordDataValid section14Catalog 13 (⟨205,(1),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2344 : RecordDataValid section14Catalog 13 (⟨205,(2),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2345 : RecordDataValid section14Catalog 13 (⟨205,(3),[1,2,5,6,13,14],[170],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2346 : RecordDataValid section14Catalog 13 (⟨205,(4),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2347 : RecordDataValid section14Catalog 13 (⟨205,(5),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2348 : RecordDataValid section14Catalog 13 (⟨205,(6),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2349 : RecordDataValid section14Catalog 13 (⟨205,(7),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2350 : RecordDataValid section14Catalog 13 (⟨205,(8),[1,2,5,6,13,14],[170],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2351 : RecordDataValid section14Catalog 13 (⟨205,(9),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2352 : RecordDataValid section14Catalog 13 (⟨205,(10),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2353 : RecordDataValid section14Catalog 13 (⟨205,(11),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2354 : RecordDataValid section14Catalog 13 (⟨205,(12),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2355 : RecordDataValid section14Catalog 13 (⟨205,(13),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2356 : RecordDataValid section14Catalog 13 (⟨205,(14),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2357 : RecordDataValid section14Catalog 13 (⟨205,(15),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2358 : RecordDataValid section14Catalog 13 (⟨205,(16),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2359 : RecordDataValid section14Catalog 13 (⟨205,(17),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2360 : RecordDataValid section14Catalog 13 (⟨205,(18),[1,2,5,6,13,14],[170],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2361 : RecordDataValid section14Catalog 13 (⟨205,(19),[1,2,5,6,13,14],[170],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2362 : RecordDataValid section14Catalog 13 (⟨205,(20),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2363 : RecordDataValid section14Catalog 13 (⟨205,(21),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2364 : RecordDataValid section14Catalog 13 (⟨205,(22),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2365 : RecordDataValid section14Catalog 13 (⟨205,(23),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2366 : RecordDataValid section14Catalog 13 (⟨205,(24),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2367 : RecordDataValid section14Catalog 13 (⟨207,(0),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2336_2368 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2336).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2336).take 32 = [⟨202,(19),[1,2,5,6,13,14],[170],472⟩,⟨202,(20),[1,2,5,6,13,14],[170],473⟩,⟨202,(21),[1,2,5,6,13,14],[170],473⟩,⟨202,(22),[1,2,5,6,13,14],[170],473⟩,⟨202,(23),[1,2,5,6,13,14],[170],473⟩,⟨202,(24),[1,2,5,6,13,14],[170],473⟩,⟨205,(0),[1,2,5,6,13,14],[170],711⟩,⟨205,(1),[1,2,5,6,13,14],[170],711⟩,⟨205,(2),[1,2,5,6,13,14],[170],711⟩,⟨205,(3),[1,2,5,6,13,14],[170],712⟩,⟨205,(4),[1,2,5,6,13,14],[170],711⟩,⟨205,(5),[1,2,5,6,13,14],[170],713⟩,⟨205,(6),[1,2,5,6,13,14],[170],713⟩,⟨205,(7),[1,2,5,6,13,14],[170],713⟩,⟨205,(8),[1,2,5,6,13,14],[170],714⟩,⟨205,(9),[1,2,5,6,13,14],[170],713⟩,⟨205,(10),[1,2,5,6,13,14],[170],715⟩,⟨205,(11),[1,2,5,6,13,14],[170],716⟩,⟨205,(12),[1,2,5,6,13,14],[170],717⟩,⟨205,(13),[1,2,5,6,13,14],[170],718⟩,⟨205,(14),[1,2,5,6,13,14],[170],719⟩,⟨205,(15),[1,2,5,6,13,14],[170],715⟩,⟨205,(16),[1,2,5,6,13,14],[170],720⟩,⟨205,(17),[1,2,5,6,13,14],[170],720⟩,⟨205,(18),[1,2,5,6,13,14],[170],721⟩,⟨205,(19),[1,2,5,6,13,14],[170],720⟩,⟨205,(20),[1,2,5,6,13,14],[170],715⟩,⟨205,(21),[1,2,5,6,13,14],[170],716⟩,⟨205,(22),[1,2,5,6,13,14],[170],717⟩,⟨205,(23),[1,2,5,6,13,14],[170],718⟩,⟨205,(24),[1,2,5,6,13,14],[170],719⟩,⟨207,(0),[1,2,5,6,13,14],[170],481⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2336
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2337
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2338
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2339
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2340
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2341
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2342
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2343
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2344
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2345
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2346
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2347
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2348
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2349
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2350
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2351
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2352
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2353
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2354
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2355
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2356
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2357
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2358
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2359
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2360
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2361
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2362
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2363
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2364
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2365
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2366
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2367
end Section14Records_13_2336_2368

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2336_2368

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2240).take 128, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 2240 2304 2368 (by decide) (by decide) (all_of_interval_split P xs 2240 2272 2304 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2240_2272 hnum) (Freiman.workReverse20260919_s0013_records_2272_2304 hnum)) (all_of_interval_split P xs 2304 2336 2368 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2304_2336 hnum) (Freiman.workReverse20260919_s0013_records_2336_2368 hnum)))

#print axioms solution
