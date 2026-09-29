-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2208_2240
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:21:05.375574+00:00
-- url     : https://prove2.me/submissions/c660b953-215a-4e97-be6f-2af40621df5f

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
namespace Section14Records_13_2208_2240
private theorem valid2208 : RecordDataValid section14Catalog 13 (⟨190,(1),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2209 : RecordDataValid section14Catalog 13 (⟨190,(2),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2210 : RecordDataValid section14Catalog 13 (⟨190,(3),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2211 : RecordDataValid section14Catalog 13 (⟨190,(4),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2212 : RecordDataValid section14Catalog 13 (⟨190,(5),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2213 : RecordDataValid section14Catalog 13 (⟨190,(6),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2214 : RecordDataValid section14Catalog 13 (⟨190,(7),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2215 : RecordDataValid section14Catalog 13 (⟨190,(8),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2216 : RecordDataValid section14Catalog 13 (⟨190,(9),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2217 : RecordDataValid section14Catalog 13 (⟨190,(10),[1,2,5,6,13,14],[170],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2218 : RecordDataValid section14Catalog 13 (⟨190,(11),[1,2,5,6,13,14],[170],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2219 : RecordDataValid section14Catalog 13 (⟨190,(12),[1,2,5,6,13,14],[170],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2220 : RecordDataValid section14Catalog 13 (⟨190,(13),[1,2,5,6,13,14],[170],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2221 : RecordDataValid section14Catalog 13 (⟨190,(14),[1,2,5,6,13,14],[170],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2222 : RecordDataValid section14Catalog 13 (⟨190,(15),[1,2,5,6,13,14],[170],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2223 : RecordDataValid section14Catalog 13 (⟨190,(16),[1,2,5,6,13,14],[170],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2224 : RecordDataValid section14Catalog 13 (⟨190,(17),[1,2,5,6,13,14],[170],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2225 : RecordDataValid section14Catalog 13 (⟨190,(18),[1,2,5,6,13,14],[170],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2226 : RecordDataValid section14Catalog 13 (⟨190,(19),[1,2,5,6,13,14],[170],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2227 : RecordDataValid section14Catalog 13 (⟨190,(20),[1,2,5,6,13,14],[170],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2228 : RecordDataValid section14Catalog 13 (⟨190,(21),[1,2,5,6,13,14],[170],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2229 : RecordDataValid section14Catalog 13 (⟨190,(22),[1,2,5,6,13,14],[170],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2230 : RecordDataValid section14Catalog 13 (⟨190,(23),[1,2,5,6,13,14],[170],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2231 : RecordDataValid section14Catalog 13 (⟨190,(24),[1,2,5,6,13,14],[170],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2232 : RecordDataValid section14Catalog 13 (⟨192,(0),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2233 : RecordDataValid section14Catalog 13 (⟨192,(1),[1,2,5,6,13,14],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2234 : RecordDataValid section14Catalog 13 (⟨192,(2),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2235 : RecordDataValid section14Catalog 13 (⟨192,(3),[1,2,5,6,13,14],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2236 : RecordDataValid section14Catalog 13 (⟨192,(4),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2237 : RecordDataValid section14Catalog 13 (⟨192,(5),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2238 : RecordDataValid section14Catalog 13 (⟨192,(6),[1,2,5,6,13,14],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2239 : RecordDataValid section14Catalog 13 (⟨192,(7),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2208).take 32 = [⟨190,(1),[1,2,5,6,13,14],[170],690⟩,⟨190,(2),[1,2,5,6,13,14],[170],690⟩,⟨190,(3),[1,2,5,6,13,14],[170],690⟩,⟨190,(4),[1,2,5,6,13,14],[170],690⟩,⟨190,(5),[1,2,5,6,13,14],[170],691⟩,⟨190,(6),[1,2,5,6,13,14],[170],691⟩,⟨190,(7),[1,2,5,6,13,14],[170],691⟩,⟨190,(8),[1,2,5,6,13,14],[170],691⟩,⟨190,(9),[1,2,5,6,13,14],[170],691⟩,⟨190,(10),[1,2,5,6,13,14],[170],692⟩,⟨190,(11),[1,2,5,6,13,14],[170],693⟩,⟨190,(12),[1,2,5,6,13,14],[170],694⟩,⟨190,(13),[1,2,5,6,13,14],[170],693⟩,⟨190,(14),[1,2,5,6,13,14],[170],695⟩,⟨190,(15),[1,2,5,6,13,14],[170],692⟩,⟨190,(16),[1,2,5,6,13,14],[170],696⟩,⟨190,(17),[1,2,5,6,13,14],[170],696⟩,⟨190,(18),[1,2,5,6,13,14],[170],696⟩,⟨190,(19),[1,2,5,6,13,14],[170],696⟩,⟨190,(20),[1,2,5,6,13,14],[170],692⟩,⟨190,(21),[1,2,5,6,13,14],[170],693⟩,⟨190,(22),[1,2,5,6,13,14],[170],694⟩,⟨190,(23),[1,2,5,6,13,14],[170],693⟩,⟨190,(24),[1,2,5,6,13,14],[170],695⟩,⟨192,(0),[1,2,5,6,13,14],[170],441⟩,⟨192,(1),[1,2,5,6,13,14],[170],442⟩,⟨192,(2),[1,2,5,6,13,14],[170],441⟩,⟨192,(3),[1,2,5,6,13,14],[170],443⟩,⟨192,(4),[1,2,5,6,13,14],[170],444⟩,⟨192,(5),[1,2,5,6,13,14],[170],441⟩,⟨192,(6),[1,2,5,6,13,14],[170],442⟩,⟨192,(7),[1,2,5,6,13,14],[170],441⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2208
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2209
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2210
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2211
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2212
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2213
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2214
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2215
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2216
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2217
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2218
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2219
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2220
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2221
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2222
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2223
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2224
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2225
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2226
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2227
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2228
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2229
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2230
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2231
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2232
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2233
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2234
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2235
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2236
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2237
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2238
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2239
end Section14Records_13_2208_2240

#print axioms solution
