-- Prove2me | solution 1 for Freiman.section14_s0007_records_0032_0064
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:13:03.659529+00:00
-- url     : https://prove2.me/submissions/fe2652d8-f3ad-4ba4-921c-f254ca335e9b

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
namespace Section14Records_7_32_64
private theorem valid32 : RecordDataValid section14Catalog 7 (⟨5,(23),[3,4,7,8,15,16],[10],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid33 : RecordDataValid section14Catalog 7 (⟨5,(24),[3,4,7,8,15,16],[10],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid34 : RecordDataValid section14Catalog 7 (⟨11,(0),[3,4,7,8],[10],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid35 : RecordDataValid section14Catalog 7 (⟨11,(1),[3,4,7,8],[10],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid36 : RecordDataValid section14Catalog 7 (⟨11,(2),[3,4,7,8],[10],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid37 : RecordDataValid section14Catalog 7 (⟨11,(3),[3,4,7,8],[10],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid38 : RecordDataValid section14Catalog 7 (⟨11,(4),[3,4,7,8],[10],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid39 : RecordDataValid section14Catalog 7 (⟨11,(5),[3,4,7,8],[10],45⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨45,[1,2,3,4,5,6,7,8],45⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid40 : RecordDataValid section14Catalog 7 (⟨11,(6),[3,4,7,8],[10],45⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨45,[1,2,3,4,5,6,7,8],45⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid41 : RecordDataValid section14Catalog 7 (⟨11,(7),[3,4,7,8],[10],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid42 : RecordDataValid section14Catalog 7 (⟨11,(8),[3,4,7,8],[10],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid43 : RecordDataValid section14Catalog 7 (⟨11,(9),[3,4,7,8],[10],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid44 : RecordDataValid section14Catalog 7 (⟨11,(10),[3,4,7,8],[10],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid45 : RecordDataValid section14Catalog 7 (⟨11,(11),[3,4,7,8],[10],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid46 : RecordDataValid section14Catalog 7 (⟨11,(12),[3,4,7,8],[10],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid47 : RecordDataValid section14Catalog 7 (⟨11,(13),[3,4,7,8],[10],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid48 : RecordDataValid section14Catalog 7 (⟨11,(14),[3,4,7,8],[10],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid49 : RecordDataValid section14Catalog 7 (⟨11,(15),[3,4,7,8],[10],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid50 : RecordDataValid section14Catalog 7 (⟨11,(16),[3,4,7,8],[10],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid51 : RecordDataValid section14Catalog 7 (⟨11,(17),[3,4,7,8],[10],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid52 : RecordDataValid section14Catalog 7 (⟨11,(18),[3,4,7,8],[10],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid53 : RecordDataValid section14Catalog 7 (⟨11,(19),[3,4,7,8],[10],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid54 : RecordDataValid section14Catalog 7 (⟨11,(20),[3,4,7,8],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid55 : RecordDataValid section14Catalog 7 (⟨11,(21),[3,4,7,8],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid56 : RecordDataValid section14Catalog 7 (⟨11,(22),[3,4,7,8],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid57 : RecordDataValid section14Catalog 7 (⟨11,(23),[3,4,7,8],[10],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid58 : RecordDataValid section14Catalog 7 (⟨11,(24),[3,4,7,8],[10],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid59 : RecordDataValid section14Catalog 7 (⟨14,(5),[7,15],[10],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid60 : RecordDataValid section14Catalog 7 (⟨14,(7),[3,7,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid61 : RecordDataValid section14Catalog 7 (⟨14,(8),[7],[10],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid62 : RecordDataValid section14Catalog 7 (⟨14,(9),[7,15],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid63 : RecordDataValid section14Catalog 7 (⟨14,(15),[7],[10],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 32).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 32).take 32 = [⟨5,(23),[3,4,7,8,15,16],[10],26⟩,⟨5,(24),[3,4,7,8,15,16],[10],26⟩,⟨11,(0),[3,4,7,8],[10],41⟩,⟨11,(1),[3,4,7,8],[10],41⟩,⟨11,(2),[3,4,7,8],[10],42⟩,⟨11,(3),[3,4,7,8],[10],43⟩,⟨11,(4),[3,4,7,8],[10],44⟩,⟨11,(5),[3,4,7,8],[10],45⟩,⟨11,(6),[3,4,7,8],[10],45⟩,⟨11,(7),[3,4,7,8],[10],42⟩,⟨11,(8),[3,4,7,8],[10],43⟩,⟨11,(9),[3,4,7,8],[10],44⟩,⟨11,(10),[3,4,7,8],[10],41⟩,⟨11,(11),[3,4,7,8],[10],41⟩,⟨11,(12),[3,4,7,8],[10],42⟩,⟨11,(13),[3,4,7,8],[10],43⟩,⟨11,(14),[3,4,7,8],[10],44⟩,⟨11,(15),[3,4,7,8],[10],46⟩,⟨11,(16),[3,4,7,8],[10],46⟩,⟨11,(17),[3,4,7,8],[10],42⟩,⟨11,(18),[3,4,7,8],[10],43⟩,⟨11,(19),[3,4,7,8],[10],44⟩,⟨11,(20),[3,4,7,8],[10],47⟩,⟨11,(21),[3,4,7,8],[10],47⟩,⟨11,(22),[3,4,7,8],[10],47⟩,⟨11,(23),[3,4,7,8],[10],43⟩,⟨11,(24),[3,4,7,8],[10],44⟩,⟨14,(5),[7,15],[10],105⟩,⟨14,(7),[3,7,15],[10],3⟩,⟨14,(8),[7],[10],48⟩,⟨14,(9),[7,15],[10],143⟩,⟨14,(15),[7],[10],48⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid32
  · exact recordValid_of_data section14Catalog 7 _ hnum valid33
  · exact recordValid_of_data section14Catalog 7 _ hnum valid34
  · exact recordValid_of_data section14Catalog 7 _ hnum valid35
  · exact recordValid_of_data section14Catalog 7 _ hnum valid36
  · exact recordValid_of_data section14Catalog 7 _ hnum valid37
  · exact recordValid_of_data section14Catalog 7 _ hnum valid38
  · exact recordValid_of_data section14Catalog 7 _ hnum valid39
  · exact recordValid_of_data section14Catalog 7 _ hnum valid40
  · exact recordValid_of_data section14Catalog 7 _ hnum valid41
  · exact recordValid_of_data section14Catalog 7 _ hnum valid42
  · exact recordValid_of_data section14Catalog 7 _ hnum valid43
  · exact recordValid_of_data section14Catalog 7 _ hnum valid44
  · exact recordValid_of_data section14Catalog 7 _ hnum valid45
  · exact recordValid_of_data section14Catalog 7 _ hnum valid46
  · exact recordValid_of_data section14Catalog 7 _ hnum valid47
  · exact recordValid_of_data section14Catalog 7 _ hnum valid48
  · exact recordValid_of_data section14Catalog 7 _ hnum valid49
  · exact recordValid_of_data section14Catalog 7 _ hnum valid50
  · exact recordValid_of_data section14Catalog 7 _ hnum valid51
  · exact recordValid_of_data section14Catalog 7 _ hnum valid52
  · exact recordValid_of_data section14Catalog 7 _ hnum valid53
  · exact recordValid_of_data section14Catalog 7 _ hnum valid54
  · exact recordValid_of_data section14Catalog 7 _ hnum valid55
  · exact recordValid_of_data section14Catalog 7 _ hnum valid56
  · exact recordValid_of_data section14Catalog 7 _ hnum valid57
  · exact recordValid_of_data section14Catalog 7 _ hnum valid58
  · exact recordValid_of_data section14Catalog 7 _ hnum valid59
  · exact recordValid_of_data section14Catalog 7 _ hnum valid60
  · exact recordValid_of_data section14Catalog 7 _ hnum valid61
  · exact recordValid_of_data section14Catalog 7 _ hnum valid62
  · exact recordValid_of_data section14Catalog 7 _ hnum valid63
end Section14Records_7_32_64

#print axioms solution
