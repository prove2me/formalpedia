-- Prove2me | solution 1 for Freiman.section14_s0012_records_0432_0448
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:31:02.783999+00:00
-- url     : https://prove2.me/submissions/c31fdd15-894d-4fe5-8288-d4c7ca402cee

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
namespace Section14Records_12_432_448
private theorem valid432 : RecordDataValid section14Catalog 12 (⟨79,(11),[4,8,12],[6,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid433 : RecordDataValid section14Catalog 12 (⟨79,(12),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid434 : RecordDataValid section14Catalog 12 (⟨79,(13),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid435 : RecordDataValid section14Catalog 12 (⟨79,(14),[4,8,12],[6,14],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid436 : RecordDataValid section14Catalog 12 (⟨79,(15),[4,8,12],[6,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid437 : RecordDataValid section14Catalog 12 (⟨79,(16),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid438 : RecordDataValid section14Catalog 12 (⟨79,(17),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid439 : RecordDataValid section14Catalog 12 (⟨79,(18),[4,8,12],[14],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid440 : RecordDataValid section14Catalog 12 (⟨79,(18),[8,12],[6],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid441 : RecordDataValid section14Catalog 12 (⟨79,(19),[4,8,12],[6,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid442 : RecordDataValid section14Catalog 12 (⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid443 : RecordDataValid section14Catalog 12 (⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid444 : RecordDataValid section14Catalog 12 (⟨82,(-1),[4,8,10,12,16],[8,12],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid445 : RecordDataValid section14Catalog 12 (⟨82,(-1),[4,8,11,12,16],[1],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid446 : RecordDataValid section14Catalog 12 (⟨82,(-1),[4,8,12,16],[9,13],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid447 : RecordDataValid section14Catalog 12 (⟨82,(-1),[4,8,12,16],[2],389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 432).take 16, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 432).take 16 = [⟨79,(11),[4,8,12],[6,14],101⟩,⟨79,(12),[4,8,12],[6,14],2⟩,⟨79,(13),[4,8,12],[6,14],2⟩,⟨79,(14),[4,8,12],[6,14],286⟩,⟨79,(15),[4,8,12],[6,14],101⟩,⟨79,(16),[4,8,12],[6,14],2⟩,⟨79,(17),[4,8,12],[6,14],2⟩,⟨79,(18),[4,8,12],[14],287⟩,⟨79,(18),[8,12],[6],287⟩,⟨79,(19),[4,8,12],[6,14],101⟩,⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩,⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩,⟨82,(-1),[4,8,10,12,16],[8,12],387⟩,⟨82,(-1),[4,8,11,12,16],[1],388⟩,⟨82,(-1),[4,8,12,16],[9,13],388⟩,⟨82,(-1),[4,8,12,16],[2],389⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid432
  · exact recordValid_of_data section14Catalog 12 _ hnum valid433
  · exact recordValid_of_data section14Catalog 12 _ hnum valid434
  · exact recordValid_of_data section14Catalog 12 _ hnum valid435
  · exact recordValid_of_data section14Catalog 12 _ hnum valid436
  · exact recordValid_of_data section14Catalog 12 _ hnum valid437
  · exact recordValid_of_data section14Catalog 12 _ hnum valid438
  · exact recordValid_of_data section14Catalog 12 _ hnum valid439
  · exact recordValid_of_data section14Catalog 12 _ hnum valid440
  · exact recordValid_of_data section14Catalog 12 _ hnum valid441
  · exact recordValid_of_data section14Catalog 12 _ hnum valid442
  · exact recordValid_of_data section14Catalog 12 _ hnum valid443
  · exact recordValid_of_data section14Catalog 12 _ hnum valid444
  · exact recordValid_of_data section14Catalog 12 _ hnum valid445
  · exact recordValid_of_data section14Catalog 12 _ hnum valid446
  · exact recordValid_of_data section14Catalog 12 _ hnum valid447
end Section14Records_12_432_448

#print axioms solution
