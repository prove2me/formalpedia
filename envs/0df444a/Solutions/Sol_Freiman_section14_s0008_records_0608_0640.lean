-- Prove2me | solution 1 for Freiman.section14_s0008_records_0608_0640
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:03:19.786781+00:00
-- url     : https://prove2.me/submissions/4ce17bfb-d1bf-45b3-b199-f040e354f2f1

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
namespace Section14Records_8_608_640
private theorem valid608 : RecordDataValid section14Catalog 8 (⟨96,(6),[4,8,12,16],[10],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 8 (⟨96,(7),[4,8,12,16],[10],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 8 (⟨96,(8),[4,8,12,16],[10],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 8 (⟨96,(9),[4,8,12,16],[10],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 8 (⟨96,(10),[4,8,12,16],[10],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 8 (⟨96,(11),[4,8,12,16],[10],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 8 (⟨96,(12),[4,8,12,16],[10],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 8 (⟨96,(13),[4,8,12,16],[10],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 8 (⟨96,(14),[4,8,12,16],[10],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 8 (⟨96,(15),[4,8,12,16],[10],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 8 (⟨100,(0),[4,8,12,16],[10],424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨424,[1,4,5,6,8,9,10,12,13,16],425⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 8 (⟨100,(1),[4,8,12,16],[10],425⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨425,[1,4,5,6,8,9,10,12,13,16],426⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 8 (⟨100,(2),[4,8,12,16],[10],426⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨426,[1,4,5,6,8,9,10,12,13,16],427⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 8 (⟨100,(3),[4,8,12,16],[10],427⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨427,[1,4,5,6,8,9,10,12,13,16],428⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 8 (⟨101,(0),[4,8,12,16],[10],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 8 (⟨101,(1),[4,8,12,16],[10],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 8 (⟨101,(2),[4,8,12,16],[10],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 8 (⟨101,(3),[4,8,12,16],[10],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 8 (⟨101,(4),[4,8,12,16],[10],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 8 (⟨101,(5),[4,8,12,16],[10],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 8 (⟨101,(6),[4,8,12,16],[10],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 8 (⟨101,(7),[4,8,12,16],[10],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 8 (⟨101,(8),[4,8,12,16],[10],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 8 (⟨101,(9),[4,8,12,16],[10],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 8 (⟨101,(10),[4,8,12,16],[10],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 8 (⟨101,(11),[4,8,12,16],[10],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 8 (⟨101,(12),[4,8,12,16],[10],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 8 (⟨101,(13),[4,8,12,16],[10],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 8 (⟨101,(14),[4,8,12,16],[10],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 8 (⟨101,(15),[4,8,12,16],[10],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 8 (⟨104,(0),[4,8,12,16],[10],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 8 (⟨104,(1),[4,8,12,16],[10],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 608).take 32 = [⟨96,(6),[4,8,12,16],[10],420⟩,⟨96,(7),[4,8,12,16],[10],421⟩,⟨96,(8),[4,8,12,16],[10],418⟩,⟨96,(9),[4,8,12,16],[10],419⟩,⟨96,(10),[4,8,12,16],[10],420⟩,⟨96,(11),[4,8,12,16],[10],421⟩,⟨96,(12),[4,8,12,16],[10],423⟩,⟨96,(13),[4,8,12,16],[10],419⟩,⟨96,(14),[4,8,12,16],[10],420⟩,⟨96,(15),[4,8,12,16],[10],421⟩,⟨100,(0),[4,8,12,16],[10],424⟩,⟨100,(1),[4,8,12,16],[10],425⟩,⟨100,(2),[4,8,12,16],[10],426⟩,⟨100,(3),[4,8,12,16],[10],427⟩,⟨101,(0),[4,8,12,16],[10],428⟩,⟨101,(1),[4,8,12,16],[10],429⟩,⟨101,(2),[4,8,12,16],[10],430⟩,⟨101,(3),[4,8,12,16],[10],431⟩,⟨101,(4),[4,8,12,16],[10],432⟩,⟨101,(5),[4,8,12,16],[10],429⟩,⟨101,(6),[4,8,12,16],[10],430⟩,⟨101,(7),[4,8,12,16],[10],431⟩,⟨101,(8),[4,8,12,16],[10],428⟩,⟨101,(9),[4,8,12,16],[10],429⟩,⟨101,(10),[4,8,12,16],[10],430⟩,⟨101,(11),[4,8,12,16],[10],431⟩,⟨101,(12),[4,8,12,16],[10],433⟩,⟨101,(13),[4,8,12,16],[10],429⟩,⟨101,(14),[4,8,12,16],[10],430⟩,⟨101,(15),[4,8,12,16],[10],431⟩,⟨104,(0),[4,8,12,16],[10],434⟩,⟨104,(1),[4,8,12,16],[10],434⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid608
  · exact recordValid_of_data section14Catalog 8 _ hnum valid609
  · exact recordValid_of_data section14Catalog 8 _ hnum valid610
  · exact recordValid_of_data section14Catalog 8 _ hnum valid611
  · exact recordValid_of_data section14Catalog 8 _ hnum valid612
  · exact recordValid_of_data section14Catalog 8 _ hnum valid613
  · exact recordValid_of_data section14Catalog 8 _ hnum valid614
  · exact recordValid_of_data section14Catalog 8 _ hnum valid615
  · exact recordValid_of_data section14Catalog 8 _ hnum valid616
  · exact recordValid_of_data section14Catalog 8 _ hnum valid617
  · exact recordValid_of_data section14Catalog 8 _ hnum valid618
  · exact recordValid_of_data section14Catalog 8 _ hnum valid619
  · exact recordValid_of_data section14Catalog 8 _ hnum valid620
  · exact recordValid_of_data section14Catalog 8 _ hnum valid621
  · exact recordValid_of_data section14Catalog 8 _ hnum valid622
  · exact recordValid_of_data section14Catalog 8 _ hnum valid623
  · exact recordValid_of_data section14Catalog 8 _ hnum valid624
  · exact recordValid_of_data section14Catalog 8 _ hnum valid625
  · exact recordValid_of_data section14Catalog 8 _ hnum valid626
  · exact recordValid_of_data section14Catalog 8 _ hnum valid627
  · exact recordValid_of_data section14Catalog 8 _ hnum valid628
  · exact recordValid_of_data section14Catalog 8 _ hnum valid629
  · exact recordValid_of_data section14Catalog 8 _ hnum valid630
  · exact recordValid_of_data section14Catalog 8 _ hnum valid631
  · exact recordValid_of_data section14Catalog 8 _ hnum valid632
  · exact recordValid_of_data section14Catalog 8 _ hnum valid633
  · exact recordValid_of_data section14Catalog 8 _ hnum valid634
  · exact recordValid_of_data section14Catalog 8 _ hnum valid635
  · exact recordValid_of_data section14Catalog 8 _ hnum valid636
  · exact recordValid_of_data section14Catalog 8 _ hnum valid637
  · exact recordValid_of_data section14Catalog 8 _ hnum valid638
  · exact recordValid_of_data section14Catalog 8 _ hnum valid639
end Section14Records_8_608_640

#print axioms solution
