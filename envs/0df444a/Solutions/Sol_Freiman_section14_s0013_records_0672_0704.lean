-- Prove2me | solution 1 for Freiman.section14_s0013_records_0672_0704
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T11:56:31.312699+00:00
-- url     : https://prove2.me/submissions/d0418cfa-5a07-4df5-9752-92416142bae5

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
namespace Section14Records_13_672_704
private theorem valid672 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid673 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid674 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid675 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid676 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid677 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid678 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid679 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid680 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid681 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid682 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid683 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid684 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid685 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid686 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid687 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid688 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid689 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid690 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid691 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid692 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid693 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid694 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid695 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid696 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid697 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,13,14],[190],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid698 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,13],[135],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid699 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,13],[151],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid700 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid701 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid702 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid703 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,13,14],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 672).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 672).take 32 = [⟨25,(17),[1,2,5,6,13,14],[146],150⟩,⟨25,(17),[1,2,13,14],[131],35⟩,⟨25,(17),[1,2,13,14],[147],172⟩,⟨25,(17),[1,2,13,14],[150],197⟩,⟨25,(17),[1,2,13,14],[190],221⟩,⟨25,(17),[1,13],[135],35⟩,⟨25,(17),[1,13],[151],172⟩,⟨25,(18),[1,2,5,6,13,14],[146],150⟩,⟨25,(18),[1,2,13,14],[131],35⟩,⟨25,(18),[1,2,13,14],[147],172⟩,⟨25,(18),[1,2,13,14],[150],197⟩,⟨25,(18),[1,2,13,14],[190],221⟩,⟨25,(18),[1,13],[135],35⟩,⟨25,(18),[1,13],[151],172⟩,⟨25,(19),[1,2,5,6,13,14],[146],150⟩,⟨25,(19),[1,2,13,14],[131],35⟩,⟨25,(19),[1,2,13,14],[147],172⟩,⟨25,(19),[1,2,13,14],[150],197⟩,⟨25,(19),[1,2,13,14],[190],221⟩,⟨25,(19),[1,13],[135],35⟩,⟨25,(19),[1,13],[151],172⟩,⟨25,(20),[1,2,5,6,13,14],[146],151⟩,⟨25,(20),[1,2,5,6,13,14],[150],198⟩,⟨25,(20),[1,2,13,14],[131],38⟩,⟨25,(20),[1,2,13,14],[147],173⟩,⟨25,(20),[1,2,13,14],[190],198⟩,⟨25,(20),[1,13],[135],38⟩,⟨25,(20),[1,13],[151],173⟩,⟨25,(21),[1,2,5,6,13,14],[146],151⟩,⟨25,(21),[1,2,13,14],[131],38⟩,⟨25,(21),[1,2,13,14],[147],173⟩,⟨25,(21),[1,2,13,14],[150],199⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid672
  · exact recordValid_of_data section14Catalog 13 _ hnum valid673
  · exact recordValid_of_data section14Catalog 13 _ hnum valid674
  · exact recordValid_of_data section14Catalog 13 _ hnum valid675
  · exact recordValid_of_data section14Catalog 13 _ hnum valid676
  · exact recordValid_of_data section14Catalog 13 _ hnum valid677
  · exact recordValid_of_data section14Catalog 13 _ hnum valid678
  · exact recordValid_of_data section14Catalog 13 _ hnum valid679
  · exact recordValid_of_data section14Catalog 13 _ hnum valid680
  · exact recordValid_of_data section14Catalog 13 _ hnum valid681
  · exact recordValid_of_data section14Catalog 13 _ hnum valid682
  · exact recordValid_of_data section14Catalog 13 _ hnum valid683
  · exact recordValid_of_data section14Catalog 13 _ hnum valid684
  · exact recordValid_of_data section14Catalog 13 _ hnum valid685
  · exact recordValid_of_data section14Catalog 13 _ hnum valid686
  · exact recordValid_of_data section14Catalog 13 _ hnum valid687
  · exact recordValid_of_data section14Catalog 13 _ hnum valid688
  · exact recordValid_of_data section14Catalog 13 _ hnum valid689
  · exact recordValid_of_data section14Catalog 13 _ hnum valid690
  · exact recordValid_of_data section14Catalog 13 _ hnum valid691
  · exact recordValid_of_data section14Catalog 13 _ hnum valid692
  · exact recordValid_of_data section14Catalog 13 _ hnum valid693
  · exact recordValid_of_data section14Catalog 13 _ hnum valid694
  · exact recordValid_of_data section14Catalog 13 _ hnum valid695
  · exact recordValid_of_data section14Catalog 13 _ hnum valid696
  · exact recordValid_of_data section14Catalog 13 _ hnum valid697
  · exact recordValid_of_data section14Catalog 13 _ hnum valid698
  · exact recordValid_of_data section14Catalog 13 _ hnum valid699
  · exact recordValid_of_data section14Catalog 13 _ hnum valid700
  · exact recordValid_of_data section14Catalog 13 _ hnum valid701
  · exact recordValid_of_data section14Catalog 13 _ hnum valid702
  · exact recordValid_of_data section14Catalog 13 _ hnum valid703
end Section14Records_13_672_704

#print axioms solution
