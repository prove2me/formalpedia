-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2656_2688
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:22:44.952563+00:00
-- url     : https://prove2.me/submissions/1358500c-b893-4f8f-ba22-56ebb93f5676

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
namespace Section14Records_13_2656_2688
private theorem valid2656 : RecordDataValid section14Catalog 13 (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2657 : RecordDataValid section14Catalog 13 (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2658 : RecordDataValid section14Catalog 13 (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨853,[1,2,3,5,6,7,10,11,13,14,15],854⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2659 : RecordDataValid section14Catalog 13 (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2660 : RecordDataValid section14Catalog 13 (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2661 : RecordDataValid section14Catalog 13 (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2662 : RecordDataValid section14Catalog 13 (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2663 : RecordDataValid section14Catalog 13 (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨855,[1,2,3,5,6,7,10,11,13,14,15],856⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2664 : RecordDataValid section14Catalog 13 (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2665 : RecordDataValid section14Catalog 13 (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2666 : RecordDataValid section14Catalog 13 (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2667 : RecordDataValid section14Catalog 13 (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2668 : RecordDataValid section14Catalog 13 (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨860,[1,2,3,5,6,7,10,11,13,14,15],861⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2669 : RecordDataValid section14Catalog 13 (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2670 : RecordDataValid section14Catalog 13 (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2671 : RecordDataValid section14Catalog 13 (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2672 : RecordDataValid section14Catalog 13 (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2673 : RecordDataValid section14Catalog 13 (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2674 : RecordDataValid section14Catalog 13 (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2675 : RecordDataValid section14Catalog 13 (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2676 : RecordDataValid section14Catalog 13 (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2677 : RecordDataValid section14Catalog 13 (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2678 : RecordDataValid section14Catalog 13 (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2679 : RecordDataValid section14Catalog 13 (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2680 : RecordDataValid section14Catalog 13 (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2681 : RecordDataValid section14Catalog 13 (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2682 : RecordDataValid section14Catalog 13 (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2683 : RecordDataValid section14Catalog 13 (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2684 : RecordDataValid section14Catalog 13 (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2685 : RecordDataValid section14Catalog 13 (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2686 : RecordDataValid section14Catalog 13 (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2687 : RecordDataValid section14Catalog 13 (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2656).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2656).take 32 = [⟨232,(7),[1,2,5,6,13,14],[170],851⟩,⟨232,(8),[1,2,5,6,13,14],[170],852⟩,⟨232,(9),[1,2,5,6,13,14],[170],853⟩,⟨232,(10),[1,2,5,6,13,14],[170],844⟩,⟨232,(11),[1,2,5,6,13,14],[170],854⟩,⟨232,(12),[1,2,5,6,13,14],[170],846⟩,⟨232,(13),[1,2,5,6,13,14],[170],847⟩,⟨232,(14),[1,2,5,6,13,14],[170],855⟩,⟨232,(15),[1,2,5,6,13,14],[170],856⟩,⟨232,(16),[1,2,5,6,13,14],[170],857⟩,⟨232,(17),[1,2,5,6,13,14],[170],858⟩,⟨232,(18),[1,2,5,6,13,14],[170],859⟩,⟨232,(19),[1,2,5,6,13,14],[170],860⟩,⟨234,(0),[1,2,5,6,13,14],[170],568⟩,⟨234,(1),[1,2,5,6,13,14],[170],569⟩,⟨234,(2),[1,2,5,6,13,14],[170],570⟩,⟨234,(3),[1,2,5,6,13,14],[170],571⟩,⟨234,(4),[1,2,5,6,13,14],[170],572⟩,⟨234,(5),[1,2,5,6,13,14],[170],573⟩,⟨234,(6),[1,2,5,6,13,14],[170],573⟩,⟨234,(7),[1,2,5,6,13,14],[170],573⟩,⟨234,(8),[1,2,5,6,13,14],[170],574⟩,⟨234,(9),[1,2,5,6,13,14],[170],575⟩,⟨234,(10),[1,2,5,6,13,14],[170],575⟩,⟨234,(11),[1,2,5,6,13,14],[170],575⟩,⟨234,(12),[1,2,5,6,13,14],[170],576⟩,⟨234,(13),[1,2,5,6,13,14],[170],577⟩,⟨234,(14),[1,2,5,6,13,14],[170],577⟩,⟨234,(15),[1,2,5,6,13,14],[170],577⟩,⟨235,(0),[1,2,5,6,13,14],[170],578⟩,⟨235,(1),[1,2,5,6,13,14],[170],579⟩,⟨235,(2),[1,2,5,6,13,14],[170],580⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2656
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2657
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2658
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2659
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2660
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2661
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2662
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2663
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2664
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2665
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2666
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2667
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2668
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2669
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2670
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2671
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2672
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2673
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2674
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2675
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2676
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2677
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2678
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2679
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2680
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2681
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2682
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2683
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2684
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2685
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2686
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2687
end Section14Records_13_2656_2688

#print axioms solution
