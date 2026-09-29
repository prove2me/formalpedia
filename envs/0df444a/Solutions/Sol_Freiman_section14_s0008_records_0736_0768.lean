-- Prove2me | solution 1 for Freiman.section14_s0008_records_0736_0768
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:06:35.219274+00:00
-- url     : https://prove2.me/submissions/8bea7e82-3bc9-411f-8876-75529b0eb6fc

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
namespace Section14Records_8_736_768
private theorem valid736 : RecordDataValid section14Catalog 8 (⟨114,(13),[4,8,12,16],[10],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid737 : RecordDataValid section14Catalog 8 (⟨114,(14),[4,8,12,16],[10],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid738 : RecordDataValid section14Catalog 8 (⟨114,(15),[4,8,12,16],[10],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid739 : RecordDataValid section14Catalog 8 (⟨114,(16),[4,8,12,16],[10],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid740 : RecordDataValid section14Catalog 8 (⟨114,(17),[4,8,12,16],[10],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid741 : RecordDataValid section14Catalog 8 (⟨114,(18),[4,8,12,16],[10],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid742 : RecordDataValid section14Catalog 8 (⟨114,(19),[4,8,12,16],[10],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid743 : RecordDataValid section14Catalog 8 (⟨114,(20),[4,8,12,16],[10],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid744 : RecordDataValid section14Catalog 8 (⟨114,(21),[4,8,12,16],[10],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid745 : RecordDataValid section14Catalog 8 (⟨114,(22),[4,8,12,16],[10],464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid746 : RecordDataValid section14Catalog 8 (⟨114,(23),[4,8,12,16],[10],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid747 : RecordDataValid section14Catalog 8 (⟨114,(24),[4,8,12,16],[10],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid748 : RecordDataValid section14Catalog 8 (⟨116,(0),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid749 : RecordDataValid section14Catalog 8 (⟨116,(1),[4,8,12,16],[10],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid750 : RecordDataValid section14Catalog 8 (⟨116,(2),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid751 : RecordDataValid section14Catalog 8 (⟨116,(3),[4,8,12,16],[10],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid752 : RecordDataValid section14Catalog 8 (⟨116,(4),[4,8,12,16],[10],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid753 : RecordDataValid section14Catalog 8 (⟨116,(5),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid754 : RecordDataValid section14Catalog 8 (⟨116,(6),[4,8,12,16],[10],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid755 : RecordDataValid section14Catalog 8 (⟨116,(7),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid756 : RecordDataValid section14Catalog 8 (⟨116,(8),[4,8,12,16],[10],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid757 : RecordDataValid section14Catalog 8 (⟨116,(9),[4,8,12,16],[10],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid758 : RecordDataValid section14Catalog 8 (⟨116,(10),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid759 : RecordDataValid section14Catalog 8 (⟨116,(11),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid760 : RecordDataValid section14Catalog 8 (⟨116,(12),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid761 : RecordDataValid section14Catalog 8 (⟨116,(13),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid762 : RecordDataValid section14Catalog 8 (⟨116,(14),[4,8,12,16],[10],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid763 : RecordDataValid section14Catalog 8 (⟨116,(15),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid764 : RecordDataValid section14Catalog 8 (⟨116,(16),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid765 : RecordDataValid section14Catalog 8 (⟨116,(17),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid766 : RecordDataValid section14Catalog 8 (⟨116,(18),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid767 : RecordDataValid section14Catalog 8 (⟨116,(19),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 736).take 32 = [⟨114,(13),[4,8,12,16],[10],463⟩,⟨114,(14),[4,8,12,16],[10],465⟩,⟨114,(15),[4,8,12,16],[10],462⟩,⟨114,(16),[4,8,12,16],[10],466⟩,⟨114,(17),[4,8,12,16],[10],466⟩,⟨114,(18),[4,8,12,16],[10],466⟩,⟨114,(19),[4,8,12,16],[10],466⟩,⟨114,(20),[4,8,12,16],[10],462⟩,⟨114,(21),[4,8,12,16],[10],463⟩,⟨114,(22),[4,8,12,16],[10],464⟩,⟨114,(23),[4,8,12,16],[10],463⟩,⟨114,(24),[4,8,12,16],[10],465⟩,⟨116,(0),[4,8,12,16],[10],467⟩,⟨116,(1),[4,8,12,16],[10],468⟩,⟨116,(2),[4,8,12,16],[10],467⟩,⟨116,(3),[4,8,12,16],[10],469⟩,⟨116,(4),[4,8,12,16],[10],470⟩,⟨116,(5),[4,8,12,16],[10],467⟩,⟨116,(6),[4,8,12,16],[10],468⟩,⟨116,(7),[4,8,12,16],[10],467⟩,⟨116,(8),[4,8,12,16],[10],469⟩,⟨116,(9),[4,8,12,16],[10],470⟩,⟨116,(10),[4,8,12,16],[10],471⟩,⟨116,(11),[4,8,12,16],[10],471⟩,⟨116,(12),[4,8,12,16],[10],471⟩,⟨116,(13),[4,8,12,16],[10],471⟩,⟨116,(14),[4,8,12,16],[10],470⟩,⟨116,(15),[4,8,12,16],[10],472⟩,⟨116,(16),[4,8,12,16],[10],472⟩,⟨116,(17),[4,8,12,16],[10],472⟩,⟨116,(18),[4,8,12,16],[10],472⟩,⟨116,(19),[4,8,12,16],[10],472⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid736
  · exact recordValid_of_data section14Catalog 8 _ hnum valid737
  · exact recordValid_of_data section14Catalog 8 _ hnum valid738
  · exact recordValid_of_data section14Catalog 8 _ hnum valid739
  · exact recordValid_of_data section14Catalog 8 _ hnum valid740
  · exact recordValid_of_data section14Catalog 8 _ hnum valid741
  · exact recordValid_of_data section14Catalog 8 _ hnum valid742
  · exact recordValid_of_data section14Catalog 8 _ hnum valid743
  · exact recordValid_of_data section14Catalog 8 _ hnum valid744
  · exact recordValid_of_data section14Catalog 8 _ hnum valid745
  · exact recordValid_of_data section14Catalog 8 _ hnum valid746
  · exact recordValid_of_data section14Catalog 8 _ hnum valid747
  · exact recordValid_of_data section14Catalog 8 _ hnum valid748
  · exact recordValid_of_data section14Catalog 8 _ hnum valid749
  · exact recordValid_of_data section14Catalog 8 _ hnum valid750
  · exact recordValid_of_data section14Catalog 8 _ hnum valid751
  · exact recordValid_of_data section14Catalog 8 _ hnum valid752
  · exact recordValid_of_data section14Catalog 8 _ hnum valid753
  · exact recordValid_of_data section14Catalog 8 _ hnum valid754
  · exact recordValid_of_data section14Catalog 8 _ hnum valid755
  · exact recordValid_of_data section14Catalog 8 _ hnum valid756
  · exact recordValid_of_data section14Catalog 8 _ hnum valid757
  · exact recordValid_of_data section14Catalog 8 _ hnum valid758
  · exact recordValid_of_data section14Catalog 8 _ hnum valid759
  · exact recordValid_of_data section14Catalog 8 _ hnum valid760
  · exact recordValid_of_data section14Catalog 8 _ hnum valid761
  · exact recordValid_of_data section14Catalog 8 _ hnum valid762
  · exact recordValid_of_data section14Catalog 8 _ hnum valid763
  · exact recordValid_of_data section14Catalog 8 _ hnum valid764
  · exact recordValid_of_data section14Catalog 8 _ hnum valid765
  · exact recordValid_of_data section14Catalog 8 _ hnum valid766
  · exact recordValid_of_data section14Catalog 8 _ hnum valid767
end Section14Records_8_736_768

#print axioms solution
