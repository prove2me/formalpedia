-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_0896_1024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T00:57:30.881263+00:00
-- url     : https://prove2.me/submissions/6fadc4a5-3111-4353-9b89-0b998c3f0d2b

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0896_0928
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_896_928
private theorem valid896 : RecordDataValid section14Catalog 1 (⟨25,(18),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid897 : RecordDataValid section14Catalog 1 (⟨25,(18),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid898 : RecordDataValid section14Catalog 1 (⟨25,(18),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid899 : RecordDataValid section14Catalog 1 (⟨25,(18),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid900 : RecordDataValid section14Catalog 1 (⟨25,(18),[1,5],[134],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid901 : RecordDataValid section14Catalog 1 (⟨25,(18),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid902 : RecordDataValid section14Catalog 1 (⟨25,(18),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid903 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid904 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid905 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid906 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid907 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid908 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid909 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,5],[134],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid910 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid911 : RecordDataValid section14Catalog 1 (⟨25,(19),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid912 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid913 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid914 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid915 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid916 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid917 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,2,13,14],[190],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid918 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,5],[134],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid919 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,13],[135],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid920 : RecordDataValid section14Catalog 1 (⟨25,(20),[1,13],[151],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid921 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid922 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid923 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid924 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid925 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,2,13,14],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid926 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,2,13,14],[190],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid927 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,5],[134],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0896_0928 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 896).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 896).take 32 = [⟨25,(18),[1,2,13,14],[131],35⟩,⟨25,(18),[1,2,13,14],[147],172⟩,⟨25,(18),[1,2,13,14],[150],197⟩,⟨25,(18),[1,2,13,14],[190],221⟩,⟨25,(18),[1,5],[134],35⟩,⟨25,(18),[1,13],[135],35⟩,⟨25,(18),[1,13],[151],172⟩,⟨25,(19),[1,2,5,6],[130],35⟩,⟨25,(19),[1,2,5,6,13,14],[146],150⟩,⟨25,(19),[1,2,13,14],[131],35⟩,⟨25,(19),[1,2,13,14],[147],172⟩,⟨25,(19),[1,2,13,14],[150],197⟩,⟨25,(19),[1,2,13,14],[190],221⟩,⟨25,(19),[1,5],[134],35⟩,⟨25,(19),[1,13],[135],35⟩,⟨25,(19),[1,13],[151],172⟩,⟨25,(20),[1,2,5,6],[130],38⟩,⟨25,(20),[1,2,5,6,13,14],[146],151⟩,⟨25,(20),[1,2,5,6,13,14],[150],198⟩,⟨25,(20),[1,2,13,14],[131],38⟩,⟨25,(20),[1,2,13,14],[147],173⟩,⟨25,(20),[1,2,13,14],[190],198⟩,⟨25,(20),[1,5],[134],38⟩,⟨25,(20),[1,13],[135],38⟩,⟨25,(20),[1,13],[151],173⟩,⟨25,(21),[1,2,5,6],[130],38⟩,⟨25,(21),[1,2,5,6,13,14],[146],151⟩,⟨25,(21),[1,2,13,14],[131],38⟩,⟨25,(21),[1,2,13,14],[147],173⟩,⟨25,(21),[1,2,13,14],[150],199⟩,⟨25,(21),[1,2,13,14],[190],222⟩,⟨25,(21),[1,5],[134],38⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid896
  · exact recordValid_of_data section14Catalog 1 _ hnum valid897
  · exact recordValid_of_data section14Catalog 1 _ hnum valid898
  · exact recordValid_of_data section14Catalog 1 _ hnum valid899
  · exact recordValid_of_data section14Catalog 1 _ hnum valid900
  · exact recordValid_of_data section14Catalog 1 _ hnum valid901
  · exact recordValid_of_data section14Catalog 1 _ hnum valid902
  · exact recordValid_of_data section14Catalog 1 _ hnum valid903
  · exact recordValid_of_data section14Catalog 1 _ hnum valid904
  · exact recordValid_of_data section14Catalog 1 _ hnum valid905
  · exact recordValid_of_data section14Catalog 1 _ hnum valid906
  · exact recordValid_of_data section14Catalog 1 _ hnum valid907
  · exact recordValid_of_data section14Catalog 1 _ hnum valid908
  · exact recordValid_of_data section14Catalog 1 _ hnum valid909
  · exact recordValid_of_data section14Catalog 1 _ hnum valid910
  · exact recordValid_of_data section14Catalog 1 _ hnum valid911
  · exact recordValid_of_data section14Catalog 1 _ hnum valid912
  · exact recordValid_of_data section14Catalog 1 _ hnum valid913
  · exact recordValid_of_data section14Catalog 1 _ hnum valid914
  · exact recordValid_of_data section14Catalog 1 _ hnum valid915
  · exact recordValid_of_data section14Catalog 1 _ hnum valid916
  · exact recordValid_of_data section14Catalog 1 _ hnum valid917
  · exact recordValid_of_data section14Catalog 1 _ hnum valid918
  · exact recordValid_of_data section14Catalog 1 _ hnum valid919
  · exact recordValid_of_data section14Catalog 1 _ hnum valid920
  · exact recordValid_of_data section14Catalog 1 _ hnum valid921
  · exact recordValid_of_data section14Catalog 1 _ hnum valid922
  · exact recordValid_of_data section14Catalog 1 _ hnum valid923
  · exact recordValid_of_data section14Catalog 1 _ hnum valid924
  · exact recordValid_of_data section14Catalog 1 _ hnum valid925
  · exact recordValid_of_data section14Catalog 1 _ hnum valid926
  · exact recordValid_of_data section14Catalog 1 _ hnum valid927
end Section14Records_1_896_928

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0896_0928


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0928_0960
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_928_960
private theorem valid928 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,13],[135],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid929 : RecordDataValid section14Catalog 1 (⟨25,(21),[1,13],[151],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid930 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid931 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid932 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid933 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid934 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,2,13,14],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid935 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,2,13,14],[190],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid936 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,5],[134],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid937 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,13],[135],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid938 : RecordDataValid section14Catalog 1 (⟨25,(22),[1,13],[151],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid939 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid940 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid941 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid942 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid943 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,2,13,14],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid944 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,2,13,14],[190],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid945 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,5],[134],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid946 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,13],[135],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid947 : RecordDataValid section14Catalog 1 (⟨25,(23),[1,13],[151],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid948 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid949 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid950 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid951 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid952 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,2,13,14],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid953 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,2,13,14],[190],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid954 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,5],[134],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid955 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,13],[135],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid956 : RecordDataValid section14Catalog 1 (⟨25,(24),[1,13],[151],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid957 : RecordDataValid section14Catalog 1 (⟨28,(0),[1],[146],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid958 : RecordDataValid section14Catalog 1 (⟨28,(0),[1],[151],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid959 : RecordDataValid section14Catalog 1 (⟨28,(0),[1],[147],174⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨174,[1,5,9,10],174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0928_0960 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 928).take 32 = [⟨25,(21),[1,13],[135],38⟩,⟨25,(21),[1,13],[151],173⟩,⟨25,(22),[1,2,5,6],[130],38⟩,⟨25,(22),[1,2,5,6,13,14],[146],151⟩,⟨25,(22),[1,2,13,14],[131],38⟩,⟨25,(22),[1,2,13,14],[147],173⟩,⟨25,(22),[1,2,13,14],[150],199⟩,⟨25,(22),[1,2,13,14],[190],222⟩,⟨25,(22),[1,5],[134],38⟩,⟨25,(22),[1,13],[135],38⟩,⟨25,(22),[1,13],[151],173⟩,⟨25,(23),[1,2,5,6],[130],38⟩,⟨25,(23),[1,2,5,6,13,14],[146],151⟩,⟨25,(23),[1,2,13,14],[131],38⟩,⟨25,(23),[1,2,13,14],[147],173⟩,⟨25,(23),[1,2,13,14],[150],199⟩,⟨25,(23),[1,2,13,14],[190],222⟩,⟨25,(23),[1,5],[134],38⟩,⟨25,(23),[1,13],[135],38⟩,⟨25,(23),[1,13],[151],173⟩,⟨25,(24),[1,2,5,6],[130],38⟩,⟨25,(24),[1,2,5,6,13,14],[146],151⟩,⟨25,(24),[1,2,13,14],[131],38⟩,⟨25,(24),[1,2,13,14],[147],173⟩,⟨25,(24),[1,2,13,14],[150],199⟩,⟨25,(24),[1,2,13,14],[190],222⟩,⟨25,(24),[1,5],[134],38⟩,⟨25,(24),[1,13],[135],38⟩,⟨25,(24),[1,13],[151],173⟩,⟨28,(0),[1],[146],85⟩,⟨28,(0),[1],[151],132⟩,⟨28,(0),[1],[147],174⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid928
  · exact recordValid_of_data section14Catalog 1 _ hnum valid929
  · exact recordValid_of_data section14Catalog 1 _ hnum valid930
  · exact recordValid_of_data section14Catalog 1 _ hnum valid931
  · exact recordValid_of_data section14Catalog 1 _ hnum valid932
  · exact recordValid_of_data section14Catalog 1 _ hnum valid933
  · exact recordValid_of_data section14Catalog 1 _ hnum valid934
  · exact recordValid_of_data section14Catalog 1 _ hnum valid935
  · exact recordValid_of_data section14Catalog 1 _ hnum valid936
  · exact recordValid_of_data section14Catalog 1 _ hnum valid937
  · exact recordValid_of_data section14Catalog 1 _ hnum valid938
  · exact recordValid_of_data section14Catalog 1 _ hnum valid939
  · exact recordValid_of_data section14Catalog 1 _ hnum valid940
  · exact recordValid_of_data section14Catalog 1 _ hnum valid941
  · exact recordValid_of_data section14Catalog 1 _ hnum valid942
  · exact recordValid_of_data section14Catalog 1 _ hnum valid943
  · exact recordValid_of_data section14Catalog 1 _ hnum valid944
  · exact recordValid_of_data section14Catalog 1 _ hnum valid945
  · exact recordValid_of_data section14Catalog 1 _ hnum valid946
  · exact recordValid_of_data section14Catalog 1 _ hnum valid947
  · exact recordValid_of_data section14Catalog 1 _ hnum valid948
  · exact recordValid_of_data section14Catalog 1 _ hnum valid949
  · exact recordValid_of_data section14Catalog 1 _ hnum valid950
  · exact recordValid_of_data section14Catalog 1 _ hnum valid951
  · exact recordValid_of_data section14Catalog 1 _ hnum valid952
  · exact recordValid_of_data section14Catalog 1 _ hnum valid953
  · exact recordValid_of_data section14Catalog 1 _ hnum valid954
  · exact recordValid_of_data section14Catalog 1 _ hnum valid955
  · exact recordValid_of_data section14Catalog 1 _ hnum valid956
  · exact recordValid_of_data section14Catalog 1 _ hnum valid957
  · exact recordValid_of_data section14Catalog 1 _ hnum valid958
  · exact recordValid_of_data section14Catalog 1 _ hnum valid959
end Section14Records_1_928_960

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0928_0960


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0960_0992
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_960_992
private theorem valid960 : RecordDataValid section14Catalog 1 (⟨28,(0),[1,2],[190],223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨223,[1,2,3],223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid961 : RecordDataValid section14Catalog 1 (⟨28,(0),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid962 : RecordDataValid section14Catalog 1 (⟨28,(0),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid963 : RecordDataValid section14Catalog 1 (⟨28,(0),[1,5],[130],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid964 : RecordDataValid section14Catalog 1 (⟨28,(0),[1,5],[134,135],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid965 : RecordDataValid section14Catalog 1 (⟨28,(1),[1],[146],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid966 : RecordDataValid section14Catalog 1 (⟨28,(1),[1],[151],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid967 : RecordDataValid section14Catalog 1 (⟨28,(1),[1],[147],174⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨174,[1,5,9,10],174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid968 : RecordDataValid section14Catalog 1 (⟨28,(1),[1,2],[190],223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨223,[1,2,3],223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid969 : RecordDataValid section14Catalog 1 (⟨28,(1),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid970 : RecordDataValid section14Catalog 1 (⟨28,(1),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid971 : RecordDataValid section14Catalog 1 (⟨28,(1),[1,5],[130],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid972 : RecordDataValid section14Catalog 1 (⟨28,(1),[1,5],[134,135],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid973 : RecordDataValid section14Catalog 1 (⟨28,(2),[1],[146],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid974 : RecordDataValid section14Catalog 1 (⟨28,(2),[1],[151],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid975 : RecordDataValid section14Catalog 1 (⟨28,(2),[1],[147],174⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨174,[1,5,9,10],174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid976 : RecordDataValid section14Catalog 1 (⟨28,(2),[1,2],[190],223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨223,[1,2,3],223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid977 : RecordDataValid section14Catalog 1 (⟨28,(2),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid978 : RecordDataValid section14Catalog 1 (⟨28,(2),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid979 : RecordDataValid section14Catalog 1 (⟨28,(2),[1,5],[130],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid980 : RecordDataValid section14Catalog 1 (⟨28,(2),[1,5],[134,135],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid981 : RecordDataValid section14Catalog 1 (⟨28,(3),[1],[146],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid982 : RecordDataValid section14Catalog 1 (⟨28,(3),[1],[151],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid983 : RecordDataValid section14Catalog 1 (⟨28,(3),[1],[147],174⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨174,[1,5,9,10],174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid984 : RecordDataValid section14Catalog 1 (⟨28,(3),[1,2],[190],223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨223,[1,2,3],223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid985 : RecordDataValid section14Catalog 1 (⟨28,(3),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid986 : RecordDataValid section14Catalog 1 (⟨28,(3),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid987 : RecordDataValid section14Catalog 1 (⟨28,(3),[1,5],[130],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid988 : RecordDataValid section14Catalog 1 (⟨28,(3),[1,5],[134,135],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid989 : RecordDataValid section14Catalog 1 (⟨28,(4),[1],[146],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid990 : RecordDataValid section14Catalog 1 (⟨28,(4),[1],[151],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid991 : RecordDataValid section14Catalog 1 (⟨28,(4),[1],[147],174⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨174,[1,5,9,10],174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0960_0992 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 960).take 32 = [⟨28,(0),[1,2],[190],223⟩,⟨28,(0),[1,2,5,6],[131],113⟩,⟨28,(0),[1,2,5,6],[150],132⟩,⟨28,(0),[1,5],[130],85⟩,⟨28,(0),[1,5],[134,135],132⟩,⟨28,(1),[1],[146],85⟩,⟨28,(1),[1],[151],132⟩,⟨28,(1),[1],[147],174⟩,⟨28,(1),[1,2],[190],223⟩,⟨28,(1),[1,2,5,6],[131],113⟩,⟨28,(1),[1,2,5,6],[150],132⟩,⟨28,(1),[1,5],[130],85⟩,⟨28,(1),[1,5],[134,135],132⟩,⟨28,(2),[1],[146],85⟩,⟨28,(2),[1],[151],132⟩,⟨28,(2),[1],[147],174⟩,⟨28,(2),[1,2],[190],223⟩,⟨28,(2),[1,2,5,6],[131],113⟩,⟨28,(2),[1,2,5,6],[150],132⟩,⟨28,(2),[1,5],[130],85⟩,⟨28,(2),[1,5],[134,135],132⟩,⟨28,(3),[1],[146],85⟩,⟨28,(3),[1],[151],132⟩,⟨28,(3),[1],[147],174⟩,⟨28,(3),[1,2],[190],223⟩,⟨28,(3),[1,2,5,6],[131],113⟩,⟨28,(3),[1,2,5,6],[150],132⟩,⟨28,(3),[1,5],[130],85⟩,⟨28,(3),[1,5],[134,135],132⟩,⟨28,(4),[1],[146],85⟩,⟨28,(4),[1],[151],132⟩,⟨28,(4),[1],[147],174⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid960
  · exact recordValid_of_data section14Catalog 1 _ hnum valid961
  · exact recordValid_of_data section14Catalog 1 _ hnum valid962
  · exact recordValid_of_data section14Catalog 1 _ hnum valid963
  · exact recordValid_of_data section14Catalog 1 _ hnum valid964
  · exact recordValid_of_data section14Catalog 1 _ hnum valid965
  · exact recordValid_of_data section14Catalog 1 _ hnum valid966
  · exact recordValid_of_data section14Catalog 1 _ hnum valid967
  · exact recordValid_of_data section14Catalog 1 _ hnum valid968
  · exact recordValid_of_data section14Catalog 1 _ hnum valid969
  · exact recordValid_of_data section14Catalog 1 _ hnum valid970
  · exact recordValid_of_data section14Catalog 1 _ hnum valid971
  · exact recordValid_of_data section14Catalog 1 _ hnum valid972
  · exact recordValid_of_data section14Catalog 1 _ hnum valid973
  · exact recordValid_of_data section14Catalog 1 _ hnum valid974
  · exact recordValid_of_data section14Catalog 1 _ hnum valid975
  · exact recordValid_of_data section14Catalog 1 _ hnum valid976
  · exact recordValid_of_data section14Catalog 1 _ hnum valid977
  · exact recordValid_of_data section14Catalog 1 _ hnum valid978
  · exact recordValid_of_data section14Catalog 1 _ hnum valid979
  · exact recordValid_of_data section14Catalog 1 _ hnum valid980
  · exact recordValid_of_data section14Catalog 1 _ hnum valid981
  · exact recordValid_of_data section14Catalog 1 _ hnum valid982
  · exact recordValid_of_data section14Catalog 1 _ hnum valid983
  · exact recordValid_of_data section14Catalog 1 _ hnum valid984
  · exact recordValid_of_data section14Catalog 1 _ hnum valid985
  · exact recordValid_of_data section14Catalog 1 _ hnum valid986
  · exact recordValid_of_data section14Catalog 1 _ hnum valid987
  · exact recordValid_of_data section14Catalog 1 _ hnum valid988
  · exact recordValid_of_data section14Catalog 1 _ hnum valid989
  · exact recordValid_of_data section14Catalog 1 _ hnum valid990
  · exact recordValid_of_data section14Catalog 1 _ hnum valid991
end Section14Records_1_960_992

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0960_0992


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0992_1024
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_992_1024
private theorem valid992 : RecordDataValid section14Catalog 1 (⟨28,(4),[1,2],[190],223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨223,[1,2,3],223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid993 : RecordDataValid section14Catalog 1 (⟨28,(4),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid994 : RecordDataValid section14Catalog 1 (⟨28,(4),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid995 : RecordDataValid section14Catalog 1 (⟨28,(4),[1,5],[130],85⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨85,[1,5,9],85⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid996 : RecordDataValid section14Catalog 1 (⟨28,(4),[1,5],[134,135],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid997 : RecordDataValid section14Catalog 1 (⟨28,(5),[1],[146],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid998 : RecordDataValid section14Catalog 1 (⟨28,(5),[1],[151],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid999 : RecordDataValid section14Catalog 1 (⟨28,(5),[1],[147],175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨175,[1,5,9,10],175⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1000 : RecordDataValid section14Catalog 1 (⟨28,(5),[1,2],[190],224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨224,[1,2,3],224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1001 : RecordDataValid section14Catalog 1 (⟨28,(5),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1002 : RecordDataValid section14Catalog 1 (⟨28,(5),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1003 : RecordDataValid section14Catalog 1 (⟨28,(5),[1,5],[130],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1004 : RecordDataValid section14Catalog 1 (⟨28,(5),[1,5],[134,135],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1005 : RecordDataValid section14Catalog 1 (⟨28,(6),[1],[146],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1006 : RecordDataValid section14Catalog 1 (⟨28,(6),[1],[151],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1007 : RecordDataValid section14Catalog 1 (⟨28,(6),[1],[147],175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨175,[1,5,9,10],175⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1008 : RecordDataValid section14Catalog 1 (⟨28,(6),[1,2],[190],224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨224,[1,2,3],224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1009 : RecordDataValid section14Catalog 1 (⟨28,(6),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1010 : RecordDataValid section14Catalog 1 (⟨28,(6),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1011 : RecordDataValid section14Catalog 1 (⟨28,(6),[1,5],[130],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1012 : RecordDataValid section14Catalog 1 (⟨28,(6),[1,5],[134,135],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1013 : RecordDataValid section14Catalog 1 (⟨28,(7),[1],[146],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1014 : RecordDataValid section14Catalog 1 (⟨28,(7),[1],[151],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1015 : RecordDataValid section14Catalog 1 (⟨28,(7),[1],[147],175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨175,[1,5,9,10],175⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1016 : RecordDataValid section14Catalog 1 (⟨28,(7),[1,2],[190],224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨224,[1,2,3],224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1017 : RecordDataValid section14Catalog 1 (⟨28,(7),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1018 : RecordDataValid section14Catalog 1 (⟨28,(7),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1019 : RecordDataValid section14Catalog 1 (⟨28,(7),[1,5],[130],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1020 : RecordDataValid section14Catalog 1 (⟨28,(7),[1,5],[134,135],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1021 : RecordDataValid section14Catalog 1 (⟨28,(8),[1],[146],86⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨86,[1,5,9],86⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1022 : RecordDataValid section14Catalog 1 (⟨28,(8),[1],[151],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1023 : RecordDataValid section14Catalog 1 (⟨28,(8),[1],[147],175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨175,[1,5,9,10],175⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0992_1024 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 992).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 992).take 32 = [⟨28,(4),[1,2],[190],223⟩,⟨28,(4),[1,2,5,6],[131],113⟩,⟨28,(4),[1,2,5,6],[150],132⟩,⟨28,(4),[1,5],[130],85⟩,⟨28,(4),[1,5],[134,135],132⟩,⟨28,(5),[1],[146],86⟩,⟨28,(5),[1],[151],133⟩,⟨28,(5),[1],[147],175⟩,⟨28,(5),[1,2],[190],224⟩,⟨28,(5),[1,2,5,6],[131],114⟩,⟨28,(5),[1,2,5,6],[150],133⟩,⟨28,(5),[1,5],[130],86⟩,⟨28,(5),[1,5],[134,135],133⟩,⟨28,(6),[1],[146],86⟩,⟨28,(6),[1],[151],133⟩,⟨28,(6),[1],[147],175⟩,⟨28,(6),[1,2],[190],224⟩,⟨28,(6),[1,2,5,6],[131],114⟩,⟨28,(6),[1,2,5,6],[150],133⟩,⟨28,(6),[1,5],[130],86⟩,⟨28,(6),[1,5],[134,135],133⟩,⟨28,(7),[1],[146],86⟩,⟨28,(7),[1],[151],133⟩,⟨28,(7),[1],[147],175⟩,⟨28,(7),[1,2],[190],224⟩,⟨28,(7),[1,2,5,6],[131],114⟩,⟨28,(7),[1,2,5,6],[150],133⟩,⟨28,(7),[1,5],[130],86⟩,⟨28,(7),[1,5],[134,135],133⟩,⟨28,(8),[1],[146],86⟩,⟨28,(8),[1],[151],133⟩,⟨28,(8),[1],[147],175⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid992
  · exact recordValid_of_data section14Catalog 1 _ hnum valid993
  · exact recordValid_of_data section14Catalog 1 _ hnum valid994
  · exact recordValid_of_data section14Catalog 1 _ hnum valid995
  · exact recordValid_of_data section14Catalog 1 _ hnum valid996
  · exact recordValid_of_data section14Catalog 1 _ hnum valid997
  · exact recordValid_of_data section14Catalog 1 _ hnum valid998
  · exact recordValid_of_data section14Catalog 1 _ hnum valid999
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1000
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1001
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1002
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1003
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1004
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1005
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1006
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1007
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1008
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1009
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1010
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1011
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1012
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1013
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1014
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1015
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1016
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1017
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1018
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1019
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1020
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1021
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1022
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1023
end Section14Records_1_992_1024

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0992_1024

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 896).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 896 960 1024 (by decide) (by decide) (all_of_interval_split P xs 896 928 960 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_0896_0928 hnum) (Freiman.workReverse20260919_s0001_records_0928_0960 hnum)) (all_of_interval_split P xs 960 992 1024 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_0960_0992 hnum) (Freiman.workReverse20260919_s0001_records_0992_1024 hnum)))

#print axioms solution
