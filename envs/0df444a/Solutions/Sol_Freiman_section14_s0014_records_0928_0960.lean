-- Prove2me | solution 1 for Freiman.section14_s0014_records_0928_0960
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:45:37.563403+00:00
-- url     : https://prove2.me/submissions/83bd8e27-930d-4819-b2f5-ee7e585f35cf

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
namespace Section14Records_14_928_960
private theorem valid928 : RecordDataValid section14Catalog 14 (⟨67,(1),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid929 : RecordDataValid section14Catalog 14 (⟨67,(2),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid930 : RecordDataValid section14Catalog 14 (⟨67,(3),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid931 : RecordDataValid section14Catalog 14 (⟨67,(4),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid932 : RecordDataValid section14Catalog 14 (⟨67,(5),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid933 : RecordDataValid section14Catalog 14 (⟨67,(6),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid934 : RecordDataValid section14Catalog 14 (⟨67,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid935 : RecordDataValid section14Catalog 14 (⟨67,(8),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid936 : RecordDataValid section14Catalog 14 (⟨67,(9),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid937 : RecordDataValid section14Catalog 14 (⟨67,(10),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid938 : RecordDataValid section14Catalog 14 (⟨67,(11),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid939 : RecordDataValid section14Catalog 14 (⟨67,(12),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid940 : RecordDataValid section14Catalog 14 (⟨67,(13),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid941 : RecordDataValid section14Catalog 14 (⟨67,(14),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid942 : RecordDataValid section14Catalog 14 (⟨67,(15),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid943 : RecordDataValid section14Catalog 14 (⟨67,(16),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid944 : RecordDataValid section14Catalog 14 (⟨67,(17),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid945 : RecordDataValid section14Catalog 14 (⟨67,(18),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid946 : RecordDataValid section14Catalog 14 (⟨67,(19),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid947 : RecordDataValid section14Catalog 14 (⟨67,(20),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid948 : RecordDataValid section14Catalog 14 (⟨67,(21),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid949 : RecordDataValid section14Catalog 14 (⟨67,(22),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid950 : RecordDataValid section14Catalog 14 (⟨67,(23),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid951 : RecordDataValid section14Catalog 14 (⟨67,(24),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid952 : RecordDataValid section14Catalog 14 (⟨69,(0),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid953 : RecordDataValid section14Catalog 14 (⟨69,(1),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid954 : RecordDataValid section14Catalog 14 (⟨69,(2),[2,14],[190],261⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨261,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid955 : RecordDataValid section14Catalog 14 (⟨69,(3),[2,14],[190],262⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨262,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid956 : RecordDataValid section14Catalog 14 (⟨69,(4),[2,14],[190],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid957 : RecordDataValid section14Catalog 14 (⟨69,(5),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid958 : RecordDataValid section14Catalog 14 (⟨69,(6),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid959 : RecordDataValid section14Catalog 14 (⟨69,(7),[1,2,5,6,13,14],[190],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 14 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 928).take 32 = [⟨67,(1),[1,2,5,6,13,14],[190],2⟩,⟨67,(2),[1,2,5,6,13,14],[190],2⟩,⟨67,(3),[1,2,5,6,13,14],[190],2⟩,⟨67,(4),[1,2,5,6,13,14],[190],2⟩,⟨67,(5),[1,2,5,6,13,14],[190],2⟩,⟨67,(6),[1,2,5,6,13,14],[190],2⟩,⟨67,(7),[1,2,5,6,13,14],[190],2⟩,⟨67,(8),[1,2,5,6,13,14],[190],2⟩,⟨67,(9),[1,2,5,6,13,14],[190],2⟩,⟨67,(10),[1,2,5,6,13,14],[190],2⟩,⟨67,(11),[1,2,5,6,13,14],[190],2⟩,⟨67,(12),[1,2,5,6,13,14],[190],2⟩,⟨67,(13),[1,2,5,6,13,14],[190],2⟩,⟨67,(14),[1,2,5,6,13,14],[190],2⟩,⟨67,(15),[1,2,5,6,13,14],[190],2⟩,⟨67,(16),[1,2,5,6,13,14],[190],2⟩,⟨67,(17),[1,2,5,6,13,14],[190],2⟩,⟨67,(18),[1,2,5,6,13,14],[190],2⟩,⟨67,(19),[1,2,5,6,13,14],[190],2⟩,⟨67,(20),[1,2,5,6,13,14],[190],2⟩,⟨67,(21),[1,2,5,6,13,14],[190],2⟩,⟨67,(22),[1,2,5,6,13,14],[190],2⟩,⟨67,(23),[1,2,5,6,13,14],[190],2⟩,⟨67,(24),[1,2,5,6,13,14],[190],2⟩,⟨69,(0),[1,2,5,6,13,14],[190],189⟩,⟨69,(1),[1,2,5,6,13,14],[190],260⟩,⟨69,(2),[2,14],[190],261⟩,⟨69,(3),[2,14],[190],262⟩,⟨69,(4),[2,14],[190],263⟩,⟨69,(5),[1,2,5,6,13,14],[190],189⟩,⟨69,(6),[1,2,5,6,13,14],[190],260⟩,⟨69,(7),[1,2,5,6,13,14],[190],375⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 14 _ hnum valid928
  · exact recordValid_of_data section14Catalog 14 _ hnum valid929
  · exact recordValid_of_data section14Catalog 14 _ hnum valid930
  · exact recordValid_of_data section14Catalog 14 _ hnum valid931
  · exact recordValid_of_data section14Catalog 14 _ hnum valid932
  · exact recordValid_of_data section14Catalog 14 _ hnum valid933
  · exact recordValid_of_data section14Catalog 14 _ hnum valid934
  · exact recordValid_of_data section14Catalog 14 _ hnum valid935
  · exact recordValid_of_data section14Catalog 14 _ hnum valid936
  · exact recordValid_of_data section14Catalog 14 _ hnum valid937
  · exact recordValid_of_data section14Catalog 14 _ hnum valid938
  · exact recordValid_of_data section14Catalog 14 _ hnum valid939
  · exact recordValid_of_data section14Catalog 14 _ hnum valid940
  · exact recordValid_of_data section14Catalog 14 _ hnum valid941
  · exact recordValid_of_data section14Catalog 14 _ hnum valid942
  · exact recordValid_of_data section14Catalog 14 _ hnum valid943
  · exact recordValid_of_data section14Catalog 14 _ hnum valid944
  · exact recordValid_of_data section14Catalog 14 _ hnum valid945
  · exact recordValid_of_data section14Catalog 14 _ hnum valid946
  · exact recordValid_of_data section14Catalog 14 _ hnum valid947
  · exact recordValid_of_data section14Catalog 14 _ hnum valid948
  · exact recordValid_of_data section14Catalog 14 _ hnum valid949
  · exact recordValid_of_data section14Catalog 14 _ hnum valid950
  · exact recordValid_of_data section14Catalog 14 _ hnum valid951
  · exact recordValid_of_data section14Catalog 14 _ hnum valid952
  · exact recordValid_of_data section14Catalog 14 _ hnum valid953
  · exact recordValid_of_data section14Catalog 14 _ hnum valid954
  · exact recordValid_of_data section14Catalog 14 _ hnum valid955
  · exact recordValid_of_data section14Catalog 14 _ hnum valid956
  · exact recordValid_of_data section14Catalog 14 _ hnum valid957
  · exact recordValid_of_data section14Catalog 14 _ hnum valid958
  · exact recordValid_of_data section14Catalog 14 _ hnum valid959
end Section14Records_14_928_960

#print axioms solution
