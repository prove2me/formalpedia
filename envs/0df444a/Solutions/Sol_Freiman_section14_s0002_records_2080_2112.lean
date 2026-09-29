-- Prove2me | solution 1 for Freiman.section14_s0002_records_2080_2112
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T06:50:31.535518+00:00
-- url     : https://prove2.me/submissions/79e8fc0b-f4bc-4157-8b14-b84226dda3a2

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
namespace Section14Records_2_2080_2112
private theorem valid2080 : RecordDataValid section14Catalog 2 (⟨205,(21),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2081 : RecordDataValid section14Catalog 2 (⟨205,(22),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2082 : RecordDataValid section14Catalog 2 (⟨205,(23),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2083 : RecordDataValid section14Catalog 2 (⟨205,(24),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2084 : RecordDataValid section14Catalog 2 (⟨207,(0),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2085 : RecordDataValid section14Catalog 2 (⟨207,(1),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2086 : RecordDataValid section14Catalog 2 (⟨207,(2),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2087 : RecordDataValid section14Catalog 2 (⟨207,(3),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2088 : RecordDataValid section14Catalog 2 (⟨207,(4),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2089 : RecordDataValid section14Catalog 2 (⟨207,(5),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2090 : RecordDataValid section14Catalog 2 (⟨207,(6),[1,2,5,6,13,14],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2091 : RecordDataValid section14Catalog 2 (⟨207,(7),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2092 : RecordDataValid section14Catalog 2 (⟨207,(8),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2093 : RecordDataValid section14Catalog 2 (⟨207,(9),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2094 : RecordDataValid section14Catalog 2 (⟨207,(10),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2095 : RecordDataValid section14Catalog 2 (⟨207,(11),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2096 : RecordDataValid section14Catalog 2 (⟨207,(12),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2097 : RecordDataValid section14Catalog 2 (⟨207,(13),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2098 : RecordDataValid section14Catalog 2 (⟨207,(14),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2099 : RecordDataValid section14Catalog 2 (⟨207,(15),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2100 : RecordDataValid section14Catalog 2 (⟨207,(16),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2101 : RecordDataValid section14Catalog 2 (⟨207,(17),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2102 : RecordDataValid section14Catalog 2 (⟨207,(18),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2103 : RecordDataValid section14Catalog 2 (⟨207,(19),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2104 : RecordDataValid section14Catalog 2 (⟨207,(20),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2105 : RecordDataValid section14Catalog 2 (⟨207,(21),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2106 : RecordDataValid section14Catalog 2 (⟨207,(22),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2107 : RecordDataValid section14Catalog 2 (⟨207,(23),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2108 : RecordDataValid section14Catalog 2 (⟨207,(24),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2109 : RecordDataValid section14Catalog 2 (⟨210,(0),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2110 : RecordDataValid section14Catalog 2 (⟨210,(1),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2111 : RecordDataValid section14Catalog 2 (⟨210,(2),[1,2,5,6,13,14],[170],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2080).take 32 = [⟨205,(21),[1,2,5,6,13,14],[170],716⟩,⟨205,(22),[1,2,5,6,13,14],[170],717⟩,⟨205,(23),[1,2,5,6,13,14],[170],718⟩,⟨205,(24),[1,2,5,6,13,14],[170],719⟩,⟨207,(0),[1,2,5,6,13,14],[170],481⟩,⟨207,(1),[1,2,5,6,13,14],[170],482⟩,⟨207,(2),[1,2,5,6,13,14],[170],481⟩,⟨207,(3),[1,2,5,6,13,14],[170],483⟩,⟨207,(4),[1,2,5,6,13,14],[170],484⟩,⟨207,(5),[1,2,5,6,13,14],[170],481⟩,⟨207,(6),[1,2,5,6,13,14],[170],482⟩,⟨207,(7),[1,2,5,6,13,14],[170],481⟩,⟨207,(8),[1,2,5,6,13,14],[170],483⟩,⟨207,(9),[1,2,5,6,13,14],[170],484⟩,⟨207,(10),[1,2,5,6,13,14],[170],485⟩,⟨207,(11),[1,2,5,6,13,14],[170],485⟩,⟨207,(12),[1,2,5,6,13,14],[170],485⟩,⟨207,(13),[1,2,5,6,13,14],[170],485⟩,⟨207,(14),[1,2,5,6,13,14],[170],484⟩,⟨207,(15),[1,2,5,6,13,14],[170],486⟩,⟨207,(16),[1,2,5,6,13,14],[170],486⟩,⟨207,(17),[1,2,5,6,13,14],[170],486⟩,⟨207,(18),[1,2,5,6,13,14],[170],486⟩,⟨207,(19),[1,2,5,6,13,14],[170],486⟩,⟨207,(20),[1,2,5,6,13,14],[170],487⟩,⟨207,(21),[1,2,5,6,13,14],[170],487⟩,⟨207,(22),[1,2,5,6,13,14],[170],487⟩,⟨207,(23),[1,2,5,6,13,14],[170],487⟩,⟨207,(24),[1,2,5,6,13,14],[170],487⟩,⟨210,(0),[1,2,5,6,13,14],[170],722⟩,⟨210,(1),[1,2,5,6,13,14],[170],723⟩,⟨210,(2),[1,2,5,6,13,14],[170],724⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2080
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2081
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2082
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2083
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2084
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2085
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2086
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2087
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2088
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2089
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2090
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2091
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2092
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2093
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2094
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2095
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2096
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2097
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2098
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2099
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2100
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2101
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2102
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2103
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2104
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2105
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2106
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2107
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2108
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2109
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2110
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2111
end Section14Records_2_2080_2112

#print axioms solution
