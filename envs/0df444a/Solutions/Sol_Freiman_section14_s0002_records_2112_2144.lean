-- Prove2me | solution 1 for Freiman.section14_s0002_records_2112_2144
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T06:52:27.389981+00:00
-- url     : https://prove2.me/submissions/5a822da2-0d47-4657-b8ff-6de2c6dea283

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
namespace Section14Records_2_2112_2144
private theorem valid2112 : RecordDataValid section14Catalog 2 (⟨210,(3),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2113 : RecordDataValid section14Catalog 2 (⟨210,(4),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2114 : RecordDataValid section14Catalog 2 (⟨210,(5),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2115 : RecordDataValid section14Catalog 2 (⟨210,(6),[1,2,5,6,13,14],[170],726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2116 : RecordDataValid section14Catalog 2 (⟨210,(7),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2117 : RecordDataValid section14Catalog 2 (⟨210,(8),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2118 : RecordDataValid section14Catalog 2 (⟨210,(9),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2119 : RecordDataValid section14Catalog 2 (⟨210,(10),[1,2,5,6,13,14],[170],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2120 : RecordDataValid section14Catalog 2 (⟨210,(11),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2121 : RecordDataValid section14Catalog 2 (⟨210,(12),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2122 : RecordDataValid section14Catalog 2 (⟨210,(13),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2123 : RecordDataValid section14Catalog 2 (⟨210,(14),[1,2,5,6,13,14],[170],727⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨727,[1,2,4,5,6,8,9,10,12,13,14,16],728⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2124 : RecordDataValid section14Catalog 2 (⟨210,(15),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2125 : RecordDataValid section14Catalog 2 (⟨213,(0),[1,2,5,6,13,14],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2126 : RecordDataValid section14Catalog 2 (⟨213,(1),[1,2,5,6,13,14],[170],495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2127 : RecordDataValid section14Catalog 2 (⟨213,(2),[1,2,5,6,13,14],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2128 : RecordDataValid section14Catalog 2 (⟨213,(3),[1,2,5,6,13,14],[170],496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2129 : RecordDataValid section14Catalog 2 (⟨213,(4),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2130 : RecordDataValid section14Catalog 2 (⟨213,(5),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2131 : RecordDataValid section14Catalog 2 (⟨213,(6),[2,14],[170],920⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨920,[2,3,14,15],924⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2132 : RecordDataValid section14Catalog 2 (⟨213,(7),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2133 : RecordDataValid section14Catalog 2 (⟨213,(8),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2134 : RecordDataValid section14Catalog 2 (⟨213,(9),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2135 : RecordDataValid section14Catalog 2 (⟨213,(10),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2136 : RecordDataValid section14Catalog 2 (⟨213,(11),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2137 : RecordDataValid section14Catalog 2 (⟨213,(12),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2138 : RecordDataValid section14Catalog 2 (⟨213,(13),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2139 : RecordDataValid section14Catalog 2 (⟨213,(14),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2140 : RecordDataValid section14Catalog 2 (⟨213,(15),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2141 : RecordDataValid section14Catalog 2 (⟨215,(0),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2142 : RecordDataValid section14Catalog 2 (⟨215,(1),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2143 : RecordDataValid section14Catalog 2 (⟨215,(2),[1,2,5,6],[170],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2112).take 32 = [⟨210,(3),[1,2,5,6,13,14],[170],725⟩,⟨210,(4),[1,2,5,6,13,14],[170],722⟩,⟨210,(5),[1,2,5,6,13,14],[170],723⟩,⟨210,(6),[1,2,5,6,13,14],[170],726⟩,⟨210,(7),[1,2,5,6,13,14],[170],725⟩,⟨210,(8),[1,2,5,6,13,14],[170],722⟩,⟨210,(9),[1,2,5,6,13,14],[170],723⟩,⟨210,(10),[1,2,5,6,13,14],[170],724⟩,⟨210,(11),[1,2,5,6,13,14],[170],725⟩,⟨210,(12),[1,2,5,6,13,14],[170],722⟩,⟨210,(13),[1,2,5,6,13,14],[170],723⟩,⟨210,(14),[1,2,5,6,13,14],[170],727⟩,⟨210,(15),[1,2,5,6,13,14],[170],725⟩,⟨213,(0),[1,2,5,6,13,14],[170],494⟩,⟨213,(1),[1,2,5,6,13,14],[170],495⟩,⟨213,(2),[1,2,5,6,13,14],[170],494⟩,⟨213,(3),[1,2,5,6,13,14],[170],496⟩,⟨213,(4),[1,2,5,6,13,14],[170],497⟩,⟨213,(5),[1,2,5,6,13,14],[170],497⟩,⟨213,(6),[2,14],[170],920⟩,⟨213,(7),[1,2,5,6,13,14],[170],497⟩,⟨213,(8),[1,2,5,6,13,14],[170],498⟩,⟨213,(9),[1,2,5,6,13,14],[170],498⟩,⟨213,(10),[1,2,5,6,13,14],[170],498⟩,⟨213,(11),[1,2,5,6,13,14],[170],498⟩,⟨213,(12),[1,2,5,6,13,14],[170],499⟩,⟨213,(13),[1,2,5,6,13,14],[170],499⟩,⟨213,(14),[1,2,5,6,13,14],[170],499⟩,⟨213,(15),[1,2,5,6,13,14],[170],499⟩,⟨215,(0),[1,2,5,6],[170],728⟩,⟨215,(1),[1,2,5,6],[170],729⟩,⟨215,(2),[1,2,5,6],[170],730⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2112
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2113
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2114
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2115
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2116
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2117
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2118
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2119
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2120
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2121
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2122
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2123
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2124
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2125
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2126
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2127
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2128
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2129
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2130
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2131
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2132
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2133
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2134
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2135
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2136
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2137
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2138
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2139
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2140
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2141
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2142
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2143
end Section14Records_2_2112_2144

#print axioms solution
