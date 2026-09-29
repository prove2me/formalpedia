-- Prove2me | solution 1 for Freiman.section14_s0010_records_2112_2144
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:52:29.658985+00:00
-- url     : https://prove2.me/submissions/c5ae2fe4-c0bc-48b5-8f0d-4aba16a63c01

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
namespace Section14Records_10_2112_2144
private theorem valid2112 : RecordDataValid section14Catalog 10 (⟨227,(0),[9,10],[42],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2113 : RecordDataValid section14Catalog 10 (⟨227,(1),[9,10],[42],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2114 : RecordDataValid section14Catalog 10 (⟨227,(2),[10],[42],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2115 : RecordDataValid section14Catalog 10 (⟨227,(3),[9,10],[42],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2116 : RecordDataValid section14Catalog 10 (⟨227,(4),[10],[42],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2117 : RecordDataValid section14Catalog 10 (⟨227,(5),[9,10],[42],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2118 : RecordDataValid section14Catalog 10 (⟨227,(6),[9,10],[42],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2119 : RecordDataValid section14Catalog 10 (⟨227,(7),[10],[42],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2120 : RecordDataValid section14Catalog 10 (⟨227,(8),[9,10],[42],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2121 : RecordDataValid section14Catalog 10 (⟨227,(9),[10],[42],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2122 : RecordDataValid section14Catalog 10 (⟨227,(10),[9,10],[42],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2123 : RecordDataValid section14Catalog 10 (⟨227,(11),[9,10],[42],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2124 : RecordDataValid section14Catalog 10 (⟨227,(12),[10],[42],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2125 : RecordDataValid section14Catalog 10 (⟨227,(13),[9,10],[42],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2126 : RecordDataValid section14Catalog 10 (⟨227,(14),[10],[42],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2127 : RecordDataValid section14Catalog 10 (⟨227,(15),[9,10],[42],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2128 : RecordDataValid section14Catalog 10 (⟨227,(16),[9,10],[42],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2129 : RecordDataValid section14Catalog 10 (⟨227,(17),[10],[42],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2130 : RecordDataValid section14Catalog 10 (⟨227,(18),[9,10],[42],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2131 : RecordDataValid section14Catalog 10 (⟨227,(19),[10],[42],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2132 : RecordDataValid section14Catalog 10 (⟨227,(20),[9,10],[42],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2133 : RecordDataValid section14Catalog 10 (⟨227,(21),[9,10],[42],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2134 : RecordDataValid section14Catalog 10 (⟨227,(22),[10],[42],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2135 : RecordDataValid section14Catalog 10 (⟨227,(23),[9,10],[42],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2136 : RecordDataValid section14Catalog 10 (⟨227,(24),[10],[42],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2137 : RecordDataValid section14Catalog 10 (⟨228,(0),[9,10],[42],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2138 : RecordDataValid section14Catalog 10 (⟨228,(1),[9,10],[42],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2139 : RecordDataValid section14Catalog 10 (⟨228,(2),[9,10],[42],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2140 : RecordDataValid section14Catalog 10 (⟨228,(3),[9,10],[42],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2141 : RecordDataValid section14Catalog 10 (⟨228,(4),[9,10],[42],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2142 : RecordDataValid section14Catalog 10 (⟨228,(5),[9,10],[42],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2143 : RecordDataValid section14Catalog 10 (⟨228,(6),[9,10],[42],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2112).take 32 = [⟨227,(0),[9,10],[42],773⟩,⟨227,(1),[9,10],[42],774⟩,⟨227,(2),[10],[42],775⟩,⟨227,(3),[9,10],[42],776⟩,⟨227,(4),[10],[42],775⟩,⟨227,(5),[9,10],[42],773⟩,⟨227,(6),[9,10],[42],774⟩,⟨227,(7),[10],[42],775⟩,⟨227,(8),[9,10],[42],776⟩,⟨227,(9),[10],[42],775⟩,⟨227,(10),[9,10],[42],777⟩,⟨227,(11),[9,10],[42],778⟩,⟨227,(12),[10],[42],779⟩,⟨227,(13),[9,10],[42],780⟩,⟨227,(14),[10],[42],779⟩,⟨227,(15),[9,10],[42],781⟩,⟨227,(16),[9,10],[42],782⟩,⟨227,(17),[10],[42],783⟩,⟨227,(18),[9,10],[42],784⟩,⟨227,(19),[10],[42],783⟩,⟨227,(20),[9,10],[42],785⟩,⟨227,(21),[9,10],[42],786⟩,⟨227,(22),[10],[42],787⟩,⟨227,(23),[9,10],[42],788⟩,⟨227,(24),[10],[42],787⟩,⟨228,(0),[9,10],[42],789⟩,⟨228,(1),[9,10],[42],790⟩,⟨228,(2),[9,10],[42],791⟩,⟨228,(3),[9,10],[42],792⟩,⟨228,(4),[9,10],[42],793⟩,⟨228,(5),[9,10],[42],794⟩,⟨228,(6),[9,10],[42],795⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2112
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2113
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2114
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2115
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2116
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2117
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2118
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2119
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2120
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2121
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2122
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2123
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2124
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2125
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2126
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2127
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2128
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2129
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2130
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2131
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2132
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2133
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2134
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2135
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2136
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2137
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2138
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2139
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2140
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2141
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2142
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2143
end Section14Records_10_2112_2144

#print axioms solution
