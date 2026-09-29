-- Prove2me | solution 1 for Freiman.section14_s0008_records_2112_2144
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:50:36.219977+00:00
-- url     : https://prove2.me/submissions/e3a5b770-7793-410c-a775-74b64fcc0c9b

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
namespace Section14Records_8_2112_2144
private theorem valid2112 : RecordDataValid section14Catalog 8 (⟨285,(10),[8,12],[10],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2113 : RecordDataValid section14Catalog 8 (⟨285,(11),[8,12],[10],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2114 : RecordDataValid section14Catalog 8 (⟨285,(12),[8,12],[10],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2115 : RecordDataValid section14Catalog 8 (⟨285,(13),[8,12],[10],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2116 : RecordDataValid section14Catalog 8 (⟨285,(14),[8,12],[10],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2117 : RecordDataValid section14Catalog 8 (⟨285,(15),[8,12],[10],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2118 : RecordDataValid section14Catalog 8 (⟨285,(16),[8,12],[10],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2119 : RecordDataValid section14Catalog 8 (⟨285,(17),[8,12],[10],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2120 : RecordDataValid section14Catalog 8 (⟨285,(18),[8,12],[10],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2121 : RecordDataValid section14Catalog 8 (⟨285,(19),[8,12],[10],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2122 : RecordDataValid section14Catalog 8 (⟨285,(20),[8,12],[10],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2123 : RecordDataValid section14Catalog 8 (⟨285,(21),[8,12],[10],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2124 : RecordDataValid section14Catalog 8 (⟨285,(22),[8,12],[10],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2125 : RecordDataValid section14Catalog 8 (⟨285,(23),[8,12],[10],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2126 : RecordDataValid section14Catalog 8 (⟨285,(24),[8,12],[10],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2127 : RecordDataValid section14Catalog 8 (⟨288,(0),[8,12],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2128 : RecordDataValid section14Catalog 8 (⟨288,(1),[8,12],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2129 : RecordDataValid section14Catalog 8 (⟨288,(2),[8,12],[10],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2130 : RecordDataValid section14Catalog 8 (⟨288,(3),[8,12],[10],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2131 : RecordDataValid section14Catalog 8 (⟨288,(4),[8,12],[10],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2132 : RecordDataValid section14Catalog 8 (⟨288,(5),[8,12],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2133 : RecordDataValid section14Catalog 8 (⟨288,(6),[8,12],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2134 : RecordDataValid section14Catalog 8 (⟨288,(7),[8,12],[10],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2135 : RecordDataValid section14Catalog 8 (⟨288,(8),[8,12],[10],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2136 : RecordDataValid section14Catalog 8 (⟨288,(9),[8,12],[10],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2137 : RecordDataValid section14Catalog 8 (⟨288,(10),[8,12],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2138 : RecordDataValid section14Catalog 8 (⟨288,(11),[8,12],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2139 : RecordDataValid section14Catalog 8 (⟨288,(12),[8,12],[10],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2140 : RecordDataValid section14Catalog 8 (⟨288,(13),[8,12],[10],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2141 : RecordDataValid section14Catalog 8 (⟨288,(14),[8,12],[10],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2142 : RecordDataValid section14Catalog 8 (⟨288,(15),[8,12],[10],1140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1140,[3,5,7,8,9,11,12,15],1144⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2143 : RecordDataValid section14Catalog 8 (⟨288,(16),[8,12],[10],1141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1141,[3,5,7,8,9,11,12,15],1145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2112).take 32 = [⟨285,(10),[8,12],[10],1430⟩,⟨285,(11),[8,12],[10],1430⟩,⟨285,(12),[8,12],[10],1431⟩,⟨285,(13),[8,12],[10],1432⟩,⟨285,(14),[8,12],[10],1433⟩,⟨285,(15),[8,12],[10],1435⟩,⟨285,(16),[8,12],[10],1435⟩,⟨285,(17),[8,12],[10],1431⟩,⟨285,(18),[8,12],[10],1432⟩,⟨285,(19),[8,12],[10],1433⟩,⟨285,(20),[8,12],[10],1436⟩,⟨285,(21),[8,12],[10],1436⟩,⟨285,(22),[8,12],[10],1436⟩,⟨285,(23),[8,12],[10],1432⟩,⟨285,(24),[8,12],[10],1433⟩,⟨288,(0),[8,12],[10],1134⟩,⟨288,(1),[8,12],[10],1135⟩,⟨288,(2),[8,12],[10],1136⟩,⟨288,(3),[8,12],[10],1136⟩,⟨288,(4),[8,12],[10],1136⟩,⟨288,(5),[8,12],[10],1134⟩,⟨288,(6),[8,12],[10],1135⟩,⟨288,(7),[8,12],[10],1137⟩,⟨288,(8),[8,12],[10],1138⟩,⟨288,(9),[8,12],[10],1137⟩,⟨288,(10),[8,12],[10],1134⟩,⟨288,(11),[8,12],[10],1135⟩,⟨288,(12),[8,12],[10],1139⟩,⟨288,(13),[8,12],[10],1138⟩,⟨288,(14),[8,12],[10],1139⟩,⟨288,(15),[8,12],[10],1140⟩,⟨288,(16),[8,12],[10],1141⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2112
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2113
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2114
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2115
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2116
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2117
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2118
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2119
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2120
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2121
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2122
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2123
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2124
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2125
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2126
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2127
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2128
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2129
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2130
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2131
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2132
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2133
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2134
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2135
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2136
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2137
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2138
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2139
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2140
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2141
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2142
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2143
end Section14Records_8_2112_2144

#print axioms solution
