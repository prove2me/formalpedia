-- Prove2me | solution 1 for Freiman.section14_s0012_records_2112_2144
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:22:36.160977+00:00
-- url     : https://prove2.me/submissions/f2619ed2-8e14-4631-8c47-04fb630464ca

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
namespace Section14Records_12_2112_2144
private theorem valid2112 : RecordDataValid section14Catalog 12 (⟨313,(0),[8,12],[10],1200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1200,[3,5,7,8,9,11,12,15],1204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2113 : RecordDataValid section14Catalog 12 (⟨313,(1),[8,12],[10],1201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1201,[3,5,7,8,9,11,12,15],1205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2114 : RecordDataValid section14Catalog 12 (⟨313,(2),[8,12],[10],1202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1202,[3,5,7,8,9,11,12,15],1206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2115 : RecordDataValid section14Catalog 12 (⟨313,(3),[12],[10],1723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1723,[12],1728⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2116 : RecordDataValid section14Catalog 12 (⟨315,(0),[8,12],[10],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2117 : RecordDataValid section14Catalog 12 (⟨315,(1),[8,12],[10],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2118 : RecordDataValid section14Catalog 12 (⟨315,(2),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2119 : RecordDataValid section14Catalog 12 (⟨315,(3),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2120 : RecordDataValid section14Catalog 12 (⟨315,(4),[8,12],[10],1489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1489,[5,8,9,12],1494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2121 : RecordDataValid section14Catalog 12 (⟨315,(5),[8,12],[10],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2122 : RecordDataValid section14Catalog 12 (⟨315,(6),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2123 : RecordDataValid section14Catalog 12 (⟨315,(7),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2124 : RecordDataValid section14Catalog 12 (⟨315,(8),[8,12],[10],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2125 : RecordDataValid section14Catalog 12 (⟨315,(9),[8,12],[10],1490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1490,[5,8,9,12],1495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2126 : RecordDataValid section14Catalog 12 (⟨315,(10),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2127 : RecordDataValid section14Catalog 12 (⟨315,(11),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2128 : RecordDataValid section14Catalog 12 (⟨315,(12),[8,12],[10],1491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1491,[5,8,9,12],1496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2129 : RecordDataValid section14Catalog 12 (⟨315,(13),[8,12],[10],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2130 : RecordDataValid section14Catalog 12 (⟨315,(14),[8,12],[10],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2131 : RecordDataValid section14Catalog 12 (⟨315,(15),[8,12],[10],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2132 : RecordDataValid section14Catalog 12 (⟨317,(0),[8,12],[10],1211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1211,[3,5,7,8,9,11,12,15],1215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2133 : RecordDataValid section14Catalog 12 (⟨317,(1),[8,12],[10],1212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1212,[3,5,7,8,9,11,12,15],1216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2134 : RecordDataValid section14Catalog 12 (⟨317,(2),[8,12],[10],1213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1213,[3,5,7,8,9,11,12,15],1217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2135 : RecordDataValid section14Catalog 12 (⟨317,(3),[8,12],[10],1214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1214,[3,5,7,8,9,11,12,15],1218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2136 : RecordDataValid section14Catalog 12 (⟨317,(4),[8,12],[10],1215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1215,[3,5,7,8,9,11,12,15],1219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2137 : RecordDataValid section14Catalog 12 (⟨317,(5),[8,12],[10],1216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1216,[3,5,7,8,9,11,12,15],1220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2138 : RecordDataValid section14Catalog 12 (⟨317,(6),[8,12],[10],1217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1217,[3,5,7,8,9,11,12,15],1221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2139 : RecordDataValid section14Catalog 12 (⟨317,(7),[8,12],[10],1218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1218,[3,5,7,8,9,11,12,15],1222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2140 : RecordDataValid section14Catalog 12 (⟨317,(8),[8,12],[10],1492⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1492,[5,8,9,12],1497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2141 : RecordDataValid section14Catalog 12 (⟨317,(9),[8,12],[10],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2142 : RecordDataValid section14Catalog 12 (⟨317,(10),[8,12],[10],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2143 : RecordDataValid section14Catalog 12 (⟨317,(11),[8,12],[10],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2112).take 32 = [⟨313,(0),[8,12],[10],1200⟩,⟨313,(1),[8,12],[10],1201⟩,⟨313,(2),[8,12],[10],1202⟩,⟨313,(3),[12],[10],1723⟩,⟨315,(0),[8,12],[10],1485⟩,⟨315,(1),[8,12],[10],1486⟩,⟨315,(2),[8,12],[10],1487⟩,⟨315,(3),[8,12],[10],1488⟩,⟨315,(4),[8,12],[10],1489⟩,⟨315,(5),[8,12],[10],1486⟩,⟨315,(6),[8,12],[10],1487⟩,⟨315,(7),[8,12],[10],1488⟩,⟨315,(8),[8,12],[10],1485⟩,⟨315,(9),[8,12],[10],1490⟩,⟨315,(10),[8,12],[10],1487⟩,⟨315,(11),[8,12],[10],1488⟩,⟨315,(12),[8,12],[10],1491⟩,⟨315,(13),[8,12],[10],1486⟩,⟨315,(14),[8,12],[10],1487⟩,⟨315,(15),[8,12],[10],1488⟩,⟨317,(0),[8,12],[10],1211⟩,⟨317,(1),[8,12],[10],1212⟩,⟨317,(2),[8,12],[10],1213⟩,⟨317,(3),[8,12],[10],1214⟩,⟨317,(4),[8,12],[10],1215⟩,⟨317,(5),[8,12],[10],1216⟩,⟨317,(6),[8,12],[10],1217⟩,⟨317,(7),[8,12],[10],1218⟩,⟨317,(8),[8,12],[10],1492⟩,⟨317,(9),[8,12],[10],1493⟩,⟨317,(10),[8,12],[10],1494⟩,⟨317,(11),[8,12],[10],1495⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2112
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2113
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2114
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2115
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2116
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2117
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2118
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2119
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2120
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2121
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2122
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2123
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2124
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2125
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2126
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2127
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2128
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2129
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2130
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2131
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2132
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2133
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2134
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2135
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2136
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2137
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2138
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2139
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2140
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2141
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2142
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2143
end Section14Records_12_2112_2144

#print axioms solution
