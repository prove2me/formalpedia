-- Prove2me | solution 1 for Freiman.section14_s0012_records_2080_2112
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:21:08.155061+00:00
-- url     : https://prove2.me/submissions/c199ecb5-9208-4607-b49e-5bbdee7a8276

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
namespace Section14Records_12_2080_2112
private theorem valid2080 : RecordDataValid section14Catalog 12 (⟨307,(5),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2081 : RecordDataValid section14Catalog 12 (⟨307,(6),[8,12],[10],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2082 : RecordDataValid section14Catalog 12 (⟨307,(7),[8,12],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2083 : RecordDataValid section14Catalog 12 (⟨307,(8),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2084 : RecordDataValid section14Catalog 12 (⟨307,(9),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2085 : RecordDataValid section14Catalog 12 (⟨307,(10),[8,12],[10],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2086 : RecordDataValid section14Catalog 12 (⟨307,(11),[8,12],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2087 : RecordDataValid section14Catalog 12 (⟨307,(12),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2088 : RecordDataValid section14Catalog 12 (⟨307,(13),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2089 : RecordDataValid section14Catalog 12 (⟨307,(14),[8,12],[10],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2090 : RecordDataValid section14Catalog 12 (⟨307,(15),[8,12],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2091 : RecordDataValid section14Catalog 12 (⟨307,(16),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2092 : RecordDataValid section14Catalog 12 (⟨307,(17),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2093 : RecordDataValid section14Catalog 12 (⟨307,(18),[8,12],[10],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2094 : RecordDataValid section14Catalog 12 (⟨307,(19),[8,12],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2095 : RecordDataValid section14Catalog 12 (⟨308,(8),[8,12],[10],1474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1474,[5,8,9,12],1479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2096 : RecordDataValid section14Catalog 12 (⟨308,(9),[8,12],[10],1475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1475,[5,8,9,12],1480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2097 : RecordDataValid section14Catalog 12 (⟨308,(10),[8,12],[10],1474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1474,[5,8,9,12],1479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2098 : RecordDataValid section14Catalog 12 (⟨308,(11),[8,12],[10],1476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1476,[5,8,9,12],1481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2099 : RecordDataValid section14Catalog 12 (⟨309,(0),[8,12],[10],1188⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1188,[3,5,7,8,9,11,12,15],1192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2100 : RecordDataValid section14Catalog 12 (⟨309,(1),[8,12],[10],1189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1189,[3,5,7,8,9,11,12,15],1193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2101 : RecordDataValid section14Catalog 12 (⟨309,(2),[8,12],[10],1190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1190,[3,5,7,8,9,11,12,15],1194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2102 : RecordDataValid section14Catalog 12 (⟨309,(3),[8,12],[10],1191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1191,[3,5,7,8,9,11,12,15],1195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2103 : RecordDataValid section14Catalog 12 (⟨309,(4),[8,12],[10],1192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1192,[3,7,8,11,12,15],1196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2104 : RecordDataValid section14Catalog 12 (⟨311,(0),[8,12],[10],1478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1478,[5,8,9,12],1483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2105 : RecordDataValid section14Catalog 12 (⟨311,(1),[8,12],[10],1479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1479,[5,8,9,12],1484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2106 : RecordDataValid section14Catalog 12 (⟨311,(2),[8,12],[10],1480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1480,[5,8,9,12],1485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2107 : RecordDataValid section14Catalog 12 (⟨311,(3),[8,12],[10],1481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1481,[5,8,9,12],1486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2108 : RecordDataValid section14Catalog 12 (⟨312,(0),[8,12],[10],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2109 : RecordDataValid section14Catalog 12 (⟨312,(1),[8,12],[10],1483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1483,[5,8,9,12],1488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2110 : RecordDataValid section14Catalog 12 (⟨312,(2),[8,12],[10],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2111 : RecordDataValid section14Catalog 12 (⟨312,(3),[8,12],[10],1484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1484,[5,8,9,12],1489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2080).take 32 = [⟨307,(5),[8,12],[10],3⟩,⟨307,(6),[8,12],[10],1266⟩,⟨307,(7),[8,12],[10],29⟩,⟨307,(8),[8,12],[10],3⟩,⟨307,(9),[8,12],[10],3⟩,⟨307,(10),[8,12],[10],512⟩,⟨307,(11),[8,12],[10],29⟩,⟨307,(12),[8,12],[10],3⟩,⟨307,(13),[8,12],[10],3⟩,⟨307,(14),[8,12],[10],1266⟩,⟨307,(15),[8,12],[10],29⟩,⟨307,(16),[8,12],[10],3⟩,⟨307,(17),[8,12],[10],3⟩,⟨307,(18),[8,12],[10],514⟩,⟨307,(19),[8,12],[10],29⟩,⟨308,(8),[8,12],[10],1474⟩,⟨308,(9),[8,12],[10],1475⟩,⟨308,(10),[8,12],[10],1474⟩,⟨308,(11),[8,12],[10],1476⟩,⟨309,(0),[8,12],[10],1188⟩,⟨309,(1),[8,12],[10],1189⟩,⟨309,(2),[8,12],[10],1190⟩,⟨309,(3),[8,12],[10],1191⟩,⟨309,(4),[8,12],[10],1192⟩,⟨311,(0),[8,12],[10],1478⟩,⟨311,(1),[8,12],[10],1479⟩,⟨311,(2),[8,12],[10],1480⟩,⟨311,(3),[8,12],[10],1481⟩,⟨312,(0),[8,12],[10],1482⟩,⟨312,(1),[8,12],[10],1483⟩,⟨312,(2),[8,12],[10],1482⟩,⟨312,(3),[8,12],[10],1484⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2080
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2081
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2082
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2083
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2084
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2085
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2086
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2087
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2088
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2089
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2090
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2091
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2092
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2093
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2094
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2095
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2096
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2097
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2098
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2099
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2100
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2101
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2102
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2103
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2104
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2105
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2106
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2107
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2108
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2109
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2110
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2111
end Section14Records_12_2080_2112

#print axioms solution
