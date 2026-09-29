-- Prove2me | solution 1 for Freiman.section14_s0008_records_2016_2048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:48:07.987986+00:00
-- url     : https://prove2.me/submissions/3e20bf29-a8dd-4a4a-9404-526494e9061b

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
namespace Section14Records_8_2016_2048
private theorem valid2016 : RecordDataValid section14Catalog 8 (⟨267,(11),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2017 : RecordDataValid section14Catalog 8 (⟨267,(12),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2018 : RecordDataValid section14Catalog 8 (⟨267,(13),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2019 : RecordDataValid section14Catalog 8 (⟨267,(14),[8,12],[10],1091⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1091,[3,5,7,8,9,11,12,15],1095⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2020 : RecordDataValid section14Catalog 8 (⟨267,(15),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2021 : RecordDataValid section14Catalog 8 (⟨270,(0),[8,12],[10],1414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1414,[5,8,9,12],1419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2022 : RecordDataValid section14Catalog 8 (⟨270,(1),[8,12],[10],1415⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1415,[5,8,9,12],1420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2023 : RecordDataValid section14Catalog 8 (⟨270,(2),[8,12],[10],1414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1414,[5,8,9,12],1419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2024 : RecordDataValid section14Catalog 8 (⟨270,(3),[8,12],[10],1416⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1416,[5,8,9,12],1421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2025 : RecordDataValid section14Catalog 8 (⟨270,(4),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2026 : RecordDataValid section14Catalog 8 (⟨270,(5),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2027 : RecordDataValid section14Catalog 8 (⟨270,(6),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2028 : RecordDataValid section14Catalog 8 (⟨270,(7),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2029 : RecordDataValid section14Catalog 8 (⟨270,(8),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2030 : RecordDataValid section14Catalog 8 (⟨270,(9),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2031 : RecordDataValid section14Catalog 8 (⟨270,(10),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2032 : RecordDataValid section14Catalog 8 (⟨270,(11),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2033 : RecordDataValid section14Catalog 8 (⟨270,(12),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2034 : RecordDataValid section14Catalog 8 (⟨270,(13),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2035 : RecordDataValid section14Catalog 8 (⟨270,(14),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2036 : RecordDataValid section14Catalog 8 (⟨270,(15),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2037 : RecordDataValid section14Catalog 8 (⟨273,(0),[8,12],[10],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2038 : RecordDataValid section14Catalog 8 (⟨273,(1),[8,12],[10],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2039 : RecordDataValid section14Catalog 8 (⟨273,(2),[8,12],[10],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2040 : RecordDataValid section14Catalog 8 (⟨273,(3),[8,12],[10],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2041 : RecordDataValid section14Catalog 8 (⟨273,(4),[8,12],[10],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2042 : RecordDataValid section14Catalog 8 (⟨273,(5),[8,12],[10],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2043 : RecordDataValid section14Catalog 8 (⟨273,(6),[8,12],[10],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2044 : RecordDataValid section14Catalog 8 (⟨273,(7),[8,12],[10],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2045 : RecordDataValid section14Catalog 8 (⟨273,(8),[8,12],[10],1102⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1102,[3,5,7,8,9,11,12,15],1106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2046 : RecordDataValid section14Catalog 8 (⟨273,(9),[8,12],[10],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2047 : RecordDataValid section14Catalog 8 (⟨275,(0),[8,12],[10],1420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1420,[5,8,9,12],1425⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2016).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2016).take 32 = [⟨267,(11),[8,12],[10],1089⟩,⟨267,(12),[8,12],[10],1086⟩,⟨267,(13),[8,12],[10],1087⟩,⟨267,(14),[8,12],[10],1091⟩,⟨267,(15),[8,12],[10],1089⟩,⟨270,(0),[8,12],[10],1414⟩,⟨270,(1),[8,12],[10],1415⟩,⟨270,(2),[8,12],[10],1414⟩,⟨270,(3),[8,12],[10],1416⟩,⟨270,(4),[8,12],[10],1417⟩,⟨270,(5),[8,12],[10],1417⟩,⟨270,(6),[8,12],[10],1417⟩,⟨270,(7),[8,12],[10],1417⟩,⟨270,(8),[8,12],[10],1418⟩,⟨270,(9),[8,12],[10],1418⟩,⟨270,(10),[8,12],[10],1418⟩,⟨270,(11),[8,12],[10],1418⟩,⟨270,(12),[8,12],[10],1419⟩,⟨270,(13),[8,12],[10],1419⟩,⟨270,(14),[8,12],[10],1419⟩,⟨270,(15),[8,12],[10],1419⟩,⟨273,(0),[8,12],[10],1098⟩,⟨273,(1),[8,12],[10],1099⟩,⟨273,(2),[8,12],[10],1100⟩,⟨273,(3),[8,12],[10],1100⟩,⟨273,(4),[8,12],[10],1100⟩,⟨273,(5),[8,12],[10],1098⟩,⟨273,(6),[8,12],[10],1099⟩,⟨273,(7),[8,12],[10],1101⟩,⟨273,(8),[8,12],[10],1102⟩,⟨273,(9),[8,12],[10],1101⟩,⟨275,(0),[8,12],[10],1420⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2016
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2017
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2018
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2019
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2020
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2021
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2022
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2023
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2024
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2025
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2026
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2027
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2028
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2029
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2030
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2031
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2032
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2033
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2034
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2035
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2036
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2037
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2038
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2039
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2040
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2041
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2042
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2043
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2044
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2045
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2046
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2047
end Section14Records_8_2016_2048

#print axioms solution
