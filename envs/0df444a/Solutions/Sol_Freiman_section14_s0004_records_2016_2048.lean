-- Prove2me | solution 1 for Freiman.section14_s0004_records_2016_2048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T03:02:35.82905+00:00
-- url     : https://prove2.me/submissions/5ec34ab0-52ed-46e5-a474-37cc2e527e35

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
namespace Section14Records_4_2016_2048
private theorem valid2016 : RecordDataValid section14Catalog 4 (⟨255,(18),[4,8],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2017 : RecordDataValid section14Catalog 4 (⟨255,(19),[4,8],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2018 : RecordDataValid section14Catalog 4 (⟨255,(20),[4,8],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2019 : RecordDataValid section14Catalog 4 (⟨255,(21),[4,8],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2020 : RecordDataValid section14Catalog 4 (⟨255,(22),[4,8],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2021 : RecordDataValid section14Catalog 4 (⟨255,(23),[4,8],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2022 : RecordDataValid section14Catalog 4 (⟨255,(24),[4,8],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2023 : RecordDataValid section14Catalog 4 (⟨259,(1),[4,8,12],[10],906⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨906,[1,2,4,5,6,8,9,10,12],908⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2024 : RecordDataValid section14Catalog 4 (⟨259,(3),[4,8,12],[10],907⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨907,[1,2,4,5,6,8,9,10,12],909⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2025 : RecordDataValid section14Catalog 4 (⟨259,(5),[4],[10],51⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨51,[1,2,4,9,10],51⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2026 : RecordDataValid section14Catalog 4 (⟨259,(7),[4],[10],52⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨52,[1,2,4,9,12],52⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2027 : RecordDataValid section14Catalog 4 (⟨259,(11),[4,12],[10],52⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨52,[1,2,4,9,12],52⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2028 : RecordDataValid section14Catalog 4 (⟨259,(13),[4],[10],52⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨52,[1,2,4,9,12],52⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2029 : RecordDataValid section14Catalog 4 (⟨259,(15),[4,8],[10],53⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨53,[1,4,6,8,9,10],53⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2030 : RecordDataValid section14Catalog 4 (⟨259,(17),[4,12],[10],52⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨52,[1,2,4,9,12],52⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2031 : RecordDataValid section14Catalog 4 (⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2032 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,8,10,12,16],[8,12],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2033 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2034 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,8,12,16],[2],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2035 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,8,12,16],[7,11,15],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2036 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,8,12,16],[6],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2037 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,8,12,16],[14],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2038 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,16],[3],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2039 : RecordDataValid section14Catalog 4 (⟨260,(-1),[4,16],[10],911⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨911,[1,2,4,13,14,16],913⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2040 : RecordDataValid section14Catalog 4 (⟨478,(0),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2041 : RecordDataValid section14Catalog 4 (⟨478,(1),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2042 : RecordDataValid section14Catalog 4 (⟨478,(2),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2043 : RecordDataValid section14Catalog 4 (⟨478,(3),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2044 : RecordDataValid section14Catalog 4 (⟨478,(4),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2045 : RecordDataValid section14Catalog 4 (⟨478,(5),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2046 : RecordDataValid section14Catalog 4 (⟨478,(6),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2047 : RecordDataValid section14Catalog 4 (⟨478,(7),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 2016).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 2016).take 32 = [⟨255,(18),[4,8],[10],901⟩,⟨255,(19),[4,8],[10],902⟩,⟨255,(20),[4,8],[10],905⟩,⟨255,(21),[4,8],[10],905⟩,⟨255,(22),[4,8],[10],905⟩,⟨255,(23),[4,8],[10],901⟩,⟨255,(24),[4,8],[10],902⟩,⟨259,(1),[4,8,12],[10],906⟩,⟨259,(3),[4,8,12],[10],907⟩,⟨259,(5),[4],[10],51⟩,⟨259,(7),[4],[10],52⟩,⟨259,(11),[4,12],[10],52⟩,⟨259,(13),[4],[10],52⟩,⟨259,(15),[4,8],[10],53⟩,⟨259,(17),[4,12],[10],52⟩,⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩,⟨260,(-1),[4,8,10,12,16],[8,12],882⟩,⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩,⟨260,(-1),[4,8,12,16],[2],884⟩,⟨260,(-1),[4,8,12,16],[7,11,15],886⟩,⟨260,(-1),[4,8,12,16],[6],887⟩,⟨260,(-1),[4,8,12,16],[14],909⟩,⟨260,(-1),[4,16],[3],884⟩,⟨260,(-1),[4,16],[10],911⟩,⟨478,(0),[4,8,12,16],[10],3⟩,⟨478,(1),[4,8,12,16],[10],3⟩,⟨478,(2),[4,8,12,16],[10],3⟩,⟨478,(3),[4,8,12,16],[10],3⟩,⟨478,(4),[4,8,12,16],[10],3⟩,⟨478,(5),[4,8,12,16],[10],3⟩,⟨478,(6),[4,8,12,16],[10],3⟩,⟨478,(7),[4,8,12,16],[10],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2016
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2017
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2018
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2019
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2020
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2021
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2022
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2023
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2024
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2025
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2026
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2027
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2028
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2029
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2030
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2031
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2032
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2033
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2034
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2035
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2036
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2037
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2038
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2039
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2040
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2041
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2042
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2043
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2044
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2045
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2046
  · exact recordValid_of_data section14Catalog 4 _ hnum valid2047
end Section14Records_4_2016_2048

#print axioms solution
