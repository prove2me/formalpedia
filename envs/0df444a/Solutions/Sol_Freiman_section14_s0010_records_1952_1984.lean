-- Prove2me | solution 1 for Freiman.section14_s0010_records_1952_1984
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:24:06.558986+00:00
-- url     : https://prove2.me/submissions/fc326790-f8b9-408b-96d5-9aed15a55633

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
namespace Section14Records_10_1952_1984
private theorem valid1952 : RecordDataValid section14Catalog 10 (⟨213,(6),[10],[42],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1953 : RecordDataValid section14Catalog 10 (⟨213,(7),[10],[42],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1954 : RecordDataValid section14Catalog 10 (⟨213,(8),[10],[42],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1955 : RecordDataValid section14Catalog 10 (⟨213,(9),[10],[42],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1956 : RecordDataValid section14Catalog 10 (⟨213,(10),[10],[42],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1957 : RecordDataValid section14Catalog 10 (⟨213,(11),[10],[42],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1958 : RecordDataValid section14Catalog 10 (⟨213,(12),[10],[42],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1959 : RecordDataValid section14Catalog 10 (⟨213,(13),[10],[42],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1960 : RecordDataValid section14Catalog 10 (⟨213,(14),[10],[42],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1961 : RecordDataValid section14Catalog 10 (⟨213,(15),[10],[42],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1962 : RecordDataValid section14Catalog 10 (⟨215,(0),[9,10],[42],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1963 : RecordDataValid section14Catalog 10 (⟨215,(1),[9,10],[42],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1964 : RecordDataValid section14Catalog 10 (⟨215,(2),[9,10],[42],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1965 : RecordDataValid section14Catalog 10 (⟨215,(3),[9,10],[42],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1966 : RecordDataValid section14Catalog 10 (⟨215,(4),[9,10],[42],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1967 : RecordDataValid section14Catalog 10 (⟨215,(5),[9,10],[42],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1968 : RecordDataValid section14Catalog 10 (⟨215,(6),[9,10],[42],732⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨732,[1,2,4,5,6,8,9,10,12],733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1969 : RecordDataValid section14Catalog 10 (⟨215,(7),[9,10],[42],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1970 : RecordDataValid section14Catalog 10 (⟨215,(8),[9,10],[42],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1971 : RecordDataValid section14Catalog 10 (⟨215,(9),[9,10],[42],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1972 : RecordDataValid section14Catalog 10 (⟨215,(10),[9,10],[42],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1973 : RecordDataValid section14Catalog 10 (⟨215,(11),[9,10],[42],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1974 : RecordDataValid section14Catalog 10 (⟨215,(12),[9,10],[42],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1975 : RecordDataValid section14Catalog 10 (⟨215,(13),[9,10],[42],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1976 : RecordDataValid section14Catalog 10 (⟨215,(14),[9,10],[42],733⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨733,[1,2,4,5,6,8,9,10,12],734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1977 : RecordDataValid section14Catalog 10 (⟨215,(15),[9,10],[42],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1978 : RecordDataValid section14Catalog 10 (⟨218,(0),[10],[42],506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨506,[1,2,3,4,5,6,7,8,9,10,11,12],507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1979 : RecordDataValid section14Catalog 10 (⟨218,(1),[10],[42],507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨507,[1,2,3,4,5,6,7,8,9,10,11,12],508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1980 : RecordDataValid section14Catalog 10 (⟨218,(2),[10],[42],508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨508,[1,2,3,4,5,6,7,8,9,10,11,12],509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1981 : RecordDataValid section14Catalog 10 (⟨218,(3),[10],[42],509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨509,[1,2,3,4,5,6,7,8,9,10,11,12],510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1982 : RecordDataValid section14Catalog 10 (⟨220,(0),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1983 : RecordDataValid section14Catalog 10 (⟨220,(1),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1952).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1952).take 32 = [⟨213,(6),[10],[42],497⟩,⟨213,(7),[10],[42],497⟩,⟨213,(8),[10],[42],498⟩,⟨213,(9),[10],[42],498⟩,⟨213,(10),[10],[42],498⟩,⟨213,(11),[10],[42],498⟩,⟨213,(12),[10],[42],499⟩,⟨213,(13),[10],[42],499⟩,⟨213,(14),[10],[42],499⟩,⟨213,(15),[10],[42],499⟩,⟨215,(0),[9,10],[42],728⟩,⟨215,(1),[9,10],[42],729⟩,⟨215,(2),[9,10],[42],730⟩,⟨215,(3),[9,10],[42],731⟩,⟨215,(4),[9,10],[42],728⟩,⟨215,(5),[9,10],[42],729⟩,⟨215,(6),[9,10],[42],732⟩,⟨215,(7),[9,10],[42],731⟩,⟨215,(8),[9,10],[42],728⟩,⟨215,(9),[9,10],[42],729⟩,⟨215,(10),[9,10],[42],730⟩,⟨215,(11),[9,10],[42],731⟩,⟨215,(12),[9,10],[42],728⟩,⟨215,(13),[9,10],[42],729⟩,⟨215,(14),[9,10],[42],733⟩,⟨215,(15),[9,10],[42],731⟩,⟨218,(0),[10],[42],506⟩,⟨218,(1),[10],[42],507⟩,⟨218,(2),[10],[42],508⟩,⟨218,(3),[10],[42],509⟩,⟨220,(0),[9,10],[42],3⟩,⟨220,(1),[9,10],[42],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1952
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1953
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1954
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1955
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1956
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1957
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1958
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1959
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1960
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1961
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1962
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1963
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1964
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1965
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1966
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1967
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1968
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1969
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1970
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1971
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1972
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1973
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1974
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1975
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1976
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1977
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1978
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1979
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1980
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1981
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1982
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1983
end Section14Records_10_1952_1984

#print axioms solution
