-- Prove2me | solution 1 for Freiman.section14_s0012_records_1952_1984
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:15:37.996252+00:00
-- url     : https://prove2.me/submissions/53b8f2a3-66e3-4104-84ff-463bded5f1a7

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
namespace Section14Records_12_1952_1984
private theorem valid1952 : RecordDataValid section14Catalog 12 (⟨290,(4),[8,12],[10],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1953 : RecordDataValid section14Catalog 12 (⟨290,(5),[8,12],[10],1441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1441,[5,8,9,12],1446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1954 : RecordDataValid section14Catalog 12 (⟨290,(6),[8,12],[10],1441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1441,[5,8,9,12],1446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1955 : RecordDataValid section14Catalog 12 (⟨290,(7),[8,12],[10],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1956 : RecordDataValid section14Catalog 12 (⟨290,(8),[8,12],[10],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1957 : RecordDataValid section14Catalog 12 (⟨290,(9),[8,12],[10],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1958 : RecordDataValid section14Catalog 12 (⟨290,(10),[8,12],[10],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1959 : RecordDataValid section14Catalog 12 (⟨290,(11),[8,12],[10],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1960 : RecordDataValid section14Catalog 12 (⟨290,(12),[8,12],[10],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1961 : RecordDataValid section14Catalog 12 (⟨290,(13),[8,12],[10],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1962 : RecordDataValid section14Catalog 12 (⟨290,(14),[8,12],[10],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1963 : RecordDataValid section14Catalog 12 (⟨290,(15),[8,12],[10],1442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1442,[5,8,9,12],1447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1964 : RecordDataValid section14Catalog 12 (⟨290,(16),[8,12],[10],1442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1442,[5,8,9,12],1447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1965 : RecordDataValid section14Catalog 12 (⟨290,(17),[8,12],[10],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1966 : RecordDataValid section14Catalog 12 (⟨290,(18),[8,12],[10],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1967 : RecordDataValid section14Catalog 12 (⟨290,(19),[8,12],[10],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1968 : RecordDataValid section14Catalog 12 (⟨290,(20),[8,12],[10],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1969 : RecordDataValid section14Catalog 12 (⟨290,(21),[8,12],[10],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1970 : RecordDataValid section14Catalog 12 (⟨290,(22),[8,12],[10],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1971 : RecordDataValid section14Catalog 12 (⟨290,(23),[8,12],[10],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1972 : RecordDataValid section14Catalog 12 (⟨290,(24),[8,12],[10],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1973 : RecordDataValid section14Catalog 12 (⟨293,(0),[8,12],[10],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1974 : RecordDataValid section14Catalog 12 (⟨293,(1),[8,12],[10],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1975 : RecordDataValid section14Catalog 12 (⟨293,(2),[8,12],[10],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1976 : RecordDataValid section14Catalog 12 (⟨293,(3),[8,12],[10],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1977 : RecordDataValid section14Catalog 12 (⟨293,(4),[8,12],[10],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1978 : RecordDataValid section14Catalog 12 (⟨293,(5),[8,12],[10],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1979 : RecordDataValid section14Catalog 12 (⟨293,(6),[8,12],[10],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1980 : RecordDataValid section14Catalog 12 (⟨293,(7),[8,12],[10],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1981 : RecordDataValid section14Catalog 12 (⟨293,(8),[8,12],[10],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1982 : RecordDataValid section14Catalog 12 (⟨293,(9),[8,12],[10],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1983 : RecordDataValid section14Catalog 12 (⟨293,(10),[8,12],[10],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1952).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1952).take 32 = [⟨290,(4),[8,12],[10],1440⟩,⟨290,(5),[8,12],[10],1441⟩,⟨290,(6),[8,12],[10],1441⟩,⟨290,(7),[8,12],[10],1438⟩,⟨290,(8),[8,12],[10],1439⟩,⟨290,(9),[8,12],[10],1440⟩,⟨290,(10),[8,12],[10],1437⟩,⟨290,(11),[8,12],[10],1437⟩,⟨290,(12),[8,12],[10],1438⟩,⟨290,(13),[8,12],[10],1439⟩,⟨290,(14),[8,12],[10],1440⟩,⟨290,(15),[8,12],[10],1442⟩,⟨290,(16),[8,12],[10],1442⟩,⟨290,(17),[8,12],[10],1438⟩,⟨290,(18),[8,12],[10],1439⟩,⟨290,(19),[8,12],[10],1440⟩,⟨290,(20),[8,12],[10],1443⟩,⟨290,(21),[8,12],[10],1443⟩,⟨290,(22),[8,12],[10],1443⟩,⟨290,(23),[8,12],[10],1439⟩,⟨290,(24),[8,12],[10],1440⟩,⟨293,(0),[8,12],[10],1152⟩,⟨293,(1),[8,12],[10],1153⟩,⟨293,(2),[8,12],[10],1154⟩,⟨293,(3),[8,12],[10],1154⟩,⟨293,(4),[8,12],[10],1154⟩,⟨293,(5),[8,12],[10],1152⟩,⟨293,(6),[8,12],[10],1153⟩,⟨293,(7),[8,12],[10],1155⟩,⟨293,(8),[8,12],[10],1156⟩,⟨293,(9),[8,12],[10],1155⟩,⟨293,(10),[8,12],[10],1152⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1952
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1953
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1954
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1955
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1956
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1957
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1958
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1959
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1960
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1961
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1962
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1963
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1964
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1965
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1966
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1967
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1968
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1969
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1970
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1971
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1972
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1973
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1974
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1975
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1976
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1977
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1978
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1979
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1980
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1981
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1982
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1983
end Section14Records_12_1952_1984

#print axioms solution
