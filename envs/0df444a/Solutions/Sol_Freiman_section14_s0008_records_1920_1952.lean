-- Prove2me | solution 1 for Freiman.section14_s0008_records_1920_1952
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:44:40.051076+00:00
-- url     : https://prove2.me/submissions/4e38d778-1a53-4050-8cfc-cdb210470cba

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
namespace Section14Records_8_1920_1952
private theorem valid1920 : RecordDataValid section14Catalog 8 (⟨253,(6),[4,8,16],[10],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1921 : RecordDataValid section14Catalog 8 (⟨253,(7),[8,12],[10],1647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1647,[8,9,12],1652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1922 : RecordDataValid section14Catalog 8 (⟨253,(8),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1923 : RecordDataValid section14Catalog 8 (⟨253,(9),[4,8,12,16],[10],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1924 : RecordDataValid section14Catalog 8 (⟨253,(10),[4,8,12,16],[10],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1925 : RecordDataValid section14Catalog 8 (⟨253,(11),[4,8,12,16],[10],897⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨897,[1,2,4,5,6,8,9,10,12,13,14,16],899⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1926 : RecordDataValid section14Catalog 8 (⟨253,(12),[4,8,12,16],[10],898⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨898,[1,2,4,5,6,8,9,10,12,13,14,16],900⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1927 : RecordDataValid section14Catalog 8 (⟨253,(13),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1928 : RecordDataValid section14Catalog 8 (⟨253,(14),[4,8,12,16],[10],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1929 : RecordDataValid section14Catalog 8 (⟨253,(15),[4,8,12,16],[10],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1930 : RecordDataValid section14Catalog 8 (⟨253,(16),[4,8,12,16],[10],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1931 : RecordDataValid section14Catalog 8 (⟨253,(17),[4,8,12,16],[10],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1932 : RecordDataValid section14Catalog 8 (⟨253,(18),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1933 : RecordDataValid section14Catalog 8 (⟨253,(19),[4,8,12,16],[10],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1934 : RecordDataValid section14Catalog 8 (⟨253,(20),[4,8,12,16],[10],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1935 : RecordDataValid section14Catalog 8 (⟨253,(21),[4,8,12,16],[10],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1936 : RecordDataValid section14Catalog 8 (⟨253,(22),[4,8,12,16],[10],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1937 : RecordDataValid section14Catalog 8 (⟨253,(23),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1938 : RecordDataValid section14Catalog 8 (⟨253,(24),[4,8,12,16],[10],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1939 : RecordDataValid section14Catalog 8 (⟨255,(0),[4,8],[10],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1940 : RecordDataValid section14Catalog 8 (⟨255,(1),[4,8],[10],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1941 : RecordDataValid section14Catalog 8 (⟨255,(2),[4,8],[10],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1942 : RecordDataValid section14Catalog 8 (⟨255,(3),[4,8],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1943 : RecordDataValid section14Catalog 8 (⟨255,(4),[4,8],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1944 : RecordDataValid section14Catalog 8 (⟨255,(5),[4,8],[10],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1945 : RecordDataValid section14Catalog 8 (⟨255,(6),[4,8],[10],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1946 : RecordDataValid section14Catalog 8 (⟨255,(7),[4,8],[10],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1947 : RecordDataValid section14Catalog 8 (⟨255,(8),[4,8],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1948 : RecordDataValid section14Catalog 8 (⟨255,(9),[4,8],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1949 : RecordDataValid section14Catalog 8 (⟨255,(10),[4,8],[10],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1950 : RecordDataValid section14Catalog 8 (⟨255,(11),[4,8],[10],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1951 : RecordDataValid section14Catalog 8 (⟨255,(12),[4,8],[10],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1920).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1920).take 32 = [⟨253,(6),[4,8,16],[10],894⟩,⟨253,(7),[8,12],[10],1647⟩,⟨253,(8),[4,8,12,16],[10],29⟩,⟨253,(9),[4,8,12,16],[10],32⟩,⟨253,(10),[4,8,12,16],[10],84⟩,⟨253,(11),[4,8,12,16],[10],897⟩,⟨253,(12),[4,8,12,16],[10],898⟩,⟨253,(13),[4,8,12,16],[10],29⟩,⟨253,(14),[4,8,12,16],[10],34⟩,⟨253,(15),[4,8,12,16],[10],35⟩,⟨253,(16),[4,8,12,16],[10],36⟩,⟨253,(17),[4,8,12,16],[10],37⟩,⟨253,(18),[4,8,12,16],[10],29⟩,⟨253,(19),[4,8,12,16],[10],37⟩,⟨253,(20),[4,8,12,16],[10],38⟩,⟨253,(21),[4,8,12,16],[10],39⟩,⟨253,(22),[4,8,12,16],[10],40⟩,⟨253,(23),[4,8,12,16],[10],29⟩,⟨253,(24),[4,8,12,16],[10],40⟩,⟨255,(0),[4,8],[10],899⟩,⟨255,(1),[4,8],[10],899⟩,⟨255,(2),[4,8],[10],900⟩,⟨255,(3),[4,8],[10],901⟩,⟨255,(4),[4,8],[10],902⟩,⟨255,(5),[4,8],[10],903⟩,⟨255,(6),[4,8],[10],903⟩,⟨255,(7),[4,8],[10],900⟩,⟨255,(8),[4,8],[10],901⟩,⟨255,(9),[4,8],[10],902⟩,⟨255,(10),[4,8],[10],899⟩,⟨255,(11),[4,8],[10],899⟩,⟨255,(12),[4,8],[10],900⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1920
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1921
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1922
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1923
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1924
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1925
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1926
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1927
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1928
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1929
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1930
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1931
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1932
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1933
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1934
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1935
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1936
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1937
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1938
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1939
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1940
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1941
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1942
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1943
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1944
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1945
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1946
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1947
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1948
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1949
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1950
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1951
end Section14Records_8_1920_1952

#print axioms solution
