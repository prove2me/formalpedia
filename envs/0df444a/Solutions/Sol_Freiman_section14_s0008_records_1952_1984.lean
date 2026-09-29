-- Prove2me | solution 1 for Freiman.section14_s0008_records_1952_1984
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:46:01.620818+00:00
-- url     : https://prove2.me/submissions/39804b21-215a-4965-a3c5-fa72cd717b00

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
namespace Section14Records_8_1952_1984
private theorem valid1952 : RecordDataValid section14Catalog 8 (⟨255,(13),[4,8],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1953 : RecordDataValid section14Catalog 8 (⟨255,(14),[4,8],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1954 : RecordDataValid section14Catalog 8 (⟨255,(15),[4,8],[10],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1955 : RecordDataValid section14Catalog 8 (⟨255,(16),[4,8],[10],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1956 : RecordDataValid section14Catalog 8 (⟨255,(17),[4,8],[10],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1957 : RecordDataValid section14Catalog 8 (⟨255,(18),[4,8],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1958 : RecordDataValid section14Catalog 8 (⟨255,(19),[4,8],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1959 : RecordDataValid section14Catalog 8 (⟨255,(20),[4,8],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1960 : RecordDataValid section14Catalog 8 (⟨255,(21),[4,8],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1961 : RecordDataValid section14Catalog 8 (⟨255,(22),[4,8],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1962 : RecordDataValid section14Catalog 8 (⟨255,(23),[4,8],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1963 : RecordDataValid section14Catalog 8 (⟨255,(24),[4,8],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1964 : RecordDataValid section14Catalog 8 (⟨259,(1),[4,8,12],[10],906⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨906,[1,2,4,5,6,8,9,10,12],908⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1965 : RecordDataValid section14Catalog 8 (⟨259,(3),[4,8,12],[10],907⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨907,[1,2,4,5,6,8,9,10,12],909⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1966 : RecordDataValid section14Catalog 8 (⟨259,(5),[8,12],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1967 : RecordDataValid section14Catalog 8 (⟨259,(7),[8,12],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1968 : RecordDataValid section14Catalog 8 (⟨259,(11),[8],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1969 : RecordDataValid section14Catalog 8 (⟨259,(13),[8,12],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1970 : RecordDataValid section14Catalog 8 (⟨259,(15),[4,8],[10],53⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨53,[1,4,6,8,9,10],53⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1971 : RecordDataValid section14Catalog 8 (⟨259,(17),[8],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1972 : RecordDataValid section14Catalog 8 (⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1973 : RecordDataValid section14Catalog 8 (⟨260,(-1),[4,8,10,12,16],[8,12],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1974 : RecordDataValid section14Catalog 8 (⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1975 : RecordDataValid section14Catalog 8 (⟨260,(-1),[4,8,12,16],[2],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1976 : RecordDataValid section14Catalog 8 (⟨260,(-1),[4,8,12,16],[7,11,15],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1977 : RecordDataValid section14Catalog 8 (⟨260,(-1),[4,8,12,16],[6],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1978 : RecordDataValid section14Catalog 8 (⟨260,(-1),[4,8,12,16],[14],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1979 : RecordDataValid section14Catalog 8 (⟨260,(-1),[8,12],[3],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1980 : RecordDataValid section14Catalog 8 (⟨264,(0),[8],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1981 : RecordDataValid section14Catalog 8 (⟨264,(1),[8],[10],1408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1408,[5,8],1413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1982 : RecordDataValid section14Catalog 8 (⟨264,(2),[8],[10],1407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1407,[5,8],1412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1983 : RecordDataValid section14Catalog 8 (⟨264,(3),[8],[10],1409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1409,[5,8],1414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1952).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1952).take 32 = [⟨255,(13),[4,8],[10],901⟩,⟨255,(14),[4,8],[10],902⟩,⟨255,(15),[4,8],[10],904⟩,⟨255,(16),[4,8],[10],904⟩,⟨255,(17),[4,8],[10],900⟩,⟨255,(18),[4,8],[10],901⟩,⟨255,(19),[4,8],[10],902⟩,⟨255,(20),[4,8],[10],905⟩,⟨255,(21),[4,8],[10],905⟩,⟨255,(22),[4,8],[10],905⟩,⟨255,(23),[4,8],[10],901⟩,⟨255,(24),[4,8],[10],902⟩,⟨259,(1),[4,8,12],[10],906⟩,⟨259,(3),[4,8,12],[10],907⟩,⟨259,(5),[8,12],[10],143⟩,⟨259,(7),[8,12],[10],143⟩,⟨259,(11),[8],[10],143⟩,⟨259,(13),[8,12],[10],143⟩,⟨259,(15),[4,8],[10],53⟩,⟨259,(17),[8],[10],143⟩,⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩,⟨260,(-1),[4,8,10,12,16],[8,12],882⟩,⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩,⟨260,(-1),[4,8,12,16],[2],884⟩,⟨260,(-1),[4,8,12,16],[7,11,15],886⟩,⟨260,(-1),[4,8,12,16],[6],887⟩,⟨260,(-1),[4,8,12,16],[14],909⟩,⟨260,(-1),[8,12],[3],886⟩,⟨264,(0),[8],[10],10⟩,⟨264,(1),[8],[10],1408⟩,⟨264,(2),[8],[10],1407⟩,⟨264,(3),[8],[10],1409⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1952
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1953
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1954
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1955
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1956
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1957
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1958
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1959
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1960
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1961
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1962
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1963
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1964
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1965
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1966
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1967
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1968
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1969
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1970
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1971
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1972
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1973
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1974
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1975
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1976
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1977
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1978
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1979
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1980
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1981
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1982
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1983
end Section14Records_8_1952_1984

#print axioms solution
