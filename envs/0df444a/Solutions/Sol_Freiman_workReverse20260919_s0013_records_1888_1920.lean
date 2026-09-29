-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_1888_1920
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:18:10.639136+00:00
-- url     : https://prove2.me/submissions/2115eb4b-6c8b-4079-b121-8d32aff06652

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
namespace Section14Records_13_1888_1920
private theorem valid1888 : RecordDataValid section14Catalog 13 (⟨142,(11),[1,5,6,13],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1889 : RecordDataValid section14Catalog 13 (⟨142,(12),[1,5,6,13],[170],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1890 : RecordDataValid section14Catalog 13 (⟨142,(13),[1,5,6,13],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1891 : RecordDataValid section14Catalog 13 (⟨142,(14),[1,5,6,13],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1892 : RecordDataValid section14Catalog 13 (⟨142,(15),[1,5,6,13],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1893 : RecordDataValid section14Catalog 13 (⟨143,(0),[1,5,6,13],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1894 : RecordDataValid section14Catalog 13 (⟨143,(1),[1,5,6,13],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1895 : RecordDataValid section14Catalog 13 (⟨143,(2),[1,5,6,13],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1896 : RecordDataValid section14Catalog 13 (⟨143,(3),[1,5,6,13],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1897 : RecordDataValid section14Catalog 13 (⟨143,(4),[1,5,6,13],[170],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1898 : RecordDataValid section14Catalog 13 (⟨143,(5),[1,5,6,13],[170],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1899 : RecordDataValid section14Catalog 13 (⟨143,(6),[1,5,6,13],[170],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1900 : RecordDataValid section14Catalog 13 (⟨143,(7),[1,5,6,13],[170],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1901 : RecordDataValid section14Catalog 13 (⟨143,(8),[1,5,6,13],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1902 : RecordDataValid section14Catalog 13 (⟨143,(9),[1,5,6,13],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1903 : RecordDataValid section14Catalog 13 (⟨143,(10),[1,5,6,13],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1904 : RecordDataValid section14Catalog 13 (⟨143,(11),[1,5,6,13],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1905 : RecordDataValid section14Catalog 13 (⟨143,(12),[1,5,6,13],[170],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1906 : RecordDataValid section14Catalog 13 (⟨143,(13),[1,5,6,13],[170],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1907 : RecordDataValid section14Catalog 13 (⟨143,(14),[1,5,6,13],[170],588⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1908 : RecordDataValid section14Catalog 13 (⟨143,(15),[1,5,6,13],[170],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1909 : RecordDataValid section14Catalog 13 (⟨144,(0),[1,5,6,13],[170],590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨590,[1,4,5,6,8,9,10,12,13,16],591⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1910 : RecordDataValid section14Catalog 13 (⟨144,(1),[1,5,6,13],[170],591⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨591,[1,4,5,6,8,9,10,12,13,16],592⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1911 : RecordDataValid section14Catalog 13 (⟨144,(2),[1,5,6,13],[170],590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨590,[1,4,5,6,8,9,10,12,13,16],591⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1912 : RecordDataValid section14Catalog 13 (⟨144,(3),[1,5,6,13],[170],592⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨592,[1,4,5,6,8,9,10,12,13,16],593⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1913 : RecordDataValid section14Catalog 13 (⟨145,(0),[1,5,6,13],[170],593⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨593,[1,4,5,6,8,9,10,12,13,16],594⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1914 : RecordDataValid section14Catalog 13 (⟨145,(1),[1,5,6,13],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1915 : RecordDataValid section14Catalog 13 (⟨145,(2),[1,5,6,13],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1916 : RecordDataValid section14Catalog 13 (⟨145,(3),[1,5,6,13],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1917 : RecordDataValid section14Catalog 13 (⟨145,(4),[1,5,6,13],[170],597⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨597,[1,4,5,6,8,9,10,12,13,16],598⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1918 : RecordDataValid section14Catalog 13 (⟨145,(5),[1,5,6,13],[170],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1919 : RecordDataValid section14Catalog 13 (⟨145,(6),[1,5,6,13],[170],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1888).take 32 = [⟨142,(11),[1,5,6,13],[170],575⟩,⟨142,(12),[1,5,6,13],[170],576⟩,⟨142,(13),[1,5,6,13],[170],577⟩,⟨142,(14),[1,5,6,13],[170],577⟩,⟨142,(15),[1,5,6,13],[170],577⟩,⟨143,(0),[1,5,6,13],[170],578⟩,⟨143,(1),[1,5,6,13],[170],579⟩,⟨143,(2),[1,5,6,13],[170],580⟩,⟨143,(3),[1,5,6,13],[170],581⟩,⟨143,(4),[1,5,6,13],[170],582⟩,⟨143,(5),[1,5,6,13],[170],583⟩,⟨143,(6),[1,5,6,13],[170],584⟩,⟨143,(7),[1,5,6,13],[170],585⟩,⟨143,(8),[1,5,6,13],[170],578⟩,⟨143,(9),[1,5,6,13],[170],579⟩,⟨143,(10),[1,5,6,13],[170],580⟩,⟨143,(11),[1,5,6,13],[170],581⟩,⟨143,(12),[1,5,6,13],[170],586⟩,⟨143,(13),[1,5,6,13],[170],587⟩,⟨143,(14),[1,5,6,13],[170],588⟩,⟨143,(15),[1,5,6,13],[170],589⟩,⟨144,(0),[1,5,6,13],[170],590⟩,⟨144,(1),[1,5,6,13],[170],591⟩,⟨144,(2),[1,5,6,13],[170],590⟩,⟨144,(3),[1,5,6,13],[170],592⟩,⟨145,(0),[1,5,6,13],[170],593⟩,⟨145,(1),[1,5,6,13],[170],594⟩,⟨145,(2),[1,5,6,13],[170],595⟩,⟨145,(3),[1,5,6,13],[170],596⟩,⟨145,(4),[1,5,6,13],[170],597⟩,⟨145,(5),[1,5,6,13],[170],598⟩,⟨145,(6),[1,5,6,13],[170],599⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1888
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1889
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1890
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1891
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1892
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1893
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1894
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1895
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1896
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1897
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1898
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1899
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1900
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1901
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1902
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1903
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1904
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1905
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1906
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1907
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1908
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1909
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1910
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1911
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1912
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1913
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1914
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1915
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1916
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1917
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1918
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1919
end Section14Records_13_1888_1920

#print axioms solution
