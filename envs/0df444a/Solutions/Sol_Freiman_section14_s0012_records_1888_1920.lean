-- Prove2me | solution 1 for Freiman.section14_s0012_records_1888_1920
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:14:04.719674+00:00
-- url     : https://prove2.me/submissions/1471e5bf-cef2-4513-b2f4-a3f565233f71

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
namespace Section14Records_12_1888_1920
private theorem valid1888 : RecordDataValid section14Catalog 12 (⟨283,(0),[8,12],[10],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1889 : RecordDataValid section14Catalog 12 (⟨283,(1),[8,12],[10],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1890 : RecordDataValid section14Catalog 12 (⟨283,(2),[8,12],[10],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1891 : RecordDataValid section14Catalog 12 (⟨283,(3),[8,12],[10],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1892 : RecordDataValid section14Catalog 12 (⟨283,(4),[8,12],[10],1123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1123,[3,5,7,8,9,11,12,15],1127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1893 : RecordDataValid section14Catalog 12 (⟨283,(5),[8,12],[10],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1894 : RecordDataValid section14Catalog 12 (⟨283,(6),[8,12],[10],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1895 : RecordDataValid section14Catalog 12 (⟨283,(7),[8,12],[10],1124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1124,[3,5,7,8,9,11,12,15],1128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1896 : RecordDataValid section14Catalog 12 (⟨283,(8),[8,12],[10],1125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1125,[3,5,7,8,9,11,12,15],1129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1897 : RecordDataValid section14Catalog 12 (⟨283,(9),[8,12],[10],1126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1126,[3,5,7,8,9,11,12,15],1130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1898 : RecordDataValid section14Catalog 12 (⟨285,(0),[8,12],[10],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1899 : RecordDataValid section14Catalog 12 (⟨285,(1),[8,12],[10],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1900 : RecordDataValid section14Catalog 12 (⟨285,(2),[8,12],[10],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1901 : RecordDataValid section14Catalog 12 (⟨285,(3),[8,12],[10],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1902 : RecordDataValid section14Catalog 12 (⟨285,(4),[8,12],[10],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1903 : RecordDataValid section14Catalog 12 (⟨285,(5),[8,12],[10],1434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1434,[5,8,9,12],1439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1904 : RecordDataValid section14Catalog 12 (⟨285,(6),[8,12],[10],1434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1434,[5,8,9,12],1439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1905 : RecordDataValid section14Catalog 12 (⟨285,(7),[8,12],[10],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1906 : RecordDataValid section14Catalog 12 (⟨285,(8),[8,12],[10],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1907 : RecordDataValid section14Catalog 12 (⟨285,(9),[8,12],[10],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1908 : RecordDataValid section14Catalog 12 (⟨285,(10),[8,12],[10],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1909 : RecordDataValid section14Catalog 12 (⟨285,(11),[8,12],[10],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1910 : RecordDataValid section14Catalog 12 (⟨285,(12),[8,12],[10],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1911 : RecordDataValid section14Catalog 12 (⟨285,(13),[8,12],[10],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1912 : RecordDataValid section14Catalog 12 (⟨285,(14),[8,12],[10],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1913 : RecordDataValid section14Catalog 12 (⟨285,(15),[8,12],[10],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1914 : RecordDataValid section14Catalog 12 (⟨285,(16),[8,12],[10],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1915 : RecordDataValid section14Catalog 12 (⟨285,(17),[8,12],[10],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1916 : RecordDataValid section14Catalog 12 (⟨285,(18),[8,12],[10],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1917 : RecordDataValid section14Catalog 12 (⟨285,(19),[8,12],[10],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1918 : RecordDataValid section14Catalog 12 (⟨285,(20),[8,12],[10],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1919 : RecordDataValid section14Catalog 12 (⟨285,(21),[8,12],[10],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1888).take 32 = [⟨283,(0),[8,12],[10],1120⟩,⟨283,(1),[8,12],[10],1121⟩,⟨283,(2),[8,12],[10],1122⟩,⟨283,(3),[8,12],[10],1122⟩,⟨283,(4),[8,12],[10],1123⟩,⟨283,(5),[8,12],[10],1120⟩,⟨283,(6),[8,12],[10],1121⟩,⟨283,(7),[8,12],[10],1124⟩,⟨283,(8),[8,12],[10],1125⟩,⟨283,(9),[8,12],[10],1126⟩,⟨285,(0),[8,12],[10],1430⟩,⟨285,(1),[8,12],[10],1430⟩,⟨285,(2),[8,12],[10],1431⟩,⟨285,(3),[8,12],[10],1432⟩,⟨285,(4),[8,12],[10],1433⟩,⟨285,(5),[8,12],[10],1434⟩,⟨285,(6),[8,12],[10],1434⟩,⟨285,(7),[8,12],[10],1431⟩,⟨285,(8),[8,12],[10],1432⟩,⟨285,(9),[8,12],[10],1433⟩,⟨285,(10),[8,12],[10],1430⟩,⟨285,(11),[8,12],[10],1430⟩,⟨285,(12),[8,12],[10],1431⟩,⟨285,(13),[8,12],[10],1432⟩,⟨285,(14),[8,12],[10],1433⟩,⟨285,(15),[8,12],[10],1435⟩,⟨285,(16),[8,12],[10],1435⟩,⟨285,(17),[8,12],[10],1431⟩,⟨285,(18),[8,12],[10],1432⟩,⟨285,(19),[8,12],[10],1433⟩,⟨285,(20),[8,12],[10],1436⟩,⟨285,(21),[8,12],[10],1436⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1888
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1889
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1890
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1891
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1892
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1893
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1894
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1895
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1896
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1897
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1898
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1899
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1900
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1901
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1902
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1903
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1904
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1905
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1906
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1907
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1908
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1909
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1910
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1911
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1912
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1913
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1914
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1915
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1916
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1917
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1918
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1919
end Section14Records_12_1888_1920

#print axioms solution
