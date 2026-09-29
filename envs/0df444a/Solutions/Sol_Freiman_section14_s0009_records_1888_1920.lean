-- Prove2me | solution 1 for Freiman.section14_s0009_records_1888_1920
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:05:39.828834+00:00
-- url     : https://prove2.me/submissions/243392fa-253a-4cb0-9ea4-35dc6f83c70c

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
namespace Section14Records_9_1888_1920
private theorem valid1888 : RecordDataValid section14Catalog 9 (⟨202,(23),[9],[42],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1889 : RecordDataValid section14Catalog 9 (⟨202,(24),[9],[42],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1890 : RecordDataValid section14Catalog 9 (⟨205,(0),[9,10],[42],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1891 : RecordDataValid section14Catalog 9 (⟨205,(1),[9,10],[42],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1892 : RecordDataValid section14Catalog 9 (⟨205,(2),[9,10],[42],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1893 : RecordDataValid section14Catalog 9 (⟨205,(3),[9,10],[42],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1894 : RecordDataValid section14Catalog 9 (⟨205,(4),[9,10],[42],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1895 : RecordDataValid section14Catalog 9 (⟨205,(5),[9,10],[42],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1896 : RecordDataValid section14Catalog 9 (⟨205,(6),[9,10],[42],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1897 : RecordDataValid section14Catalog 9 (⟨205,(7),[9,10],[42],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1898 : RecordDataValid section14Catalog 9 (⟨205,(8),[9,10],[42],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1899 : RecordDataValid section14Catalog 9 (⟨205,(9),[9,10],[42],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1900 : RecordDataValid section14Catalog 9 (⟨205,(10),[9,10],[42],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1901 : RecordDataValid section14Catalog 9 (⟨205,(11),[9,10],[42],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1902 : RecordDataValid section14Catalog 9 (⟨205,(12),[9,10],[42],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1903 : RecordDataValid section14Catalog 9 (⟨205,(13),[9,10],[42],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1904 : RecordDataValid section14Catalog 9 (⟨205,(14),[9,10],[42],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1905 : RecordDataValid section14Catalog 9 (⟨205,(15),[9,10],[42],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1906 : RecordDataValid section14Catalog 9 (⟨205,(16),[9,10],[42],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1907 : RecordDataValid section14Catalog 9 (⟨205,(17),[9,10],[42],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1908 : RecordDataValid section14Catalog 9 (⟨205,(18),[9,10],[42],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1909 : RecordDataValid section14Catalog 9 (⟨205,(19),[9,10],[42],720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1910 : RecordDataValid section14Catalog 9 (⟨205,(20),[9,10],[42],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1911 : RecordDataValid section14Catalog 9 (⟨205,(21),[9,10],[42],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1912 : RecordDataValid section14Catalog 9 (⟨205,(22),[9,10],[42],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1913 : RecordDataValid section14Catalog 9 (⟨205,(23),[9,10],[42],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1914 : RecordDataValid section14Catalog 9 (⟨205,(24),[9,10],[42],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1915 : RecordDataValid section14Catalog 9 (⟨207,(0),[9],[42],1336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1336,[4,8,9,12,16],1340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1916 : RecordDataValid section14Catalog 9 (⟨207,(1),[9],[42],1337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1337,[4,8,9,12,16],1341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1917 : RecordDataValid section14Catalog 9 (⟨207,(2),[9],[42],1336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1336,[4,8,9,12,16],1340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1918 : RecordDataValid section14Catalog 9 (⟨207,(3),[9],[42],1338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1338,[4,8,9,12,16],1342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1919 : RecordDataValid section14Catalog 9 (⟨207,(4),[9],[42],1339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1339,[4,8,9,12,16],1343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1888).take 32 = [⟨202,(23),[9],[42],1335⟩,⟨202,(24),[9],[42],1335⟩,⟨205,(0),[9,10],[42],711⟩,⟨205,(1),[9,10],[42],711⟩,⟨205,(2),[9,10],[42],711⟩,⟨205,(3),[9,10],[42],712⟩,⟨205,(4),[9,10],[42],711⟩,⟨205,(5),[9,10],[42],713⟩,⟨205,(6),[9,10],[42],713⟩,⟨205,(7),[9,10],[42],713⟩,⟨205,(8),[9,10],[42],714⟩,⟨205,(9),[9,10],[42],713⟩,⟨205,(10),[9,10],[42],715⟩,⟨205,(11),[9,10],[42],716⟩,⟨205,(12),[9,10],[42],717⟩,⟨205,(13),[9,10],[42],718⟩,⟨205,(14),[9,10],[42],719⟩,⟨205,(15),[9,10],[42],715⟩,⟨205,(16),[9,10],[42],720⟩,⟨205,(17),[9,10],[42],720⟩,⟨205,(18),[9,10],[42],721⟩,⟨205,(19),[9,10],[42],720⟩,⟨205,(20),[9,10],[42],715⟩,⟨205,(21),[9,10],[42],716⟩,⟨205,(22),[9,10],[42],717⟩,⟨205,(23),[9,10],[42],718⟩,⟨205,(24),[9,10],[42],719⟩,⟨207,(0),[9],[42],1336⟩,⟨207,(1),[9],[42],1337⟩,⟨207,(2),[9],[42],1336⟩,⟨207,(3),[9],[42],1338⟩,⟨207,(4),[9],[42],1339⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1888
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1889
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1890
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1891
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1892
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1893
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1894
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1895
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1896
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1897
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1898
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1899
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1900
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1901
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1902
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1903
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1904
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1905
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1906
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1907
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1908
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1909
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1910
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1911
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1912
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1913
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1914
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1915
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1916
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1917
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1918
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1919
end Section14Records_9_1888_1920

#print axioms solution
