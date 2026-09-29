-- Prove2me | solution 1 for Freiman.section14_s0009_records_1920_1952
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:07:25.495986+00:00
-- url     : https://prove2.me/submissions/d22234d5-99f2-4ce4-8198-8c6e7d1d19b1

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
namespace Section14Records_9_1920_1952
private theorem valid1920 : RecordDataValid section14Catalog 9 (⟨207,(5),[9],[42],1336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1336,[4,8,9,12,16],1340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1921 : RecordDataValid section14Catalog 9 (⟨207,(6),[9],[42],1337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1337,[4,8,9,12,16],1341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1922 : RecordDataValid section14Catalog 9 (⟨207,(7),[9],[42],1336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1336,[4,8,9,12,16],1340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1923 : RecordDataValid section14Catalog 9 (⟨207,(8),[9],[42],1338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1338,[4,8,9,12,16],1342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1924 : RecordDataValid section14Catalog 9 (⟨207,(9),[9],[42],1339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1339,[4,8,9,12,16],1343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1925 : RecordDataValid section14Catalog 9 (⟨207,(10),[9],[42],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1926 : RecordDataValid section14Catalog 9 (⟨207,(11),[9],[42],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1927 : RecordDataValid section14Catalog 9 (⟨207,(12),[9],[42],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1928 : RecordDataValid section14Catalog 9 (⟨207,(13),[9],[42],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1929 : RecordDataValid section14Catalog 9 (⟨207,(14),[9],[42],1339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1339,[4,8,9,12,16],1343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1930 : RecordDataValid section14Catalog 9 (⟨207,(15),[9],[42],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1931 : RecordDataValid section14Catalog 9 (⟨207,(16),[9],[42],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1932 : RecordDataValid section14Catalog 9 (⟨207,(17),[9],[42],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1933 : RecordDataValid section14Catalog 9 (⟨207,(18),[9],[42],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1934 : RecordDataValid section14Catalog 9 (⟨207,(19),[9],[42],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1935 : RecordDataValid section14Catalog 9 (⟨207,(20),[9],[42],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1936 : RecordDataValid section14Catalog 9 (⟨207,(21),[9],[42],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1937 : RecordDataValid section14Catalog 9 (⟨207,(22),[9],[42],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1938 : RecordDataValid section14Catalog 9 (⟨207,(23),[9],[42],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1939 : RecordDataValid section14Catalog 9 (⟨207,(24),[9],[42],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1940 : RecordDataValid section14Catalog 9 (⟨210,(0),[9,10],[42],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1941 : RecordDataValid section14Catalog 9 (⟨210,(1),[9,10],[42],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1942 : RecordDataValid section14Catalog 9 (⟨210,(2),[9,10],[42],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1943 : RecordDataValid section14Catalog 9 (⟨210,(3),[9,10],[42],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1944 : RecordDataValid section14Catalog 9 (⟨210,(4),[9,10],[42],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1945 : RecordDataValid section14Catalog 9 (⟨210,(5),[9,10],[42],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1946 : RecordDataValid section14Catalog 9 (⟨210,(6),[9,10],[42],726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1947 : RecordDataValid section14Catalog 9 (⟨210,(7),[9,10],[42],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1948 : RecordDataValid section14Catalog 9 (⟨210,(8),[9,10],[42],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1949 : RecordDataValid section14Catalog 9 (⟨210,(9),[9,10],[42],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1950 : RecordDataValid section14Catalog 9 (⟨210,(10),[9,10],[42],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1951 : RecordDataValid section14Catalog 9 (⟨210,(11),[9,10],[42],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1920).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1920).take 32 = [⟨207,(5),[9],[42],1336⟩,⟨207,(6),[9],[42],1337⟩,⟨207,(7),[9],[42],1336⟩,⟨207,(8),[9],[42],1338⟩,⟨207,(9),[9],[42],1339⟩,⟨207,(10),[9],[42],1340⟩,⟨207,(11),[9],[42],1340⟩,⟨207,(12),[9],[42],1340⟩,⟨207,(13),[9],[42],1340⟩,⟨207,(14),[9],[42],1339⟩,⟨207,(15),[9],[42],1341⟩,⟨207,(16),[9],[42],1341⟩,⟨207,(17),[9],[42],1341⟩,⟨207,(18),[9],[42],1341⟩,⟨207,(19),[9],[42],1341⟩,⟨207,(20),[9],[42],1342⟩,⟨207,(21),[9],[42],1342⟩,⟨207,(22),[9],[42],1342⟩,⟨207,(23),[9],[42],1342⟩,⟨207,(24),[9],[42],1342⟩,⟨210,(0),[9,10],[42],722⟩,⟨210,(1),[9,10],[42],723⟩,⟨210,(2),[9,10],[42],724⟩,⟨210,(3),[9,10],[42],725⟩,⟨210,(4),[9,10],[42],722⟩,⟨210,(5),[9,10],[42],723⟩,⟨210,(6),[9,10],[42],726⟩,⟨210,(7),[9,10],[42],725⟩,⟨210,(8),[9,10],[42],722⟩,⟨210,(9),[9,10],[42],723⟩,⟨210,(10),[9,10],[42],724⟩,⟨210,(11),[9,10],[42],725⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1920
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1921
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1922
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1923
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1924
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1925
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1926
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1927
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1928
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1929
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1930
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1931
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1932
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1933
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1934
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1935
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1936
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1937
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1938
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1939
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1940
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1941
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1942
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1943
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1944
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1945
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1946
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1947
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1948
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1949
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1950
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1951
end Section14Records_9_1920_1952

#print axioms solution
