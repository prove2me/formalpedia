-- Prove2me | solution 1 for Freiman.section14_s0004_records_1920_1952
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T03:00:27.522048+00:00
-- url     : https://prove2.me/submissions/475e87cd-fb87-44ec-bd30-6aaa11a08fa4

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
namespace Section14Records_4_1920_1952
private theorem valid1920 : RecordDataValid section14Catalog 4 (⟨242,(5),[4,8,12],[10],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1921 : RecordDataValid section14Catalog 4 (⟨242,(6),[4,8,12],[10],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1922 : RecordDataValid section14Catalog 4 (⟨242,(7),[4,8,12],[10],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1923 : RecordDataValid section14Catalog 4 (⟨242,(8),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1924 : RecordDataValid section14Catalog 4 (⟨242,(9),[4,8,12],[10],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1925 : RecordDataValid section14Catalog 4 (⟨242,(10),[4,8,12],[10],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1926 : RecordDataValid section14Catalog 4 (⟨242,(11),[4,8,12],[10],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1927 : RecordDataValid section14Catalog 4 (⟨242,(12),[4,8,12],[10],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1928 : RecordDataValid section14Catalog 4 (⟨242,(13),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1929 : RecordDataValid section14Catalog 4 (⟨242,(14),[4,8,12],[10],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1930 : RecordDataValid section14Catalog 4 (⟨242,(15),[4,8,12],[10],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1931 : RecordDataValid section14Catalog 4 (⟨242,(16),[4,8,12],[10],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1932 : RecordDataValid section14Catalog 4 (⟨242,(17),[4,8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1933 : RecordDataValid section14Catalog 4 (⟨242,(18),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1934 : RecordDataValid section14Catalog 4 (⟨242,(19),[4,8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1935 : RecordDataValid section14Catalog 4 (⟨242,(20),[4,8,12],[10],876⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨876,[1,2,4,5,6,8,9,10,12],877⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1936 : RecordDataValid section14Catalog 4 (⟨242,(21),[4,8,12],[10],877⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨877,[1,2,4,5,6,8,9,10,12],878⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1937 : RecordDataValid section14Catalog 4 (⟨242,(22),[4,8,12],[10],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1938 : RecordDataValid section14Catalog 4 (⟨242,(23),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1939 : RecordDataValid section14Catalog 4 (⟨242,(24),[4,8,12],[10],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1940 : RecordDataValid section14Catalog 4 (⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1941 : RecordDataValid section14Catalog 4 (⟨245,(-1),[4,8,10,16],[8,12],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1942 : RecordDataValid section14Catalog 4 (⟨245,(-1),[4,8,16],[1,5,9,13],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1943 : RecordDataValid section14Catalog 4 (⟨245,(-1),[4,8,16],[2],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1944 : RecordDataValid section14Catalog 4 (⟨245,(-1),[4,8,16],[7,11,15],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1945 : RecordDataValid section14Catalog 4 (⟨245,(-1),[4,8,16],[6],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1946 : RecordDataValid section14Catalog 4 (⟨245,(-1),[4,16],[3],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1947 : RecordDataValid section14Catalog 4 (⟨245,(-1),[4,16],[14],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1948 : RecordDataValid section14Catalog 4 (⟨249,(0),[4,8,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1949 : RecordDataValid section14Catalog 4 (⟨249,(1),[4,8,16],[10],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1950 : RecordDataValid section14Catalog 4 (⟨249,(2),[4,8,16],[10],888⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1951 : RecordDataValid section14Catalog 4 (⟨249,(3),[4,8,16],[10],889⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1920).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1920).take 32 = [⟨242,(5),[4,8,12],[10],632⟩,⟨242,(6),[4,8,12],[10],872⟩,⟨242,(7),[4,8,12],[10],874⟩,⟨242,(8),[4,8,12],[10],101⟩,⟨242,(9),[4,8,12],[10],874⟩,⟨242,(10),[4,8,12],[10],632⟩,⟨242,(11),[4,8,12],[10],872⟩,⟨242,(12),[4,8,12],[10],875⟩,⟨242,(13),[4,8,12],[10],101⟩,⟨242,(14),[4,8,12],[10],875⟩,⟨242,(15),[4,8,12],[10],625⟩,⟨242,(16),[4,8,12],[10],626⟩,⟨242,(17),[4,8,12],[10],286⟩,⟨242,(18),[4,8,12],[10],101⟩,⟨242,(19),[4,8,12],[10],286⟩,⟨242,(20),[4,8,12],[10],876⟩,⟨242,(21),[4,8,12],[10],877⟩,⟨242,(22),[4,8,12],[10],287⟩,⟨242,(23),[4,8,12],[10],101⟩,⟨242,(24),[4,8,12],[10],287⟩,⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩,⟨245,(-1),[4,8,10,16],[8,12],882⟩,⟨245,(-1),[4,8,16],[1,5,9,13],883⟩,⟨245,(-1),[4,8,16],[2],884⟩,⟨245,(-1),[4,8,16],[7,11,15],886⟩,⟨245,(-1),[4,8,16],[6],887⟩,⟨245,(-1),[4,16],[3],884⟩,⟨245,(-1),[4,16],[14],909⟩,⟨249,(0),[4,8,16],[10],10⟩,⟨249,(1),[4,8,16],[10],11⟩,⟨249,(2),[4,8,16],[10],888⟩,⟨249,(3),[4,8,16],[10],889⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1920
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1921
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1922
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1923
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1924
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1925
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1926
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1927
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1928
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1929
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1930
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1931
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1932
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1933
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1934
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1935
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1936
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1937
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1938
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1939
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1940
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1941
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1942
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1943
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1944
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1945
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1946
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1947
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1948
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1949
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1950
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1951
end Section14Records_4_1920_1952

#print axioms solution
