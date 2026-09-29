-- Prove2me | solution 1 for Freiman.section14_s0016_records_0960_0992
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:14:09.661044+00:00
-- url     : https://prove2.me/submissions/57a417cb-cae3-4939-8b2d-cb215e972c2b

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
namespace Section14Records_16_960_992
private theorem valid960 : RecordDataValid section14Catalog 16 (⟨167,(0),[4,8,12,16],[10],1285⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1285,[4,8,9,12,16],1289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid961 : RecordDataValid section14Catalog 16 (⟨167,(1),[4,8,12,16],[10],1286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1286,[4,8,9,12,16],1290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid962 : RecordDataValid section14Catalog 16 (⟨167,(2),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid963 : RecordDataValid section14Catalog 16 (⟨167,(3),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid964 : RecordDataValid section14Catalog 16 (⟨167,(4),[4,8,12,16],[10],1289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1289,[4,8,9,12,16],1293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid965 : RecordDataValid section14Catalog 16 (⟨167,(5),[4,8,12,16],[10],1286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1286,[4,8,9,12,16],1290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid966 : RecordDataValid section14Catalog 16 (⟨167,(6),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid967 : RecordDataValid section14Catalog 16 (⟨167,(7),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid968 : RecordDataValid section14Catalog 16 (⟨167,(8),[4,8,12,16],[10],1285⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1285,[4,8,9,12,16],1289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid969 : RecordDataValid section14Catalog 16 (⟨167,(9),[4,8,12,16],[10],1286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1286,[4,8,9,12,16],1290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid970 : RecordDataValid section14Catalog 16 (⟨167,(10),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid971 : RecordDataValid section14Catalog 16 (⟨167,(11),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid972 : RecordDataValid section14Catalog 16 (⟨167,(12),[4,8,12,16],[10],1290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1290,[4,8,9,12,16],1294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid973 : RecordDataValid section14Catalog 16 (⟨167,(13),[4,8,12,16],[10],1286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1286,[4,8,9,12,16],1290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid974 : RecordDataValid section14Catalog 16 (⟨167,(14),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid975 : RecordDataValid section14Catalog 16 (⟨167,(15),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid976 : RecordDataValid section14Catalog 16 (⟨171,(0),[3,4,8,12,15,16],[10],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid977 : RecordDataValid section14Catalog 16 (⟨171,(1),[3,4,8,12,15,16],[10],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid978 : RecordDataValid section14Catalog 16 (⟨171,(2),[3,4,8,12,15,16],[10],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid979 : RecordDataValid section14Catalog 16 (⟨171,(3),[3,4,8,12,15,16],[10],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid980 : RecordDataValid section14Catalog 16 (⟨172,(0),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid981 : RecordDataValid section14Catalog 16 (⟨172,(1),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid982 : RecordDataValid section14Catalog 16 (⟨172,(2),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid983 : RecordDataValid section14Catalog 16 (⟨172,(3),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid984 : RecordDataValid section14Catalog 16 (⟨172,(4),[4,8,12,16],[10],1295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1295,[4,8,9,12,16],1299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid985 : RecordDataValid section14Catalog 16 (⟨172,(5),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid986 : RecordDataValid section14Catalog 16 (⟨172,(6),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid987 : RecordDataValid section14Catalog 16 (⟨172,(7),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid988 : RecordDataValid section14Catalog 16 (⟨172,(8),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid989 : RecordDataValid section14Catalog 16 (⟨172,(9),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid990 : RecordDataValid section14Catalog 16 (⟨172,(10),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid991 : RecordDataValid section14Catalog 16 (⟨172,(11),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 960).take 32 = [⟨167,(0),[4,8,12,16],[10],1285⟩,⟨167,(1),[4,8,12,16],[10],1286⟩,⟨167,(2),[4,8,12,16],[10],1287⟩,⟨167,(3),[4,8,12,16],[10],1288⟩,⟨167,(4),[4,8,12,16],[10],1289⟩,⟨167,(5),[4,8,12,16],[10],1286⟩,⟨167,(6),[4,8,12,16],[10],1287⟩,⟨167,(7),[4,8,12,16],[10],1288⟩,⟨167,(8),[4,8,12,16],[10],1285⟩,⟨167,(9),[4,8,12,16],[10],1286⟩,⟨167,(10),[4,8,12,16],[10],1287⟩,⟨167,(11),[4,8,12,16],[10],1288⟩,⟨167,(12),[4,8,12,16],[10],1290⟩,⟨167,(13),[4,8,12,16],[10],1286⟩,⟨167,(14),[4,8,12,16],[10],1287⟩,⟨167,(15),[4,8,12,16],[10],1288⟩,⟨171,(0),[3,4,8,12,15,16],[10],650⟩,⟨171,(1),[3,4,8,12,15,16],[10],651⟩,⟨171,(2),[3,4,8,12,15,16],[10],652⟩,⟨171,(3),[3,4,8,12,15,16],[10],653⟩,⟨172,(0),[4,8,12,16],[10],1291⟩,⟨172,(1),[4,8,12,16],[10],1292⟩,⟨172,(2),[4,8,12,16],[10],1293⟩,⟨172,(3),[4,8,12,16],[10],1294⟩,⟨172,(4),[4,8,12,16],[10],1295⟩,⟨172,(5),[4,8,12,16],[10],1292⟩,⟨172,(6),[4,8,12,16],[10],1293⟩,⟨172,(7),[4,8,12,16],[10],1294⟩,⟨172,(8),[4,8,12,16],[10],1291⟩,⟨172,(9),[4,8,12,16],[10],1292⟩,⟨172,(10),[4,8,12,16],[10],1293⟩,⟨172,(11),[4,8,12,16],[10],1294⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid960
  · exact recordValid_of_data section14Catalog 16 _ hnum valid961
  · exact recordValid_of_data section14Catalog 16 _ hnum valid962
  · exact recordValid_of_data section14Catalog 16 _ hnum valid963
  · exact recordValid_of_data section14Catalog 16 _ hnum valid964
  · exact recordValid_of_data section14Catalog 16 _ hnum valid965
  · exact recordValid_of_data section14Catalog 16 _ hnum valid966
  · exact recordValid_of_data section14Catalog 16 _ hnum valid967
  · exact recordValid_of_data section14Catalog 16 _ hnum valid968
  · exact recordValid_of_data section14Catalog 16 _ hnum valid969
  · exact recordValid_of_data section14Catalog 16 _ hnum valid970
  · exact recordValid_of_data section14Catalog 16 _ hnum valid971
  · exact recordValid_of_data section14Catalog 16 _ hnum valid972
  · exact recordValid_of_data section14Catalog 16 _ hnum valid973
  · exact recordValid_of_data section14Catalog 16 _ hnum valid974
  · exact recordValid_of_data section14Catalog 16 _ hnum valid975
  · exact recordValid_of_data section14Catalog 16 _ hnum valid976
  · exact recordValid_of_data section14Catalog 16 _ hnum valid977
  · exact recordValid_of_data section14Catalog 16 _ hnum valid978
  · exact recordValid_of_data section14Catalog 16 _ hnum valid979
  · exact recordValid_of_data section14Catalog 16 _ hnum valid980
  · exact recordValid_of_data section14Catalog 16 _ hnum valid981
  · exact recordValid_of_data section14Catalog 16 _ hnum valid982
  · exact recordValid_of_data section14Catalog 16 _ hnum valid983
  · exact recordValid_of_data section14Catalog 16 _ hnum valid984
  · exact recordValid_of_data section14Catalog 16 _ hnum valid985
  · exact recordValid_of_data section14Catalog 16 _ hnum valid986
  · exact recordValid_of_data section14Catalog 16 _ hnum valid987
  · exact recordValid_of_data section14Catalog 16 _ hnum valid988
  · exact recordValid_of_data section14Catalog 16 _ hnum valid989
  · exact recordValid_of_data section14Catalog 16 _ hnum valid990
  · exact recordValid_of_data section14Catalog 16 _ hnum valid991
end Section14Records_16_960_992

#print axioms solution
