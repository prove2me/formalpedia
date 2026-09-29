-- Prove2me | solution 1 for Freiman.section14_s0016_records_0992_1024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:15:11.113066+00:00
-- url     : https://prove2.me/submissions/cf9a8859-8ad9-46d0-9b52-8e7f260b8ff5

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
namespace Section14Records_16_992_1024
private theorem valid992 : RecordDataValid section14Catalog 16 (⟨172,(12),[4,8,12,16],[10],1296⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1296,[4,8,9,12,16],1300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid993 : RecordDataValid section14Catalog 16 (⟨172,(13),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid994 : RecordDataValid section14Catalog 16 (⟨172,(14),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid995 : RecordDataValid section14Catalog 16 (⟨172,(15),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid996 : RecordDataValid section14Catalog 16 (⟨175,(0),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid997 : RecordDataValid section14Catalog 16 (⟨175,(1),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid998 : RecordDataValid section14Catalog 16 (⟨175,(2),[3,4,8,12,15,16],[10],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid999 : RecordDataValid section14Catalog 16 (⟨175,(3),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1000 : RecordDataValid section14Catalog 16 (⟨175,(4),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1001 : RecordDataValid section14Catalog 16 (⟨175,(5),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1002 : RecordDataValid section14Catalog 16 (⟨175,(6),[3,4,8,12,15,16],[10],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1003 : RecordDataValid section14Catalog 16 (⟨175,(7),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1004 : RecordDataValid section14Catalog 16 (⟨175,(8),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1005 : RecordDataValid section14Catalog 16 (⟨175,(9),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1006 : RecordDataValid section14Catalog 16 (⟨175,(10),[3,4,8,12,15,16],[10],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1007 : RecordDataValid section14Catalog 16 (⟨175,(11),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1008 : RecordDataValid section14Catalog 16 (⟨175,(12),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1009 : RecordDataValid section14Catalog 16 (⟨175,(13),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1010 : RecordDataValid section14Catalog 16 (⟨175,(14),[3,4,8,12,15,16],[10],659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨659,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],660⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1011 : RecordDataValid section14Catalog 16 (⟨175,(15),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1012 : RecordDataValid section14Catalog 16 (⟨178,(0),[4,8,12,16],[10],1297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1297,[4,8,9,12,16],1301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1013 : RecordDataValid section14Catalog 16 (⟨178,(1),[4,8,12,16],[10],1298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1298,[4,8,9,12,16],1302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1014 : RecordDataValid section14Catalog 16 (⟨178,(2),[4,8,12,16],[10],1297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1297,[4,8,9,12,16],1301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1015 : RecordDataValid section14Catalog 16 (⟨178,(3),[4,8,12,16],[10],1299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1299,[4,8,9,12,16],1303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1016 : RecordDataValid section14Catalog 16 (⟨178,(4),[4,8,12,16],[10],1300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1300,[4,8,9,12,16],1304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1017 : RecordDataValid section14Catalog 16 (⟨178,(5),[4,8,12,16],[10],1300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1300,[4,8,9,12,16],1304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1018 : RecordDataValid section14Catalog 16 (⟨178,(6),[4,8,12,16],[10],1300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1300,[4,8,9,12,16],1304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1019 : RecordDataValid section14Catalog 16 (⟨178,(7),[4,8,12,16],[10],1300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1300,[4,8,9,12,16],1304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1020 : RecordDataValid section14Catalog 16 (⟨178,(8),[4,8,12,16],[10],1301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1301,[4,8,9,12,16],1305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1021 : RecordDataValid section14Catalog 16 (⟨178,(9),[4,8,12,16],[10],1301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1301,[4,8,9,12,16],1305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1022 : RecordDataValid section14Catalog 16 (⟨178,(10),[4,8,12,16],[10],1301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1301,[4,8,9,12,16],1305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1023 : RecordDataValid section14Catalog 16 (⟨178,(11),[4,8,12,16],[10],1301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1301,[4,8,9,12,16],1305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 992).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 992).take 32 = [⟨172,(12),[4,8,12,16],[10],1296⟩,⟨172,(13),[4,8,12,16],[10],1292⟩,⟨172,(14),[4,8,12,16],[10],1293⟩,⟨172,(15),[4,8,12,16],[10],1294⟩,⟨175,(0),[3,4,8,12,15,16],[10],654⟩,⟨175,(1),[3,4,8,12,15,16],[10],655⟩,⟨175,(2),[3,4,8,12,15,16],[10],656⟩,⟨175,(3),[3,4,8,12,15,16],[10],657⟩,⟨175,(4),[3,4,8,12,15,16],[10],654⟩,⟨175,(5),[3,4,8,12,15,16],[10],655⟩,⟨175,(6),[3,4,8,12,15,16],[10],658⟩,⟨175,(7),[3,4,8,12,15,16],[10],657⟩,⟨175,(8),[3,4,8,12,15,16],[10],654⟩,⟨175,(9),[3,4,8,12,15,16],[10],655⟩,⟨175,(10),[3,4,8,12,15,16],[10],656⟩,⟨175,(11),[3,4,8,12,15,16],[10],657⟩,⟨175,(12),[3,4,8,12,15,16],[10],654⟩,⟨175,(13),[3,4,8,12,15,16],[10],655⟩,⟨175,(14),[3,4,8,12,15,16],[10],659⟩,⟨175,(15),[3,4,8,12,15,16],[10],657⟩,⟨178,(0),[4,8,12,16],[10],1297⟩,⟨178,(1),[4,8,12,16],[10],1298⟩,⟨178,(2),[4,8,12,16],[10],1297⟩,⟨178,(3),[4,8,12,16],[10],1299⟩,⟨178,(4),[4,8,12,16],[10],1300⟩,⟨178,(5),[4,8,12,16],[10],1300⟩,⟨178,(6),[4,8,12,16],[10],1300⟩,⟨178,(7),[4,8,12,16],[10],1300⟩,⟨178,(8),[4,8,12,16],[10],1301⟩,⟨178,(9),[4,8,12,16],[10],1301⟩,⟨178,(10),[4,8,12,16],[10],1301⟩,⟨178,(11),[4,8,12,16],[10],1301⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid992
  · exact recordValid_of_data section14Catalog 16 _ hnum valid993
  · exact recordValid_of_data section14Catalog 16 _ hnum valid994
  · exact recordValid_of_data section14Catalog 16 _ hnum valid995
  · exact recordValid_of_data section14Catalog 16 _ hnum valid996
  · exact recordValid_of_data section14Catalog 16 _ hnum valid997
  · exact recordValid_of_data section14Catalog 16 _ hnum valid998
  · exact recordValid_of_data section14Catalog 16 _ hnum valid999
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1000
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1001
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1002
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1003
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1004
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1005
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1006
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1007
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1008
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1009
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1010
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1011
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1012
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1013
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1014
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1015
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1016
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1017
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1018
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1019
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1020
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1021
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1022
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1023
end Section14Records_16_992_1024

#print axioms solution
