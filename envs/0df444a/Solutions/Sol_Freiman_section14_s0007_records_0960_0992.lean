-- Prove2me | solution 1 for Freiman.section14_s0007_records_0960_0992
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:45:45.878395+00:00
-- url     : https://prove2.me/submissions/37fe90e8-8bcd-44a6-97d6-e380026d5eb1

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
namespace Section14Records_7_960_992
private theorem valid960 : RecordDataValid section14Catalog 7 (⟨190,(6),[7],[10],1582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1582,[7],1587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid961 : RecordDataValid section14Catalog 7 (⟨190,(7),[3,7],[11],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid962 : RecordDataValid section14Catalog 7 (⟨190,(7),[7],[10],1582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1582,[7],1587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid963 : RecordDataValid section14Catalog 7 (⟨190,(8),[3,7],[11],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid964 : RecordDataValid section14Catalog 7 (⟨190,(8),[7],[10],1582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1582,[7],1587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid965 : RecordDataValid section14Catalog 7 (⟨190,(9),[3,7],[11],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid966 : RecordDataValid section14Catalog 7 (⟨190,(9),[7],[10],1582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1582,[7],1587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid967 : RecordDataValid section14Catalog 7 (⟨190,(10),[3,7],[11],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid968 : RecordDataValid section14Catalog 7 (⟨190,(10),[7],[10],1583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1583,[7],1588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid969 : RecordDataValid section14Catalog 7 (⟨190,(11),[3,7],[11],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid970 : RecordDataValid section14Catalog 7 (⟨190,(11),[7],[10],1584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1584,[7],1589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid971 : RecordDataValid section14Catalog 7 (⟨190,(12),[3,7],[11],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid972 : RecordDataValid section14Catalog 7 (⟨190,(12),[7],[10],1585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1585,[7],1590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid973 : RecordDataValid section14Catalog 7 (⟨190,(13),[3,7],[11],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid974 : RecordDataValid section14Catalog 7 (⟨190,(13),[7],[10],1584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1584,[7],1589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid975 : RecordDataValid section14Catalog 7 (⟨190,(14),[3,7],[11],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid976 : RecordDataValid section14Catalog 7 (⟨190,(14),[7],[10],1586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1586,[7],1591⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid977 : RecordDataValid section14Catalog 7 (⟨190,(15),[3,7],[11],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid978 : RecordDataValid section14Catalog 7 (⟨190,(15),[7],[10],1583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1583,[7],1588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid979 : RecordDataValid section14Catalog 7 (⟨190,(16),[3,7],[11],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid980 : RecordDataValid section14Catalog 7 (⟨190,(16),[7],[10],1587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1587,[7],1592⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid981 : RecordDataValid section14Catalog 7 (⟨190,(17),[3,7],[11],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid982 : RecordDataValid section14Catalog 7 (⟨190,(17),[7],[10],1587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1587,[7],1592⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid983 : RecordDataValid section14Catalog 7 (⟨190,(18),[3,7],[11],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid984 : RecordDataValid section14Catalog 7 (⟨190,(18),[7],[10],1587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1587,[7],1592⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid985 : RecordDataValid section14Catalog 7 (⟨190,(19),[3,7],[11],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid986 : RecordDataValid section14Catalog 7 (⟨190,(19),[7],[10],1587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1587,[7],1592⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid987 : RecordDataValid section14Catalog 7 (⟨190,(20),[3,7],[11],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid988 : RecordDataValid section14Catalog 7 (⟨190,(20),[7],[10],1583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1583,[7],1588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid989 : RecordDataValid section14Catalog 7 (⟨190,(21),[3,7],[11],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid990 : RecordDataValid section14Catalog 7 (⟨190,(21),[7],[10],1584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1584,[7],1589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid991 : RecordDataValid section14Catalog 7 (⟨190,(22),[3,7],[11],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 960).take 32 = [⟨190,(6),[7],[10],1582⟩,⟨190,(7),[3,7],[11],691⟩,⟨190,(7),[7],[10],1582⟩,⟨190,(8),[3,7],[11],691⟩,⟨190,(8),[7],[10],1582⟩,⟨190,(9),[3,7],[11],691⟩,⟨190,(9),[7],[10],1582⟩,⟨190,(10),[3,7],[11],692⟩,⟨190,(10),[7],[10],1583⟩,⟨190,(11),[3,7],[11],693⟩,⟨190,(11),[7],[10],1584⟩,⟨190,(12),[3,7],[11],694⟩,⟨190,(12),[7],[10],1585⟩,⟨190,(13),[3,7],[11],693⟩,⟨190,(13),[7],[10],1584⟩,⟨190,(14),[3,7],[11],695⟩,⟨190,(14),[7],[10],1586⟩,⟨190,(15),[3,7],[11],692⟩,⟨190,(15),[7],[10],1583⟩,⟨190,(16),[3,7],[11],696⟩,⟨190,(16),[7],[10],1587⟩,⟨190,(17),[3,7],[11],696⟩,⟨190,(17),[7],[10],1587⟩,⟨190,(18),[3,7],[11],696⟩,⟨190,(18),[7],[10],1587⟩,⟨190,(19),[3,7],[11],696⟩,⟨190,(19),[7],[10],1587⟩,⟨190,(20),[3,7],[11],692⟩,⟨190,(20),[7],[10],1583⟩,⟨190,(21),[3,7],[11],693⟩,⟨190,(21),[7],[10],1584⟩,⟨190,(22),[3,7],[11],694⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid960
  · exact recordValid_of_data section14Catalog 7 _ hnum valid961
  · exact recordValid_of_data section14Catalog 7 _ hnum valid962
  · exact recordValid_of_data section14Catalog 7 _ hnum valid963
  · exact recordValid_of_data section14Catalog 7 _ hnum valid964
  · exact recordValid_of_data section14Catalog 7 _ hnum valid965
  · exact recordValid_of_data section14Catalog 7 _ hnum valid966
  · exact recordValid_of_data section14Catalog 7 _ hnum valid967
  · exact recordValid_of_data section14Catalog 7 _ hnum valid968
  · exact recordValid_of_data section14Catalog 7 _ hnum valid969
  · exact recordValid_of_data section14Catalog 7 _ hnum valid970
  · exact recordValid_of_data section14Catalog 7 _ hnum valid971
  · exact recordValid_of_data section14Catalog 7 _ hnum valid972
  · exact recordValid_of_data section14Catalog 7 _ hnum valid973
  · exact recordValid_of_data section14Catalog 7 _ hnum valid974
  · exact recordValid_of_data section14Catalog 7 _ hnum valid975
  · exact recordValid_of_data section14Catalog 7 _ hnum valid976
  · exact recordValid_of_data section14Catalog 7 _ hnum valid977
  · exact recordValid_of_data section14Catalog 7 _ hnum valid978
  · exact recordValid_of_data section14Catalog 7 _ hnum valid979
  · exact recordValid_of_data section14Catalog 7 _ hnum valid980
  · exact recordValid_of_data section14Catalog 7 _ hnum valid981
  · exact recordValid_of_data section14Catalog 7 _ hnum valid982
  · exact recordValid_of_data section14Catalog 7 _ hnum valid983
  · exact recordValid_of_data section14Catalog 7 _ hnum valid984
  · exact recordValid_of_data section14Catalog 7 _ hnum valid985
  · exact recordValid_of_data section14Catalog 7 _ hnum valid986
  · exact recordValid_of_data section14Catalog 7 _ hnum valid987
  · exact recordValid_of_data section14Catalog 7 _ hnum valid988
  · exact recordValid_of_data section14Catalog 7 _ hnum valid989
  · exact recordValid_of_data section14Catalog 7 _ hnum valid990
  · exact recordValid_of_data section14Catalog 7 _ hnum valid991
end Section14Records_7_960_992

#print axioms solution
