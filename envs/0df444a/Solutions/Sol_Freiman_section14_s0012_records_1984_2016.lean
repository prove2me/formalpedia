-- Prove2me | solution 1 for Freiman.section14_s0012_records_1984_2016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:17:53.689538+00:00
-- url     : https://prove2.me/submissions/76a3db72-6cd5-4597-b9ff-63be369ca6d8

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
namespace Section14Records_12_1984_2016
private theorem valid1984 : RecordDataValid section14Catalog 12 (⟨293,(11),[8,12],[10],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1985 : RecordDataValid section14Catalog 12 (⟨293,(12),[8,12],[10],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1986 : RecordDataValid section14Catalog 12 (⟨293,(13),[8,12],[10],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1987 : RecordDataValid section14Catalog 12 (⟨293,(14),[8,12],[10],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1988 : RecordDataValid section14Catalog 12 (⟨293,(15),[8,12],[10],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1989 : RecordDataValid section14Catalog 12 (⟨293,(16),[8,12],[10],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1990 : RecordDataValid section14Catalog 12 (⟨293,(17),[8,12],[10],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1991 : RecordDataValid section14Catalog 12 (⟨293,(18),[8,12],[10],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1992 : RecordDataValid section14Catalog 12 (⟨293,(19),[8,12],[10],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1993 : RecordDataValid section14Catalog 12 (⟨293,(20),[8,12],[10],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1994 : RecordDataValid section14Catalog 12 (⟨293,(21),[8,12],[10],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1995 : RecordDataValid section14Catalog 12 (⟨293,(22),[8,12],[10],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1996 : RecordDataValid section14Catalog 12 (⟨293,(23),[8,12],[10],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1997 : RecordDataValid section14Catalog 12 (⟨293,(24),[8,12],[10],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1998 : RecordDataValid section14Catalog 12 (⟨295,(0),[8,12],[10],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1999 : RecordDataValid section14Catalog 12 (⟨295,(1),[8,12],[10],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2000 : RecordDataValid section14Catalog 12 (⟨295,(2),[8,12],[10],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2001 : RecordDataValid section14Catalog 12 (⟨295,(3),[8,12],[10],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2002 : RecordDataValid section14Catalog 12 (⟨295,(4),[8,12],[10],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2003 : RecordDataValid section14Catalog 12 (⟨295,(5),[8,12],[10],1448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1448,[5,8,9,12],1453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2004 : RecordDataValid section14Catalog 12 (⟨295,(6),[8,12],[10],1448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1448,[5,8,9,12],1453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2005 : RecordDataValid section14Catalog 12 (⟨295,(7),[8,12],[10],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2006 : RecordDataValid section14Catalog 12 (⟨295,(8),[8,12],[10],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2007 : RecordDataValid section14Catalog 12 (⟨295,(9),[8,12],[10],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2008 : RecordDataValid section14Catalog 12 (⟨295,(10),[8,12],[10],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2009 : RecordDataValid section14Catalog 12 (⟨295,(11),[8,12],[10],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2010 : RecordDataValid section14Catalog 12 (⟨295,(12),[8,12],[10],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2011 : RecordDataValid section14Catalog 12 (⟨295,(13),[8,12],[10],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2012 : RecordDataValid section14Catalog 12 (⟨295,(14),[8,12],[10],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2013 : RecordDataValid section14Catalog 12 (⟨295,(15),[8,12],[10],1449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1449,[5,8,9,12],1454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2014 : RecordDataValid section14Catalog 12 (⟨295,(16),[8,12],[10],1449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1449,[5,8,9,12],1454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2015 : RecordDataValid section14Catalog 12 (⟨295,(17),[8,12],[10],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1984).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1984).take 32 = [⟨293,(11),[8,12],[10],1153⟩,⟨293,(12),[8,12],[10],1157⟩,⟨293,(13),[8,12],[10],1156⟩,⟨293,(14),[8,12],[10],1157⟩,⟨293,(15),[8,12],[10],1152⟩,⟨293,(16),[8,12],[10],1153⟩,⟨293,(17),[8,12],[10],1155⟩,⟨293,(18),[8,12],[10],1156⟩,⟨293,(19),[8,12],[10],1155⟩,⟨293,(20),[8,12],[10],1152⟩,⟨293,(21),[8,12],[10],1153⟩,⟨293,(22),[8,12],[10],1158⟩,⟨293,(23),[8,12],[10],1156⟩,⟨293,(24),[8,12],[10],1158⟩,⟨295,(0),[8,12],[10],1444⟩,⟨295,(1),[8,12],[10],1444⟩,⟨295,(2),[8,12],[10],1445⟩,⟨295,(3),[8,12],[10],1446⟩,⟨295,(4),[8,12],[10],1447⟩,⟨295,(5),[8,12],[10],1448⟩,⟨295,(6),[8,12],[10],1448⟩,⟨295,(7),[8,12],[10],1445⟩,⟨295,(8),[8,12],[10],1446⟩,⟨295,(9),[8,12],[10],1447⟩,⟨295,(10),[8,12],[10],1444⟩,⟨295,(11),[8,12],[10],1444⟩,⟨295,(12),[8,12],[10],1445⟩,⟨295,(13),[8,12],[10],1446⟩,⟨295,(14),[8,12],[10],1447⟩,⟨295,(15),[8,12],[10],1449⟩,⟨295,(16),[8,12],[10],1449⟩,⟨295,(17),[8,12],[10],1445⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1984
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1985
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1986
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1987
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1988
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1989
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1990
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1991
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1992
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1993
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1994
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1995
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1996
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1997
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1998
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1999
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2000
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2001
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2002
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2003
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2004
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2005
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2006
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2007
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2008
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2009
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2010
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2011
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2012
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2013
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2014
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2015
end Section14Records_12_1984_2016

#print axioms solution
