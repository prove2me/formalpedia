-- Prove2me | solution 1 for Freiman.section14_s0008_records_1984_2016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:46:47.821639+00:00
-- url     : https://prove2.me/submissions/6211d2c2-7667-449b-95e8-e0ad9ba1237d

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
namespace Section14Records_8_1984_2016
private theorem valid1984 : RecordDataValid section14Catalog 8 (⟨264,(4),[8],[10],1410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1410,[5,8,9,12],1415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1985 : RecordDataValid section14Catalog 8 (⟨264,(5),[8],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1986 : RecordDataValid section14Catalog 8 (⟨264,(6),[8],[10],1408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1408,[5,8],1413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1987 : RecordDataValid section14Catalog 8 (⟨264,(7),[8],[10],1407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1407,[5,8],1412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1988 : RecordDataValid section14Catalog 8 (⟨264,(8),[8],[10],1409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1409,[5,8],1414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1989 : RecordDataValid section14Catalog 8 (⟨264,(9),[8],[10],1410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1410,[5,8,9,12],1415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1990 : RecordDataValid section14Catalog 8 (⟨264,(10),[8],[10],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1991 : RecordDataValid section14Catalog 8 (⟨264,(11),[8],[10],1411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1411,[5,8],1416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1992 : RecordDataValid section14Catalog 8 (⟨264,(12),[8],[10],1411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1411,[5,8],1416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1993 : RecordDataValid section14Catalog 8 (⟨264,(13),[8],[10],1411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1411,[5,8],1416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1994 : RecordDataValid section14Catalog 8 (⟨264,(14),[8],[10],1410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1410,[5,8,9,12],1415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1995 : RecordDataValid section14Catalog 8 (⟨264,(15),[8],[10],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1996 : RecordDataValid section14Catalog 8 (⟨264,(16),[8],[10],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1997 : RecordDataValid section14Catalog 8 (⟨264,(17),[8],[10],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1998 : RecordDataValid section14Catalog 8 (⟨264,(18),[8],[10],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1999 : RecordDataValid section14Catalog 8 (⟨264,(19),[8],[10],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2000 : RecordDataValid section14Catalog 8 (⟨264,(20),[8],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2001 : RecordDataValid section14Catalog 8 (⟨264,(21),[8],[10],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2002 : RecordDataValid section14Catalog 8 (⟨264,(22),[8],[10],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2003 : RecordDataValid section14Catalog 8 (⟨264,(23),[8],[10],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2004 : RecordDataValid section14Catalog 8 (⟨264,(24),[8],[10],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2005 : RecordDataValid section14Catalog 8 (⟨267,(0),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2006 : RecordDataValid section14Catalog 8 (⟨267,(1),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2007 : RecordDataValid section14Catalog 8 (⟨267,(2),[8,12],[10],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2008 : RecordDataValid section14Catalog 8 (⟨267,(3),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2009 : RecordDataValid section14Catalog 8 (⟨267,(4),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2010 : RecordDataValid section14Catalog 8 (⟨267,(5),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2011 : RecordDataValid section14Catalog 8 (⟨267,(6),[8,12],[10],1090⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1090,[3,5,7,8,9,11,12,15],1094⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2012 : RecordDataValid section14Catalog 8 (⟨267,(7),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2013 : RecordDataValid section14Catalog 8 (⟨267,(8),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2014 : RecordDataValid section14Catalog 8 (⟨267,(9),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2015 : RecordDataValid section14Catalog 8 (⟨267,(10),[8,12],[10],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1984).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1984).take 32 = [⟨264,(4),[8],[10],1410⟩,⟨264,(5),[8],[10],10⟩,⟨264,(6),[8],[10],1408⟩,⟨264,(7),[8],[10],1407⟩,⟨264,(8),[8],[10],1409⟩,⟨264,(9),[8],[10],1410⟩,⟨264,(10),[8],[10],18⟩,⟨264,(11),[8],[10],1411⟩,⟨264,(12),[8],[10],1411⟩,⟨264,(13),[8],[10],1411⟩,⟨264,(14),[8],[10],1410⟩,⟨264,(15),[8],[10],21⟩,⟨264,(16),[8],[10],1412⟩,⟨264,(17),[8],[10],1412⟩,⟨264,(18),[8],[10],1412⟩,⟨264,(19),[8],[10],1412⟩,⟨264,(20),[8],[10],24⟩,⟨264,(21),[8],[10],1413⟩,⟨264,(22),[8],[10],1413⟩,⟨264,(23),[8],[10],1413⟩,⟨264,(24),[8],[10],1413⟩,⟨267,(0),[8,12],[10],1086⟩,⟨267,(1),[8,12],[10],1087⟩,⟨267,(2),[8,12],[10],1088⟩,⟨267,(3),[8,12],[10],1089⟩,⟨267,(4),[8,12],[10],1086⟩,⟨267,(5),[8,12],[10],1087⟩,⟨267,(6),[8,12],[10],1090⟩,⟨267,(7),[8,12],[10],1089⟩,⟨267,(8),[8,12],[10],1086⟩,⟨267,(9),[8,12],[10],1087⟩,⟨267,(10),[8,12],[10],1088⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1984
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1985
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1986
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1987
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1988
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1989
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1990
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1991
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1992
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1993
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1994
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1995
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1996
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1997
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1998
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1999
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2000
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2001
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2002
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2003
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2004
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2005
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2006
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2007
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2008
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2009
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2010
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2011
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2012
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2013
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2014
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2015
end Section14Records_8_1984_2016

#print axioms solution
