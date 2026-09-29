-- Prove2me | solution 1 for Freiman.section14_s0007_records_1984_2016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:28:33.275335+00:00
-- url     : https://prove2.me/submissions/9d397355-b30b-4dbc-8dc3-6b0b5b34b64e

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
namespace Section14Records_7_1984_2016
private theorem valid1984 : RecordDataValid section14Catalog 7 (⟨335,(2),[3,7,15],[9],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1985 : RecordDataValid section14Catalog 7 (⟨335,(3),[3,7,15],[8],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1986 : RecordDataValid section14Catalog 7 (⟨335,(3),[3,7,15],[9],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1987 : RecordDataValid section14Catalog 7 (⟨335,(4),[3,7,15],[8],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1988 : RecordDataValid section14Catalog 7 (⟨335,(4),[3,7,15],[9],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1989 : RecordDataValid section14Catalog 7 (⟨335,(5),[3,7,15],[8],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1990 : RecordDataValid section14Catalog 7 (⟨335,(5),[3,7,15],[9],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1991 : RecordDataValid section14Catalog 7 (⟨335,(6),[3,7,15],[8],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1992 : RecordDataValid section14Catalog 7 (⟨335,(6),[3,7,15],[9],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1993 : RecordDataValid section14Catalog 7 (⟨335,(7),[3,7,15],[8],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1994 : RecordDataValid section14Catalog 7 (⟨335,(7),[3,7,15],[9],131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨131,[1,2,3,5,6,7,13,14,15],131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1995 : RecordDataValid section14Catalog 7 (⟨335,(8),[3,7,15],[8],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1996 : RecordDataValid section14Catalog 7 (⟨335,(8),[3,7,15],[9],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1997 : RecordDataValid section14Catalog 7 (⟨335,(9),[3,7,15],[8],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1998 : RecordDataValid section14Catalog 7 (⟨335,(9),[3,7,15],[9],129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨129,[1,2,3,5,6,7,13,14,15],129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1999 : RecordDataValid section14Catalog 7 (⟨339,(0),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2000 : RecordDataValid section14Catalog 7 (⟨339,(1),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2001 : RecordDataValid section14Catalog 7 (⟨339,(2),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2002 : RecordDataValid section14Catalog 7 (⟨339,(3),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2003 : RecordDataValid section14Catalog 7 (⟨339,(4),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2004 : RecordDataValid section14Catalog 7 (⟨339,(5),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2005 : RecordDataValid section14Catalog 7 (⟨339,(6),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2006 : RecordDataValid section14Catalog 7 (⟨339,(7),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2007 : RecordDataValid section14Catalog 7 (⟨339,(8),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2008 : RecordDataValid section14Catalog 7 (⟨339,(9),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2009 : RecordDataValid section14Catalog 7 (⟨343,(0),[3,7],[8],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2010 : RecordDataValid section14Catalog 7 (⟨343,(0),[3,7],[9],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2011 : RecordDataValid section14Catalog 7 (⟨343,(1),[3,7],[8],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2012 : RecordDataValid section14Catalog 7 (⟨343,(1),[3,7],[9],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2013 : RecordDataValid section14Catalog 7 (⟨343,(2),[3,7],[8],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2014 : RecordDataValid section14Catalog 7 (⟨343,(2),[3,7],[9],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2015 : RecordDataValid section14Catalog 7 (⟨343,(3),[3,7],[8],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1984).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1984).take 32 = [⟨335,(2),[3,7,15],[9],126⟩,⟨335,(3),[3,7,15],[8],107⟩,⟨335,(3),[3,7,15],[9],126⟩,⟨335,(4),[3,7,15],[8],108⟩,⟨335,(4),[3,7,15],[9],127⟩,⟨335,(5),[3,7,15],[8],110⟩,⟨335,(5),[3,7,15],[9],129⟩,⟨335,(6),[3,7,15],[8],108⟩,⟨335,(6),[3,7,15],[9],127⟩,⟨335,(7),[3,7,15],[8],112⟩,⟨335,(7),[3,7,15],[9],131⟩,⟨335,(8),[3,7,15],[8],108⟩,⟨335,(8),[3,7,15],[9],127⟩,⟨335,(9),[3,7,15],[8],110⟩,⟨335,(9),[3,7,15],[9],129⟩,⟨339,(0),[3,7,15],[8,9],2⟩,⟨339,(1),[3,7,15],[8,9],2⟩,⟨339,(2),[3,7,15],[8,9],2⟩,⟨339,(3),[3,7,15],[8,9],2⟩,⟨339,(4),[3,7,15],[8,9],2⟩,⟨339,(5),[3,7,15],[8,9],2⟩,⟨339,(6),[3,7,15],[8,9],2⟩,⟨339,(7),[3,7,15],[8,9],2⟩,⟨339,(8),[3,7,15],[8,9],2⟩,⟨339,(9),[3,7,15],[8,9],2⟩,⟨343,(0),[3,7],[8],113⟩,⟨343,(0),[3,7],[9],132⟩,⟨343,(1),[3,7],[8],113⟩,⟨343,(1),[3,7],[9],132⟩,⟨343,(2),[3,7],[8],114⟩,⟨343,(2),[3,7],[9],133⟩,⟨343,(3),[3,7],[8],114⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1984
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1985
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1986
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1987
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1988
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1989
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1990
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1991
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1992
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1993
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1994
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1995
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1996
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1997
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1998
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1999
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2000
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2001
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2002
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2003
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2004
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2005
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2006
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2007
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2008
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2009
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2010
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2011
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2012
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2013
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2014
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2015
end Section14Records_7_1984_2016

#print axioms solution
