-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_1984_2112
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:58:11.640695+00:00
-- url     : https://prove2.me/submissions/dd8936da-61b7-4064-a958-ae209a8e7b74

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1984_2016
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1984_2016
private theorem valid1984 : RecordDataValid section14Catalog 13 (⟨155,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1985 : RecordDataValid section14Catalog 13 (⟨155,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1986 : RecordDataValid section14Catalog 13 (⟨155,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1987 : RecordDataValid section14Catalog 13 (⟨155,(10),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1988 : RecordDataValid section14Catalog 13 (⟨155,(11),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1989 : RecordDataValid section14Catalog 13 (⟨155,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1990 : RecordDataValid section14Catalog 13 (⟨155,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1991 : RecordDataValid section14Catalog 13 (⟨155,(14),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1992 : RecordDataValid section14Catalog 13 (⟨155,(15),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1993 : RecordDataValid section14Catalog 13 (⟨155,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1994 : RecordDataValid section14Catalog 13 (⟨155,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1995 : RecordDataValid section14Catalog 13 (⟨155,(18),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1996 : RecordDataValid section14Catalog 13 (⟨155,(19),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1997 : RecordDataValid section14Catalog 13 (⟨155,(20),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1998 : RecordDataValid section14Catalog 13 (⟨155,(21),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1999 : RecordDataValid section14Catalog 13 (⟨155,(22),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2000 : RecordDataValid section14Catalog 13 (⟨155,(23),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2001 : RecordDataValid section14Catalog 13 (⟨155,(24),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2002 : RecordDataValid section14Catalog 13 (⟨157,(0),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2003 : RecordDataValid section14Catalog 13 (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2004 : RecordDataValid section14Catalog 13 (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2005 : RecordDataValid section14Catalog 13 (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2006 : RecordDataValid section14Catalog 13 (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2007 : RecordDataValid section14Catalog 13 (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2008 : RecordDataValid section14Catalog 13 (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2009 : RecordDataValid section14Catalog 13 (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2010 : RecordDataValid section14Catalog 13 (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2011 : RecordDataValid section14Catalog 13 (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2012 : RecordDataValid section14Catalog 13 (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2013 : RecordDataValid section14Catalog 13 (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2014 : RecordDataValid section14Catalog 13 (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2015 : RecordDataValid section14Catalog 13 (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1984_2016 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1984).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1984).take 32 = [⟨155,(7),[1,2,5,6,13,14],[170],3⟩,⟨155,(8),[1,2,5,6,13,14],[170],3⟩,⟨155,(9),[1,2,5,6,13,14],[170],3⟩,⟨155,(10),[1,2,5,6,13,14],[170],3⟩,⟨155,(11),[1,2,5,6,13,14],[170],3⟩,⟨155,(12),[1,2,5,6,13,14],[170],3⟩,⟨155,(13),[1,2,5,6,13,14],[170],3⟩,⟨155,(14),[1,2,5,6,13,14],[170],3⟩,⟨155,(15),[1,2,5,6,13,14],[170],3⟩,⟨155,(16),[1,2,5,6,13,14],[170],3⟩,⟨155,(17),[1,2,5,6,13,14],[170],3⟩,⟨155,(18),[1,2,5,6,13,14],[170],3⟩,⟨155,(19),[1,2,5,6,13,14],[170],3⟩,⟨155,(20),[1,2,5,6,13,14],[170],3⟩,⟨155,(21),[1,2,5,6,13,14],[170],3⟩,⟨155,(22),[1,2,5,6,13,14],[170],3⟩,⟨155,(23),[1,2,5,6,13,14],[170],3⟩,⟨155,(24),[1,2,5,6,13,14],[170],3⟩,⟨157,(0),[1,2,5,6,13,14],[170],10⟩,⟨157,(1),[1,2,5,6,13,14],[170],393⟩,⟨157,(2),[1,2,5,6,13,14],[170],394⟩,⟨157,(3),[1,2,5,6,13,14],[170],395⟩,⟨157,(4),[1,2,5,6,13,14],[170],396⟩,⟨157,(5),[1,2,5,6,13,14],[170],10⟩,⟨157,(6),[1,2,5,6,13,14],[170],393⟩,⟨157,(7),[1,2,5,6,13,14],[170],394⟩,⟨157,(8),[1,2,5,6,13,14],[170],395⟩,⟨157,(9),[1,2,5,6,13,14],[170],396⟩,⟨157,(10),[1,2,5,6,13,14],[170],18⟩,⟨157,(11),[1,2,5,6,13,14],[170],397⟩,⟨157,(12),[1,2,5,6,13,14],[170],397⟩,⟨157,(13),[1,2,5,6,13,14],[170],397⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1984
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1985
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1986
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1987
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1988
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1989
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1990
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1991
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1992
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1993
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1994
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1995
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1996
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1997
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1998
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1999
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2000
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2001
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2002
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2003
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2004
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2005
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2006
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2007
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2008
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2009
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2010
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2011
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2012
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2013
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2014
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2015
end Section14Records_13_1984_2016

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1984_2016


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2016_2048
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2016_2048
private theorem valid2016 : RecordDataValid section14Catalog 13 (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2017 : RecordDataValid section14Catalog 13 (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2018 : RecordDataValid section14Catalog 13 (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2019 : RecordDataValid section14Catalog 13 (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2020 : RecordDataValid section14Catalog 13 (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2021 : RecordDataValid section14Catalog 13 (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2022 : RecordDataValid section14Catalog 13 (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2023 : RecordDataValid section14Catalog 13 (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2024 : RecordDataValid section14Catalog 13 (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2025 : RecordDataValid section14Catalog 13 (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2026 : RecordDataValid section14Catalog 13 (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2027 : RecordDataValid section14Catalog 13 (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2028 : RecordDataValid section14Catalog 13 (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2029 : RecordDataValid section14Catalog 13 (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2030 : RecordDataValid section14Catalog 13 (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2031 : RecordDataValid section14Catalog 13 (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2032 : RecordDataValid section14Catalog 13 (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2033 : RecordDataValid section14Catalog 13 (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2034 : RecordDataValid section14Catalog 13 (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2035 : RecordDataValid section14Catalog 13 (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2036 : RecordDataValid section14Catalog 13 (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2037 : RecordDataValid section14Catalog 13 (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2038 : RecordDataValid section14Catalog 13 (⟨160,(11),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2039 : RecordDataValid section14Catalog 13 (⟨160,(12),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2040 : RecordDataValid section14Catalog 13 (⟨160,(13),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2041 : RecordDataValid section14Catalog 13 (⟨160,(14),[1,2,5,6,13,14],[170],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2042 : RecordDataValid section14Catalog 13 (⟨160,(15),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2043 : RecordDataValid section14Catalog 13 (⟨163,(0),[1,2,5,6,13,14],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2044 : RecordDataValid section14Catalog 13 (⟨163,(1),[1,2,5,6,13,14],[170],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2045 : RecordDataValid section14Catalog 13 (⟨163,(2),[1,2,5,6,13,14],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2046 : RecordDataValid section14Catalog 13 (⟨163,(3),[1,2,5,6,13,14],[170],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2047 : RecordDataValid section14Catalog 13 (⟨163,(4),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2016_2048 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2016).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2016).take 32 = [⟨157,(14),[1,2,5,6,13,14],[170],396⟩,⟨157,(15),[1,2,5,6,13,14],[170],21⟩,⟨157,(16),[1,2,5,6,13,14],[170],398⟩,⟨157,(17),[1,2,5,6,13,14],[170],398⟩,⟨157,(18),[1,2,5,6,13,14],[170],398⟩,⟨157,(19),[1,2,5,6,13,14],[170],398⟩,⟨157,(20),[1,2,5,6,13,14],[170],24⟩,⟨157,(21),[1,2,5,6,13,14],[170],399⟩,⟨157,(22),[1,2,5,6,13,14],[170],399⟩,⟨157,(23),[1,2,5,6,13,14],[170],399⟩,⟨157,(24),[1,2,5,6,13,14],[170],399⟩,⟨160,(0),[1,2,5,6,13,14],[170],638⟩,⟨160,(1),[1,2,5,6,13,14],[170],639⟩,⟨160,(2),[1,2,5,6,13,14],[170],640⟩,⟨160,(3),[1,2,5,6,13,14],[170],641⟩,⟨160,(4),[1,2,5,6,13,14],[170],638⟩,⟨160,(5),[1,2,5,6,13,14],[170],639⟩,⟨160,(6),[1,2,5,6,13,14],[170],642⟩,⟨160,(7),[1,2,5,6,13,14],[170],641⟩,⟨160,(8),[1,2,5,6,13,14],[170],638⟩,⟨160,(9),[1,2,5,6,13,14],[170],639⟩,⟨160,(10),[1,2,5,6,13,14],[170],640⟩,⟨160,(11),[1,2,5,6,13,14],[170],641⟩,⟨160,(12),[1,2,5,6,13,14],[170],638⟩,⟨160,(13),[1,2,5,6,13,14],[170],639⟩,⟨160,(14),[1,2,5,6,13,14],[170],643⟩,⟨160,(15),[1,2,5,6,13,14],[170],641⟩,⟨163,(0),[1,2,5,6,13,14],[170],406⟩,⟨163,(1),[1,2,5,6,13,14],[170],407⟩,⟨163,(2),[1,2,5,6,13,14],[170],406⟩,⟨163,(3),[1,2,5,6,13,14],[170],408⟩,⟨163,(4),[1,2,5,6,13,14],[170],409⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2016
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2017
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2018
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2019
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2020
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2021
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2022
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2023
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2024
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2025
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2026
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2027
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2028
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2029
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2030
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2031
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2032
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2033
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2034
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2035
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2036
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2037
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2038
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2039
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2040
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2041
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2042
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2043
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2044
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2045
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2046
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2047
end Section14Records_13_2016_2048

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2016_2048


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2048_2080
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2048_2080
private theorem valid2048 : RecordDataValid section14Catalog 13 (⟨163,(5),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2049 : RecordDataValid section14Catalog 13 (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2050 : RecordDataValid section14Catalog 13 (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2051 : RecordDataValid section14Catalog 13 (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2052 : RecordDataValid section14Catalog 13 (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2053 : RecordDataValid section14Catalog 13 (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2054 : RecordDataValid section14Catalog 13 (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2055 : RecordDataValid section14Catalog 13 (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2056 : RecordDataValid section14Catalog 13 (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2057 : RecordDataValid section14Catalog 13 (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2058 : RecordDataValid section14Catalog 13 (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2059 : RecordDataValid section14Catalog 13 (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2060 : RecordDataValid section14Catalog 13 (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2061 : RecordDataValid section14Catalog 13 (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2062 : RecordDataValid section14Catalog 13 (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2063 : RecordDataValid section14Catalog 13 (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2064 : RecordDataValid section14Catalog 13 (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2065 : RecordDataValid section14Catalog 13 (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2066 : RecordDataValid section14Catalog 13 (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2067 : RecordDataValid section14Catalog 13 (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2068 : RecordDataValid section14Catalog 13 (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨647,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],648⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2069 : RecordDataValid section14Catalog 13 (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2070 : RecordDataValid section14Catalog 13 (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2071 : RecordDataValid section14Catalog 13 (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2072 : RecordDataValid section14Catalog 13 (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2073 : RecordDataValid section14Catalog 13 (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2074 : RecordDataValid section14Catalog 13 (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2075 : RecordDataValid section14Catalog 13 (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2076 : RecordDataValid section14Catalog 13 (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2077 : RecordDataValid section14Catalog 13 (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2078 : RecordDataValid section14Catalog 13 (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2079 : RecordDataValid section14Catalog 13 (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2048_2080 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2048).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2048).take 32 = [⟨163,(5),[1,2,5,6,13,14],[170],409⟩,⟨163,(6),[1,2,5,6,13,14],[170],409⟩,⟨163,(7),[1,2,5,6,13,14],[170],409⟩,⟨163,(8),[1,2,5,6,13,14],[170],410⟩,⟨163,(9),[1,2,5,6,13,14],[170],410⟩,⟨163,(10),[1,2,5,6,13,14],[170],410⟩,⟨163,(11),[1,2,5,6,13,14],[170],410⟩,⟨163,(12),[1,2,5,6,13,14],[170],411⟩,⟨163,(13),[1,2,5,6,13,14],[170],411⟩,⟨163,(14),[1,2,5,6,13,14],[170],411⟩,⟨163,(15),[1,2,5,6,13,14],[170],411⟩,⟨166,(0),[1,2,5,6,13,14],[170],644⟩,⟨166,(1),[1,2,5,6,13,14],[170],644⟩,⟨166,(2),[1,2,5,6,13,14],[170],644⟩,⟨166,(3),[1,2,5,6,13,14],[170],644⟩,⟨166,(4),[1,2,5,6,13,14],[170],645⟩,⟨166,(5),[1,2,5,6,13,14],[170],645⟩,⟨166,(6),[1,2,5,6,13,14],[170],645⟩,⟨166,(7),[1,2,5,6,13,14],[170],645⟩,⟨166,(8),[1,2,5,6,13,14],[170],646⟩,⟨166,(9),[1,2,5,6,13,14],[170],647⟩,⟨166,(10),[1,2,5,6,13,14],[170],646⟩,⟨166,(11),[1,2,5,6,13,14],[170],648⟩,⟨166,(12),[1,2,5,6,13,14],[170],649⟩,⟨166,(13),[1,2,5,6,13,14],[170],649⟩,⟨166,(14),[1,2,5,6,13,14],[170],649⟩,⟨166,(15),[1,2,5,6,13,14],[170],649⟩,⟨167,(0),[1,2,5,6,13,14],[170],418⟩,⟨167,(1),[1,2,5,6,13,14],[170],419⟩,⟨167,(2),[1,2,5,6,13,14],[170],420⟩,⟨167,(3),[1,2,5,6,13,14],[170],421⟩,⟨167,(4),[1,2,5,6,13,14],[170],422⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2048
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2049
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2050
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2051
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2052
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2053
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2054
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2055
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2056
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2057
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2058
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2059
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2060
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2061
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2062
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2063
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2064
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2065
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2066
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2067
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2068
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2069
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2070
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2071
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2072
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2073
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2074
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2075
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2076
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2077
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2078
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2079
end Section14Records_13_2048_2080

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2048_2080


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2080_2112
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2080_2112
private theorem valid2080 : RecordDataValid section14Catalog 13 (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2081 : RecordDataValid section14Catalog 13 (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2082 : RecordDataValid section14Catalog 13 (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2083 : RecordDataValid section14Catalog 13 (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2084 : RecordDataValid section14Catalog 13 (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2085 : RecordDataValid section14Catalog 13 (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2086 : RecordDataValid section14Catalog 13 (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2087 : RecordDataValid section14Catalog 13 (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2088 : RecordDataValid section14Catalog 13 (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2089 : RecordDataValid section14Catalog 13 (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2090 : RecordDataValid section14Catalog 13 (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2091 : RecordDataValid section14Catalog 13 (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2092 : RecordDataValid section14Catalog 13 (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2093 : RecordDataValid section14Catalog 13 (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2094 : RecordDataValid section14Catalog 13 (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2095 : RecordDataValid section14Catalog 13 (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2096 : RecordDataValid section14Catalog 13 (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2097 : RecordDataValid section14Catalog 13 (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2098 : RecordDataValid section14Catalog 13 (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2099 : RecordDataValid section14Catalog 13 (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2100 : RecordDataValid section14Catalog 13 (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2101 : RecordDataValid section14Catalog 13 (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2102 : RecordDataValid section14Catalog 13 (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2103 : RecordDataValid section14Catalog 13 (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2104 : RecordDataValid section14Catalog 13 (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2105 : RecordDataValid section14Catalog 13 (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2106 : RecordDataValid section14Catalog 13 (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2107 : RecordDataValid section14Catalog 13 (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2108 : RecordDataValid section14Catalog 13 (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2109 : RecordDataValid section14Catalog 13 (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2110 : RecordDataValid section14Catalog 13 (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2111 : RecordDataValid section14Catalog 13 (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2080_2112 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2080).take 32 = [⟨167,(5),[1,2,5,6,13,14],[170],419⟩,⟨167,(6),[1,2,5,6,13,14],[170],420⟩,⟨167,(7),[1,2,5,6,13,14],[170],421⟩,⟨167,(8),[1,2,5,6,13,14],[170],418⟩,⟨167,(9),[1,2,5,6,13,14],[170],419⟩,⟨167,(10),[1,2,5,6,13,14],[170],420⟩,⟨167,(11),[1,2,5,6,13,14],[170],421⟩,⟨167,(12),[1,2,5,6,13,14],[170],423⟩,⟨167,(13),[1,2,5,6,13,14],[170],419⟩,⟨167,(14),[1,2,5,6,13,14],[170],420⟩,⟨167,(15),[1,2,5,6,13,14],[170],421⟩,⟨171,(0),[1,2,5,6,13,14],[170],650⟩,⟨171,(1),[1,2,5,6,13,14],[170],651⟩,⟨171,(2),[1,2,5,6,13,14],[170],652⟩,⟨171,(3),[1,2,5,6,13,14],[170],653⟩,⟨172,(0),[1,2,5,6,13,14],[170],428⟩,⟨172,(1),[1,2,5,6,13,14],[170],429⟩,⟨172,(2),[1,2,5,6,13,14],[170],430⟩,⟨172,(3),[1,2,5,6,13,14],[170],431⟩,⟨172,(4),[1,2,5,6,13,14],[170],432⟩,⟨172,(5),[1,2,5,6,13,14],[170],429⟩,⟨172,(6),[1,2,5,6,13,14],[170],430⟩,⟨172,(7),[1,2,5,6,13,14],[170],431⟩,⟨172,(8),[1,2,5,6,13,14],[170],428⟩,⟨172,(9),[1,2,5,6,13,14],[170],429⟩,⟨172,(10),[1,2,5,6,13,14],[170],430⟩,⟨172,(11),[1,2,5,6,13,14],[170],431⟩,⟨172,(12),[1,2,5,6,13,14],[170],433⟩,⟨172,(13),[1,2,5,6,13,14],[170],429⟩,⟨172,(14),[1,2,5,6,13,14],[170],430⟩,⟨172,(15),[1,2,5,6,13,14],[170],431⟩,⟨175,(0),[1,2,5,6,13,14],[170],654⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2080
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2081
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2082
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2083
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2084
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2085
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2086
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2087
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2088
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2089
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2090
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2091
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2092
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2093
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2094
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2095
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2096
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2097
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2098
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2099
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2100
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2101
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2102
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2103
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2104
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2105
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2106
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2107
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2108
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2109
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2110
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2111
end Section14Records_13_2080_2112

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2080_2112

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1984).take 128, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 1984 2048 2112 (by decide) (by decide) (all_of_interval_split P xs 1984 2016 2048 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_1984_2016 hnum) (Freiman.workReverse20260919_s0013_records_2016_2048 hnum)) (all_of_interval_split P xs 2048 2080 2112 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2048_2080 hnum) (Freiman.workReverse20260919_s0013_records_2080_2112 hnum)))

#print axioms solution
