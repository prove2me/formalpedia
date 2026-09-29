-- Prove2me | solution 1 for Freiman.section14_s0004_records_0896_0928
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:24:08.007287+00:00
-- url     : https://prove2.me/submissions/3c9b0525-fcaa-42b1-be99-18cab8dd6c94

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
namespace Section14Records_4_896_928
private theorem valid896 : RecordDataValid section14Catalog 4 (⟨124,(14),[4,8,12,16],[10],493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨493,[1,4,5,6,8,9,10,12,13,16],494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid897 : RecordDataValid section14Catalog 4 (⟨124,(15),[4,8,12,16],[10],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid898 : RecordDataValid section14Catalog 4 (⟨127,(0),[4,8,12,16],[10],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid899 : RecordDataValid section14Catalog 4 (⟨127,(1),[4,8,12,16],[10],495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid900 : RecordDataValid section14Catalog 4 (⟨127,(2),[4,8,12,16],[10],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid901 : RecordDataValid section14Catalog 4 (⟨127,(3),[4,8,12,16],[10],496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid902 : RecordDataValid section14Catalog 4 (⟨127,(4),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid903 : RecordDataValid section14Catalog 4 (⟨127,(5),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid904 : RecordDataValid section14Catalog 4 (⟨127,(6),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid905 : RecordDataValid section14Catalog 4 (⟨127,(7),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid906 : RecordDataValid section14Catalog 4 (⟨127,(8),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid907 : RecordDataValid section14Catalog 4 (⟨127,(9),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid908 : RecordDataValid section14Catalog 4 (⟨127,(10),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid909 : RecordDataValid section14Catalog 4 (⟨127,(11),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid910 : RecordDataValid section14Catalog 4 (⟨127,(12),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid911 : RecordDataValid section14Catalog 4 (⟨127,(13),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid912 : RecordDataValid section14Catalog 4 (⟨127,(14),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid913 : RecordDataValid section14Catalog 4 (⟨127,(15),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid914 : RecordDataValid section14Catalog 4 (⟨129,(0),[4,8,12],[10],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid915 : RecordDataValid section14Catalog 4 (⟨129,(1),[4,8,12],[10],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid916 : RecordDataValid section14Catalog 4 (⟨129,(2),[4,8,12],[10],502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨502,[1,4,5,6,8,9,10,12],503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid917 : RecordDataValid section14Catalog 4 (⟨129,(3),[4,8,12],[10],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid918 : RecordDataValid section14Catalog 4 (⟨129,(4),[4,8,12],[10],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid919 : RecordDataValid section14Catalog 4 (⟨129,(5),[4,8,12],[10],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid920 : RecordDataValid section14Catalog 4 (⟨129,(6),[4,8,12],[10],504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨504,[1,4,5,6,8,9,10,12],505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid921 : RecordDataValid section14Catalog 4 (⟨129,(7),[4,8,12],[10],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid922 : RecordDataValid section14Catalog 4 (⟨129,(8),[4,8,12],[10],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid923 : RecordDataValid section14Catalog 4 (⟨129,(9),[4,8,12],[10],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid924 : RecordDataValid section14Catalog 4 (⟨129,(10),[4,8,12],[10],502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨502,[1,4,5,6,8,9,10,12],503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid925 : RecordDataValid section14Catalog 4 (⟨129,(11),[4,8,12],[10],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid926 : RecordDataValid section14Catalog 4 (⟨129,(12),[4,8,12],[10],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid927 : RecordDataValid section14Catalog 4 (⟨129,(13),[4,8,12],[10],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 896).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 896).take 32 = [⟨124,(14),[4,8,12,16],[10],493⟩,⟨124,(15),[4,8,12,16],[10],491⟩,⟨127,(0),[4,8,12,16],[10],494⟩,⟨127,(1),[4,8,12,16],[10],495⟩,⟨127,(2),[4,8,12,16],[10],494⟩,⟨127,(3),[4,8,12,16],[10],496⟩,⟨127,(4),[4,8,12,16],[10],497⟩,⟨127,(5),[4,8,12,16],[10],497⟩,⟨127,(6),[4,8,12,16],[10],497⟩,⟨127,(7),[4,8,12,16],[10],497⟩,⟨127,(8),[4,8,12,16],[10],498⟩,⟨127,(9),[4,8,12,16],[10],498⟩,⟨127,(10),[4,8,12,16],[10],498⟩,⟨127,(11),[4,8,12,16],[10],498⟩,⟨127,(12),[4,8,12,16],[10],499⟩,⟨127,(13),[4,8,12,16],[10],499⟩,⟨127,(14),[4,8,12,16],[10],499⟩,⟨127,(15),[4,8,12,16],[10],499⟩,⟨129,(0),[4,8,12],[10],500⟩,⟨129,(1),[4,8,12],[10],501⟩,⟨129,(2),[4,8,12],[10],502⟩,⟨129,(3),[4,8,12],[10],503⟩,⟨129,(4),[4,8,12],[10],500⟩,⟨129,(5),[4,8,12],[10],501⟩,⟨129,(6),[4,8,12],[10],504⟩,⟨129,(7),[4,8,12],[10],503⟩,⟨129,(8),[4,8,12],[10],500⟩,⟨129,(9),[4,8,12],[10],501⟩,⟨129,(10),[4,8,12],[10],502⟩,⟨129,(11),[4,8,12],[10],503⟩,⟨129,(12),[4,8,12],[10],500⟩,⟨129,(13),[4,8,12],[10],501⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid896
  · exact recordValid_of_data section14Catalog 4 _ hnum valid897
  · exact recordValid_of_data section14Catalog 4 _ hnum valid898
  · exact recordValid_of_data section14Catalog 4 _ hnum valid899
  · exact recordValid_of_data section14Catalog 4 _ hnum valid900
  · exact recordValid_of_data section14Catalog 4 _ hnum valid901
  · exact recordValid_of_data section14Catalog 4 _ hnum valid902
  · exact recordValid_of_data section14Catalog 4 _ hnum valid903
  · exact recordValid_of_data section14Catalog 4 _ hnum valid904
  · exact recordValid_of_data section14Catalog 4 _ hnum valid905
  · exact recordValid_of_data section14Catalog 4 _ hnum valid906
  · exact recordValid_of_data section14Catalog 4 _ hnum valid907
  · exact recordValid_of_data section14Catalog 4 _ hnum valid908
  · exact recordValid_of_data section14Catalog 4 _ hnum valid909
  · exact recordValid_of_data section14Catalog 4 _ hnum valid910
  · exact recordValid_of_data section14Catalog 4 _ hnum valid911
  · exact recordValid_of_data section14Catalog 4 _ hnum valid912
  · exact recordValid_of_data section14Catalog 4 _ hnum valid913
  · exact recordValid_of_data section14Catalog 4 _ hnum valid914
  · exact recordValid_of_data section14Catalog 4 _ hnum valid915
  · exact recordValid_of_data section14Catalog 4 _ hnum valid916
  · exact recordValid_of_data section14Catalog 4 _ hnum valid917
  · exact recordValid_of_data section14Catalog 4 _ hnum valid918
  · exact recordValid_of_data section14Catalog 4 _ hnum valid919
  · exact recordValid_of_data section14Catalog 4 _ hnum valid920
  · exact recordValid_of_data section14Catalog 4 _ hnum valid921
  · exact recordValid_of_data section14Catalog 4 _ hnum valid922
  · exact recordValid_of_data section14Catalog 4 _ hnum valid923
  · exact recordValid_of_data section14Catalog 4 _ hnum valid924
  · exact recordValid_of_data section14Catalog 4 _ hnum valid925
  · exact recordValid_of_data section14Catalog 4 _ hnum valid926
  · exact recordValid_of_data section14Catalog 4 _ hnum valid927
end Section14Records_4_896_928

#print axioms solution
