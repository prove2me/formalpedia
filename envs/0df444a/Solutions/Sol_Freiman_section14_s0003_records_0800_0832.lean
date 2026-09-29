-- Prove2me | solution 1 for Freiman.section14_s0003_records_0800_0832
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T12:37:44.169686+00:00
-- url     : https://prove2.me/submissions/44c35477-2fc5-422a-a425-8f26f398f130

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
namespace Section14Records_3_800_832
private theorem valid800 : RecordDataValid section14Catalog 3 (⟨178,(5),[3,7],[11],986⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨986,[3,5,6,7],990⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid801 : RecordDataValid section14Catalog 3 (⟨178,(5),[3,7,15],[10],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid802 : RecordDataValid section14Catalog 3 (⟨178,(6),[3,7],[11],986⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨986,[3,5,6,7],990⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid803 : RecordDataValid section14Catalog 3 (⟨178,(6),[3,7,15],[10],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid804 : RecordDataValid section14Catalog 3 (⟨178,(7),[3,7],[11],986⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨986,[3,5,6,7],990⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid805 : RecordDataValid section14Catalog 3 (⟨178,(7),[3,7,15],[10],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid806 : RecordDataValid section14Catalog 3 (⟨178,(8),[3,7],[11],987⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨987,[3,5,6,7],991⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid807 : RecordDataValid section14Catalog 3 (⟨178,(8),[3,7,15],[10],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid808 : RecordDataValid section14Catalog 3 (⟨178,(9),[3,7],[11],987⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨987,[3,5,6,7],991⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid809 : RecordDataValid section14Catalog 3 (⟨178,(9),[3,7,15],[10],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid810 : RecordDataValid section14Catalog 3 (⟨178,(10),[3,7],[11],987⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨987,[3,5,6,7],991⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid811 : RecordDataValid section14Catalog 3 (⟨178,(10),[3,7,15],[10],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid812 : RecordDataValid section14Catalog 3 (⟨178,(11),[3,7],[11],987⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨987,[3,5,6,7],991⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid813 : RecordDataValid section14Catalog 3 (⟨178,(11),[3,7,15],[10],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid814 : RecordDataValid section14Catalog 3 (⟨178,(12),[3,7],[11],988⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨988,[3,5,6,7],992⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid815 : RecordDataValid section14Catalog 3 (⟨178,(12),[3,7,15],[10],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid816 : RecordDataValid section14Catalog 3 (⟨178,(13),[3,7],[11],988⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨988,[3,5,6,7],992⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid817 : RecordDataValid section14Catalog 3 (⟨178,(13),[3,7,15],[10],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid818 : RecordDataValid section14Catalog 3 (⟨178,(14),[3,7],[11],988⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨988,[3,5,6,7],992⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid819 : RecordDataValid section14Catalog 3 (⟨178,(14),[3,7,15],[10],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid820 : RecordDataValid section14Catalog 3 (⟨178,(15),[3,7],[11],988⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨988,[3,5,6,7],992⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid821 : RecordDataValid section14Catalog 3 (⟨178,(15),[3,7,15],[10],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid822 : RecordDataValid section14Catalog 3 (⟨180,(0),[3,4,8,12,15,16],[10],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid823 : RecordDataValid section14Catalog 3 (⟨180,(0),[3,7],[11],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid824 : RecordDataValid section14Catalog 3 (⟨180,(1),[3,4,8,12,15,16],[10],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid825 : RecordDataValid section14Catalog 3 (⟨180,(1),[3,7],[11],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid826 : RecordDataValid section14Catalog 3 (⟨180,(2),[3,4,8,12,15,16],[10],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid827 : RecordDataValid section14Catalog 3 (⟨180,(2),[3,7],[11],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid828 : RecordDataValid section14Catalog 3 (⟨180,(3),[3,4,8,12,15,16],[10],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid829 : RecordDataValid section14Catalog 3 (⟨180,(3),[3,7],[11],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid830 : RecordDataValid section14Catalog 3 (⟨180,(4),[3,4,8,12,15,16],[10],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid831 : RecordDataValid section14Catalog 3 (⟨180,(4),[3,7],[11],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 800).take 32 = [⟨178,(5),[3,7],[11],986⟩,⟨178,(5),[3,7,15],[10],663⟩,⟨178,(6),[3,7],[11],986⟩,⟨178,(6),[3,7,15],[10],663⟩,⟨178,(7),[3,7],[11],986⟩,⟨178,(7),[3,7,15],[10],663⟩,⟨178,(8),[3,7],[11],987⟩,⟨178,(8),[3,7,15],[10],664⟩,⟨178,(9),[3,7],[11],987⟩,⟨178,(9),[3,7,15],[10],664⟩,⟨178,(10),[3,7],[11],987⟩,⟨178,(10),[3,7,15],[10],664⟩,⟨178,(11),[3,7],[11],987⟩,⟨178,(11),[3,7,15],[10],664⟩,⟨178,(12),[3,7],[11],988⟩,⟨178,(12),[3,7,15],[10],665⟩,⟨178,(13),[3,7],[11],988⟩,⟨178,(13),[3,7,15],[10],665⟩,⟨178,(14),[3,7],[11],988⟩,⟨178,(14),[3,7,15],[10],665⟩,⟨178,(15),[3,7],[11],988⟩,⟨178,(15),[3,7,15],[10],665⟩,⟨180,(0),[3,4,8,12,15,16],[10],666⟩,⟨180,(0),[3,7],[11],666⟩,⟨180,(1),[3,4,8,12,15,16],[10],667⟩,⟨180,(1),[3,7],[11],667⟩,⟨180,(2),[3,4,8,12,15,16],[10],668⟩,⟨180,(2),[3,7],[11],668⟩,⟨180,(3),[3,4,8,12,15,16],[10],669⟩,⟨180,(3),[3,7],[11],669⟩,⟨180,(4),[3,4,8,12,15,16],[10],666⟩,⟨180,(4),[3,7],[11],666⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid800
  · exact recordValid_of_data section14Catalog 3 _ hnum valid801
  · exact recordValid_of_data section14Catalog 3 _ hnum valid802
  · exact recordValid_of_data section14Catalog 3 _ hnum valid803
  · exact recordValid_of_data section14Catalog 3 _ hnum valid804
  · exact recordValid_of_data section14Catalog 3 _ hnum valid805
  · exact recordValid_of_data section14Catalog 3 _ hnum valid806
  · exact recordValid_of_data section14Catalog 3 _ hnum valid807
  · exact recordValid_of_data section14Catalog 3 _ hnum valid808
  · exact recordValid_of_data section14Catalog 3 _ hnum valid809
  · exact recordValid_of_data section14Catalog 3 _ hnum valid810
  · exact recordValid_of_data section14Catalog 3 _ hnum valid811
  · exact recordValid_of_data section14Catalog 3 _ hnum valid812
  · exact recordValid_of_data section14Catalog 3 _ hnum valid813
  · exact recordValid_of_data section14Catalog 3 _ hnum valid814
  · exact recordValid_of_data section14Catalog 3 _ hnum valid815
  · exact recordValid_of_data section14Catalog 3 _ hnum valid816
  · exact recordValid_of_data section14Catalog 3 _ hnum valid817
  · exact recordValid_of_data section14Catalog 3 _ hnum valid818
  · exact recordValid_of_data section14Catalog 3 _ hnum valid819
  · exact recordValid_of_data section14Catalog 3 _ hnum valid820
  · exact recordValid_of_data section14Catalog 3 _ hnum valid821
  · exact recordValid_of_data section14Catalog 3 _ hnum valid822
  · exact recordValid_of_data section14Catalog 3 _ hnum valid823
  · exact recordValid_of_data section14Catalog 3 _ hnum valid824
  · exact recordValid_of_data section14Catalog 3 _ hnum valid825
  · exact recordValid_of_data section14Catalog 3 _ hnum valid826
  · exact recordValid_of_data section14Catalog 3 _ hnum valid827
  · exact recordValid_of_data section14Catalog 3 _ hnum valid828
  · exact recordValid_of_data section14Catalog 3 _ hnum valid829
  · exact recordValid_of_data section14Catalog 3 _ hnum valid830
  · exact recordValid_of_data section14Catalog 3 _ hnum valid831
end Section14Records_3_800_832

#print axioms solution
