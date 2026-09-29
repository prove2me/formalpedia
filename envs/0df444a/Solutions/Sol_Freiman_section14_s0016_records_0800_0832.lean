-- Prove2me | solution 1 for Freiman.section14_s0016_records_0800_0832
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:04:32.520554+00:00
-- url     : https://prove2.me/submissions/2c2d44c2-9e13-403b-bf40-fe397f9e89f2

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
namespace Section14Records_16_800_832
private theorem valid800 : RecordDataValid section14Catalog 16 (⟨139,(19),[4,8,12,16],[10],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid801 : RecordDataValid section14Catalog 16 (⟨140,(0),[4,8,12,16],[10],563⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨563,[1,4,5,6,8,9,10,12,13,16],564⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid802 : RecordDataValid section14Catalog 16 (⟨140,(1),[4,8,12,16],[10],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid803 : RecordDataValid section14Catalog 16 (⟨140,(2),[4,8,12,16],[10],565⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨565,[1,4,5,6,8,9,10,12,13,16],566⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid804 : RecordDataValid section14Catalog 16 (⟨140,(3),[4,8,12,16],[10],1270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1270,[4,5,8,9,12,16],1274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid805 : RecordDataValid section14Catalog 16 (⟨140,(4),[4,8,12,16],[10],566⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨566,[1,4,5,6,8,9,10,12,13,16],567⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid806 : RecordDataValid section14Catalog 16 (⟨140,(5),[4,8,12,16],[10],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid807 : RecordDataValid section14Catalog 16 (⟨140,(6),[4,16],[10],567⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨567,[1,4,5,6,10,13,16],568⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid808 : RecordDataValid section14Catalog 16 (⟨140,(7),[4,16],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid809 : RecordDataValid section14Catalog 16 (⟨142,(0),[4,8,12,16],[10],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid810 : RecordDataValid section14Catalog 16 (⟨142,(1),[4,8,12,16],[10],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid811 : RecordDataValid section14Catalog 16 (⟨142,(2),[4,8,12,16],[10],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid812 : RecordDataValid section14Catalog 16 (⟨142,(3),[4,8,12,16],[10],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid813 : RecordDataValid section14Catalog 16 (⟨142,(4),[4,8,12,16],[10],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid814 : RecordDataValid section14Catalog 16 (⟨142,(5),[4,8,12,16],[10],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid815 : RecordDataValid section14Catalog 16 (⟨142,(6),[4,8,12,16],[10],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid816 : RecordDataValid section14Catalog 16 (⟨142,(7),[4,8,12,16],[10],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid817 : RecordDataValid section14Catalog 16 (⟨142,(8),[4,8,12,16],[10],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid818 : RecordDataValid section14Catalog 16 (⟨142,(9),[4,8,12,16],[10],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid819 : RecordDataValid section14Catalog 16 (⟨142,(10),[4,8,12,16],[10],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid820 : RecordDataValid section14Catalog 16 (⟨142,(11),[4,8,12,16],[10],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid821 : RecordDataValid section14Catalog 16 (⟨142,(12),[4,8,12,16],[10],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid822 : RecordDataValid section14Catalog 16 (⟨142,(13),[4,8,12,16],[10],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid823 : RecordDataValid section14Catalog 16 (⟨142,(14),[4,8,12,16],[10],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid824 : RecordDataValid section14Catalog 16 (⟨142,(15),[4,8,12,16],[10],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid825 : RecordDataValid section14Catalog 16 (⟨143,(0),[4,8,12,16],[10],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid826 : RecordDataValid section14Catalog 16 (⟨143,(1),[4,8,12,16],[10],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid827 : RecordDataValid section14Catalog 16 (⟨143,(2),[4,8,12,16],[10],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid828 : RecordDataValid section14Catalog 16 (⟨143,(3),[4,8,12,16],[10],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid829 : RecordDataValid section14Catalog 16 (⟨143,(4),[4,8,12,16],[10],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid830 : RecordDataValid section14Catalog 16 (⟨143,(5),[4,8,12,16],[10],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid831 : RecordDataValid section14Catalog 16 (⟨143,(6),[4,8,12,16],[10],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 800).take 32 = [⟨139,(19),[4,8,12,16],[10],558⟩,⟨140,(0),[4,8,12,16],[10],563⟩,⟨140,(1),[4,8,12,16],[10],564⟩,⟨140,(2),[4,8,12,16],[10],565⟩,⟨140,(3),[4,8,12,16],[10],1270⟩,⟨140,(4),[4,8,12,16],[10],566⟩,⟨140,(5),[4,8,12,16],[10],564⟩,⟨140,(6),[4,16],[10],567⟩,⟨140,(7),[4,16],[10],547⟩,⟨142,(0),[4,8,12,16],[10],568⟩,⟨142,(1),[4,8,12,16],[10],569⟩,⟨142,(2),[4,8,12,16],[10],570⟩,⟨142,(3),[4,8,12,16],[10],571⟩,⟨142,(4),[4,8,12,16],[10],572⟩,⟨142,(5),[4,8,12,16],[10],573⟩,⟨142,(6),[4,8,12,16],[10],573⟩,⟨142,(7),[4,8,12,16],[10],573⟩,⟨142,(8),[4,8,12,16],[10],574⟩,⟨142,(9),[4,8,12,16],[10],575⟩,⟨142,(10),[4,8,12,16],[10],575⟩,⟨142,(11),[4,8,12,16],[10],575⟩,⟨142,(12),[4,8,12,16],[10],576⟩,⟨142,(13),[4,8,12,16],[10],577⟩,⟨142,(14),[4,8,12,16],[10],577⟩,⟨142,(15),[4,8,12,16],[10],577⟩,⟨143,(0),[4,8,12,16],[10],578⟩,⟨143,(1),[4,8,12,16],[10],579⟩,⟨143,(2),[4,8,12,16],[10],580⟩,⟨143,(3),[4,8,12,16],[10],581⟩,⟨143,(4),[4,8,12,16],[10],582⟩,⟨143,(5),[4,8,12,16],[10],583⟩,⟨143,(6),[4,8,12,16],[10],584⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid800
  · exact recordValid_of_data section14Catalog 16 _ hnum valid801
  · exact recordValid_of_data section14Catalog 16 _ hnum valid802
  · exact recordValid_of_data section14Catalog 16 _ hnum valid803
  · exact recordValid_of_data section14Catalog 16 _ hnum valid804
  · exact recordValid_of_data section14Catalog 16 _ hnum valid805
  · exact recordValid_of_data section14Catalog 16 _ hnum valid806
  · exact recordValid_of_data section14Catalog 16 _ hnum valid807
  · exact recordValid_of_data section14Catalog 16 _ hnum valid808
  · exact recordValid_of_data section14Catalog 16 _ hnum valid809
  · exact recordValid_of_data section14Catalog 16 _ hnum valid810
  · exact recordValid_of_data section14Catalog 16 _ hnum valid811
  · exact recordValid_of_data section14Catalog 16 _ hnum valid812
  · exact recordValid_of_data section14Catalog 16 _ hnum valid813
  · exact recordValid_of_data section14Catalog 16 _ hnum valid814
  · exact recordValid_of_data section14Catalog 16 _ hnum valid815
  · exact recordValid_of_data section14Catalog 16 _ hnum valid816
  · exact recordValid_of_data section14Catalog 16 _ hnum valid817
  · exact recordValid_of_data section14Catalog 16 _ hnum valid818
  · exact recordValid_of_data section14Catalog 16 _ hnum valid819
  · exact recordValid_of_data section14Catalog 16 _ hnum valid820
  · exact recordValid_of_data section14Catalog 16 _ hnum valid821
  · exact recordValid_of_data section14Catalog 16 _ hnum valid822
  · exact recordValid_of_data section14Catalog 16 _ hnum valid823
  · exact recordValid_of_data section14Catalog 16 _ hnum valid824
  · exact recordValid_of_data section14Catalog 16 _ hnum valid825
  · exact recordValid_of_data section14Catalog 16 _ hnum valid826
  · exact recordValid_of_data section14Catalog 16 _ hnum valid827
  · exact recordValid_of_data section14Catalog 16 _ hnum valid828
  · exact recordValid_of_data section14Catalog 16 _ hnum valid829
  · exact recordValid_of_data section14Catalog 16 _ hnum valid830
  · exact recordValid_of_data section14Catalog 16 _ hnum valid831
end Section14Records_16_800_832

#print axioms solution
