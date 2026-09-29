-- Prove2me | solution 1 for Freiman.section14_s0011_records_0800_0864
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:41:42.107056+00:00
-- url     : https://prove2.me/submissions/974304ec-bb2e-4076-a459-44869a6daedf

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
namespace Section14Records_11_800_864
private theorem valid800 : RecordDataValid section14Catalog 11 (⟨330,(0),[11],[2],28⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨28,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],28⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid801 : RecordDataValid section14Catalog 11 (⟨330,(1),[11],[2],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid802 : RecordDataValid section14Catalog 11 (⟨330,(2),[11],[2],925⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨925,[3,7,11,15],929⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid803 : RecordDataValid section14Catalog 11 (⟨330,(3),[11],[2],926⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨926,[3,7,11,15],930⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid804 : RecordDataValid section14Catalog 11 (⟨330,(4),[11],[2],927⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨927,[3,7,11,15],931⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid805 : RecordDataValid section14Catalog 11 (⟨330,(5),[11],[2],928⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨928,[3,7,11,15],932⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid806 : RecordDataValid section14Catalog 11 (⟨330,(6),[11],[2],929⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨929,[3,7,11,15],933⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid807 : RecordDataValid section14Catalog 11 (⟨330,(7),[11],[2],929⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨929,[3,7,11,15],933⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid808 : RecordDataValid section14Catalog 11 (⟨330,(8),[11],[2],930⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨930,[3,7,11,15],934⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid809 : RecordDataValid section14Catalog 11 (⟨330,(9),[11],[2],930⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨930,[3,7,11,15],934⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid810 : RecordDataValid section14Catalog 11 (⟨335,(0),[11],[2],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid811 : RecordDataValid section14Catalog 11 (⟨335,(1),[11],[2],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid812 : RecordDataValid section14Catalog 11 (⟨335,(2),[11],[2],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid813 : RecordDataValid section14Catalog 11 (⟨335,(3),[11],[2],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid814 : RecordDataValid section14Catalog 11 (⟨335,(4),[11],[2],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid815 : RecordDataValid section14Catalog 11 (⟨335,(5),[11],[2],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid816 : RecordDataValid section14Catalog 11 (⟨335,(6),[11],[2],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid817 : RecordDataValid section14Catalog 11 (⟨335,(7),[11],[2],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid818 : RecordDataValid section14Catalog 11 (⟨335,(8),[11],[2],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid819 : RecordDataValid section14Catalog 11 (⟨335,(9),[11],[2],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid820 : RecordDataValid section14Catalog 11 (⟨339,(0),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid821 : RecordDataValid section14Catalog 11 (⟨339,(1),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid822 : RecordDataValid section14Catalog 11 (⟨339,(2),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid823 : RecordDataValid section14Catalog 11 (⟨339,(3),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid824 : RecordDataValid section14Catalog 11 (⟨339,(4),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid825 : RecordDataValid section14Catalog 11 (⟨339,(5),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid826 : RecordDataValid section14Catalog 11 (⟨339,(6),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid827 : RecordDataValid section14Catalog 11 (⟨339,(7),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid828 : RecordDataValid section14Catalog 11 (⟨339,(8),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid829 : RecordDataValid section14Catalog 11 (⟨339,(9),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid830 : RecordDataValid section14Catalog 11 (⟨343,(0),[11],[2],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid831 : RecordDataValid section14Catalog 11 (⟨343,(1),[11],[2],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid832 : RecordDataValid section14Catalog 11 (⟨343,(2),[11],[2],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid833 : RecordDataValid section14Catalog 11 (⟨343,(3),[11],[2],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid834 : RecordDataValid section14Catalog 11 (⟨343,(4),[11],[2],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid835 : RecordDataValid section14Catalog 11 (⟨343,(5),[11],[2],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid836 : RecordDataValid section14Catalog 11 (⟨343,(6),[11],[2],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid837 : RecordDataValid section14Catalog 11 (⟨343,(7),[11],[2],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid838 : RecordDataValid section14Catalog 11 (⟨343,(8),[11],[2],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid839 : RecordDataValid section14Catalog 11 (⟨343,(9),[11],[2],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid840 : RecordDataValid section14Catalog 11 (⟨347,(0),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid841 : RecordDataValid section14Catalog 11 (⟨347,(1),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid842 : RecordDataValid section14Catalog 11 (⟨347,(2),[11],[2],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid843 : RecordDataValid section14Catalog 11 (⟨347,(3),[11],[2],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid844 : RecordDataValid section14Catalog 11 (⟨349,(0),[11],[2],121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨121,[1,2,3,5,6,7,9,10,11],121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid845 : RecordDataValid section14Catalog 11 (⟨349,(1),[11],[2],122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨122,[1,2,3,5,6,7,9,10,11],122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid846 : RecordDataValid section14Catalog 11 (⟨349,(2),[11],[2],931⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨931,[3,7,11],935⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid847 : RecordDataValid section14Catalog 11 (⟨349,(3),[11],[2],124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨124,[1,2,3,5,6,7,9,10,11],124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid848 : RecordDataValid section14Catalog 11 (⟨352,(0),[11],[2],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid849 : RecordDataValid section14Catalog 11 (⟨352,(1),[11],[2],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid850 : RecordDataValid section14Catalog 11 (⟨352,(2),[11],[2],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid851 : RecordDataValid section14Catalog 11 (⟨352,(3),[11],[2],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid852 : RecordDataValid section14Catalog 11 (⟨352,(4),[11],[2],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid853 : RecordDataValid section14Catalog 11 (⟨352,(5),[11],[2],1536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1536,[6,7,9,10,11],1541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid854 : RecordDataValid section14Catalog 11 (⟨352,(6),[11],[2],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid855 : RecordDataValid section14Catalog 11 (⟨352,(7),[11],[2],1538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1538,[6,7,9,10,11],1543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid856 : RecordDataValid section14Catalog 11 (⟨352,(8),[11],[2],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid857 : RecordDataValid section14Catalog 11 (⟨352,(9),[11],[2],1536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1536,[6,7,9,10,11],1541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid858 : RecordDataValid section14Catalog 11 (⟨356,(0),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid859 : RecordDataValid section14Catalog 11 (⟨356,(1),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid860 : RecordDataValid section14Catalog 11 (⟨356,(2),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid861 : RecordDataValid section14Catalog 11 (⟨356,(3),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid862 : RecordDataValid section14Catalog 11 (⟨356,(4),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid863 : RecordDataValid section14Catalog 11 (⟨356,(5),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 800).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 800).take 64 = [⟨330,(0),[11],[2],28⟩,⟨330,(1),[11],[2],30⟩,⟨330,(2),[11],[2],925⟩,⟨330,(3),[11],[2],926⟩,⟨330,(4),[11],[2],927⟩,⟨330,(5),[11],[2],928⟩,⟨330,(6),[11],[2],929⟩,⟨330,(7),[11],[2],929⟩,⟨330,(8),[11],[2],930⟩,⟨330,(9),[11],[2],930⟩,⟨335,(0),[11],[2],106⟩,⟨335,(1),[11],[2],106⟩,⟨335,(2),[11],[2],107⟩,⟨335,(3),[11],[2],107⟩,⟨335,(4),[11],[2],108⟩,⟨335,(5),[11],[2],110⟩,⟨335,(6),[11],[2],108⟩,⟨335,(7),[11],[2],112⟩,⟨335,(8),[11],[2],108⟩,⟨335,(9),[11],[2],110⟩,⟨339,(0),[11],[2],2⟩,⟨339,(1),[11],[2],2⟩,⟨339,(2),[11],[2],2⟩,⟨339,(3),[11],[2],2⟩,⟨339,(4),[11],[2],2⟩,⟨339,(5),[11],[2],2⟩,⟨339,(6),[11],[2],2⟩,⟨339,(7),[11],[2],2⟩,⟨339,(8),[11],[2],2⟩,⟨339,(9),[11],[2],2⟩,⟨343,(0),[11],[2],113⟩,⟨343,(1),[11],[2],113⟩,⟨343,(2),[11],[2],114⟩,⟨343,(3),[11],[2],114⟩,⟨343,(4),[11],[2],115⟩,⟨343,(5),[11],[2],117⟩,⟨343,(6),[11],[2],115⟩,⟨343,(7),[11],[2],119⟩,⟨343,(8),[11],[2],115⟩,⟨343,(9),[11],[2],117⟩,⟨347,(0),[11],[2],2⟩,⟨347,(1),[11],[2],2⟩,⟨347,(2),[11],[2],159⟩,⟨347,(3),[11],[2],99⟩,⟨349,(0),[11],[2],121⟩,⟨349,(1),[11],[2],122⟩,⟨349,(2),[11],[2],931⟩,⟨349,(3),[11],[2],124⟩,⟨352,(0),[11],[2],1532⟩,⟨352,(1),[11],[2],1532⟩,⟨352,(2),[11],[2],1533⟩,⟨352,(3),[11],[2],1533⟩,⟨352,(4),[11],[2],1534⟩,⟨352,(5),[11],[2],1536⟩,⟨352,(6),[11],[2],1534⟩,⟨352,(7),[11],[2],1538⟩,⟨352,(8),[11],[2],1534⟩,⟨352,(9),[11],[2],1536⟩,⟨356,(0),[11],[2],2⟩,⟨356,(1),[11],[2],2⟩,⟨356,(2),[11],[2],2⟩,⟨356,(3),[11],[2],2⟩,⟨356,(4),[11],[2],2⟩,⟨356,(5),[11],[2],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid800
  · exact recordValid_of_data section14Catalog 11 _ hnum valid801
  · exact recordValid_of_data section14Catalog 11 _ hnum valid802
  · exact recordValid_of_data section14Catalog 11 _ hnum valid803
  · exact recordValid_of_data section14Catalog 11 _ hnum valid804
  · exact recordValid_of_data section14Catalog 11 _ hnum valid805
  · exact recordValid_of_data section14Catalog 11 _ hnum valid806
  · exact recordValid_of_data section14Catalog 11 _ hnum valid807
  · exact recordValid_of_data section14Catalog 11 _ hnum valid808
  · exact recordValid_of_data section14Catalog 11 _ hnum valid809
  · exact recordValid_of_data section14Catalog 11 _ hnum valid810
  · exact recordValid_of_data section14Catalog 11 _ hnum valid811
  · exact recordValid_of_data section14Catalog 11 _ hnum valid812
  · exact recordValid_of_data section14Catalog 11 _ hnum valid813
  · exact recordValid_of_data section14Catalog 11 _ hnum valid814
  · exact recordValid_of_data section14Catalog 11 _ hnum valid815
  · exact recordValid_of_data section14Catalog 11 _ hnum valid816
  · exact recordValid_of_data section14Catalog 11 _ hnum valid817
  · exact recordValid_of_data section14Catalog 11 _ hnum valid818
  · exact recordValid_of_data section14Catalog 11 _ hnum valid819
  · exact recordValid_of_data section14Catalog 11 _ hnum valid820
  · exact recordValid_of_data section14Catalog 11 _ hnum valid821
  · exact recordValid_of_data section14Catalog 11 _ hnum valid822
  · exact recordValid_of_data section14Catalog 11 _ hnum valid823
  · exact recordValid_of_data section14Catalog 11 _ hnum valid824
  · exact recordValid_of_data section14Catalog 11 _ hnum valid825
  · exact recordValid_of_data section14Catalog 11 _ hnum valid826
  · exact recordValid_of_data section14Catalog 11 _ hnum valid827
  · exact recordValid_of_data section14Catalog 11 _ hnum valid828
  · exact recordValid_of_data section14Catalog 11 _ hnum valid829
  · exact recordValid_of_data section14Catalog 11 _ hnum valid830
  · exact recordValid_of_data section14Catalog 11 _ hnum valid831
  · exact recordValid_of_data section14Catalog 11 _ hnum valid832
  · exact recordValid_of_data section14Catalog 11 _ hnum valid833
  · exact recordValid_of_data section14Catalog 11 _ hnum valid834
  · exact recordValid_of_data section14Catalog 11 _ hnum valid835
  · exact recordValid_of_data section14Catalog 11 _ hnum valid836
  · exact recordValid_of_data section14Catalog 11 _ hnum valid837
  · exact recordValid_of_data section14Catalog 11 _ hnum valid838
  · exact recordValid_of_data section14Catalog 11 _ hnum valid839
  · exact recordValid_of_data section14Catalog 11 _ hnum valid840
  · exact recordValid_of_data section14Catalog 11 _ hnum valid841
  · exact recordValid_of_data section14Catalog 11 _ hnum valid842
  · exact recordValid_of_data section14Catalog 11 _ hnum valid843
  · exact recordValid_of_data section14Catalog 11 _ hnum valid844
  · exact recordValid_of_data section14Catalog 11 _ hnum valid845
  · exact recordValid_of_data section14Catalog 11 _ hnum valid846
  · exact recordValid_of_data section14Catalog 11 _ hnum valid847
  · exact recordValid_of_data section14Catalog 11 _ hnum valid848
  · exact recordValid_of_data section14Catalog 11 _ hnum valid849
  · exact recordValid_of_data section14Catalog 11 _ hnum valid850
  · exact recordValid_of_data section14Catalog 11 _ hnum valid851
  · exact recordValid_of_data section14Catalog 11 _ hnum valid852
  · exact recordValid_of_data section14Catalog 11 _ hnum valid853
  · exact recordValid_of_data section14Catalog 11 _ hnum valid854
  · exact recordValid_of_data section14Catalog 11 _ hnum valid855
  · exact recordValid_of_data section14Catalog 11 _ hnum valid856
  · exact recordValid_of_data section14Catalog 11 _ hnum valid857
  · exact recordValid_of_data section14Catalog 11 _ hnum valid858
  · exact recordValid_of_data section14Catalog 11 _ hnum valid859
  · exact recordValid_of_data section14Catalog 11 _ hnum valid860
  · exact recordValid_of_data section14Catalog 11 _ hnum valid861
  · exact recordValid_of_data section14Catalog 11 _ hnum valid862
  · exact recordValid_of_data section14Catalog 11 _ hnum valid863
end Section14Records_11_800_864

#print axioms solution
