-- Prove2me | solution 1 for Freiman.section14_s0002_records_1664_1696
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T06:35:08.161164+00:00
-- url     : https://prove2.me/submissions/791e08f5-ebe8-4445-9bbc-a77b0ce0ff2b

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
namespace Section14Records_2_1664_1696
private theorem valid1664 : RecordDataValid section14Catalog 2 (⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1665 : RecordDataValid section14Catalog 2 (⟨82,(-1),[2,6,9,10,14],[16,20],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1666 : RecordDataValid section14Catalog 2 (⟨82,(-1),[2,6,14],[40,44,56,60],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1667 : RecordDataValid section14Catalog 2 (⟨82,(-1),[2,6,14],[211,215,235,239,251,255],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1668 : RecordDataValid section14Catalog 2 (⟨82,(-1),[2,6,14],[190],629⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨629,[1,2,4,5,6,8,9,10,12,13,14,16],630⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1669 : RecordDataValid section14Catalog 2 (⟨82,(-1),[2,14],[194,195,198,199],389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1670 : RecordDataValid section14Catalog 2 (⟨82,(-1),[2,14],[170],919⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨919,[2,3,14,15],922⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1671 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1672 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1673 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,9,10,13,14],[5],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1674 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1675 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1676 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1677 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1678 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1679 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[130,134],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1680 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[146],635⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨635,[1,2,3,5,6,7,13,14,15],636⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1681 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1682 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[150],637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1683 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[186],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1684 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1685 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1686 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,5,6,14],[190],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1687 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,13,14],[131,135],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1688 : RecordDataValid section14Catalog 2 (⟨153,(-1),[1,2,13,14],[174],878⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨878,[1,2,13,14],879⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1689 : RecordDataValid section14Catalog 2 (⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1690 : RecordDataValid section14Catalog 2 (⟨153,(-1),[2,6,9,10,14],[16,20],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1691 : RecordDataValid section14Catalog 2 (⟨153,(-1),[2,6,14],[40,44,56,60],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1692 : RecordDataValid section14Catalog 2 (⟨153,(-1),[2,6,14],[211,215,235,239,251,255],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1693 : RecordDataValid section14Catalog 2 (⟨153,(-1),[2,14],[194,195,198,199],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1694 : RecordDataValid section14Catalog 2 (⟨155,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1695 : RecordDataValid section14Catalog 2 (⟨155,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1664).take 32 = [⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩,⟨82,(-1),[2,6,9,10,14],[16,20],387⟩,⟨82,(-1),[2,6,14],[40,44,56,60],387⟩,⟨82,(-1),[2,6,14],[211,215,235,239,251,255],391⟩,⟨82,(-1),[2,6,14],[190],629⟩,⟨82,(-1),[2,14],[194,195,198,199],389⟩,⟨82,(-1),[2,14],[170],919⟩,⟨153,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],631⟩,⟨153,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨153,(-1),[1,2,5,6,9,10,13,14],[5],631⟩,⟨153,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨153,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨153,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],631⟩,⟨153,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],632⟩,⟨153,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],633⟩,⟨153,(-1),[1,2,5,6,13,14],[130,134],634⟩,⟨153,(-1),[1,2,5,6,13,14],[146],635⟩,⟨153,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],636⟩,⟨153,(-1),[1,2,5,6,13,14],[150],637⟩,⟨153,(-1),[1,2,5,6,13,14],[186],879⟩,⟨153,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],880⟩,⟨153,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨153,(-1),[1,2,5,6,14],[190],879⟩,⟨153,(-1),[1,2,13,14],[131,135],634⟩,⟨153,(-1),[1,2,13,14],[174],878⟩,⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩,⟨153,(-1),[2,6,9,10,14],[16,20],632⟩,⟨153,(-1),[2,6,14],[40,44,56,60],632⟩,⟨153,(-1),[2,6,14],[211,215,235,239,251,255],636⟩,⟨153,(-1),[2,14],[194,195,198,199],634⟩,⟨155,(0),[1,2,5,6,13,14],[170],3⟩,⟨155,(1),[1,2,5,6,13,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1664
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1665
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1666
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1667
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1668
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1669
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1670
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1671
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1672
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1673
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1674
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1675
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1676
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1677
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1678
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1679
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1680
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1681
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1682
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1683
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1684
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1685
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1686
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1687
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1688
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1689
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1690
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1691
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1692
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1693
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1694
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1695
end Section14Records_2_1664_1696

#print axioms solution
