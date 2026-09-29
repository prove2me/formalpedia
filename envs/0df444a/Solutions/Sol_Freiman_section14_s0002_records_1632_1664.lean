-- Prove2me | solution 1 for Freiman.section14_s0002_records_1632_1664
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T06:33:03.944868+00:00
-- url     : https://prove2.me/submissions/bb2ed468-60af-41ed-a84e-8dfed1c123bc

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
namespace Section14Records_2_1632_1664
private theorem valid1632 : RecordDataValid section14Catalog 2 (⟨80,(5),[1,2,5,6,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1633 : RecordDataValid section14Catalog 2 (⟨80,(7),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1634 : RecordDataValid section14Catalog 2 (⟨80,(7),[1,2,6,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1635 : RecordDataValid section14Catalog 2 (⟨80,(8),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1636 : RecordDataValid section14Catalog 2 (⟨80,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1637 : RecordDataValid section14Catalog 2 (⟨80,(9),[1,2],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1638 : RecordDataValid section14Catalog 2 (⟨80,(9),[1,2,5,6],[150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1639 : RecordDataValid section14Catalog 2 (⟨80,(15),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1640 : RecordDataValid section14Catalog 2 (⟨80,(15),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1641 : RecordDataValid section14Catalog 2 (⟨80,(16),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1642 : RecordDataValid section14Catalog 2 (⟨80,(16),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1643 : RecordDataValid section14Catalog 2 (⟨80,(17),[1,2,5,6,13,14],[190],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1644 : RecordDataValid section14Catalog 2 (⟨80,(17),[1,2,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1645 : RecordDataValid section14Catalog 2 (⟨80,(19),[1,2],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1646 : RecordDataValid section14Catalog 2 (⟨80,(19),[1,2,5,6,13,14],[190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1647 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1648 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1649 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,9,10,13,14],[5],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1650 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1651 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1652 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1653 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1654 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1655 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[130,134],389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1656 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[146],390⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨390,[1,2,3,5,6,7,13,14,15],391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1657 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1658 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[150],392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨392,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1659 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[174],628⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨628,[1,2,3,5,6,7,13,14,15],629⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1660 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[186],629⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨629,[1,2,4,5,6,8,9,10,12,13,14,16],630⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1661 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1662 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1663 : RecordDataValid section14Catalog 2 (⟨82,(-1),[1,2,13,14],[131,135],389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1632).take 32 = [⟨80,(5),[1,2,5,6,14],[190],3⟩,⟨80,(7),[1,2,5,6],[150],3⟩,⟨80,(7),[1,2,6,14],[190],3⟩,⟨80,(8),[1,2,5,6],[150],3⟩,⟨80,(8),[1,2,5,6,13,14],[190],3⟩,⟨80,(9),[1,2],[190],3⟩,⟨80,(9),[1,2,5,6],[150],143⟩,⟨80,(15),[1,2,5,6],[150],3⟩,⟨80,(15),[1,2,5,6,13,14],[190],3⟩,⟨80,(16),[1,2,5,6],[150],3⟩,⟨80,(16),[1,2,5,6,13,14],[190],3⟩,⟨80,(17),[1,2,5,6,13,14],[190],48⟩,⟨80,(17),[1,2,6],[150],3⟩,⟨80,(19),[1,2],[150],3⟩,⟨80,(19),[1,2,5,6,13,14],[190],143⟩,⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩,⟨82,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨82,(-1),[1,2,5,6,9,10,13,14],[5],386⟩,⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨82,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨82,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],386⟩,⟨82,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],387⟩,⟨82,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],388⟩,⟨82,(-1),[1,2,5,6,13,14],[130,134],389⟩,⟨82,(-1),[1,2,5,6,13,14],[146],390⟩,⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩,⟨82,(-1),[1,2,5,6,13,14],[150],392⟩,⟨82,(-1),[1,2,5,6,13,14],[174],628⟩,⟨82,(-1),[1,2,5,6,13,14],[186],629⟩,⟨82,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],630⟩,⟨82,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨82,(-1),[1,2,13,14],[131,135],389⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1632
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1633
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1634
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1635
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1636
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1637
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1638
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1639
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1640
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1641
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1642
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1643
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1644
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1645
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1646
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1647
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1648
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1649
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1650
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1651
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1652
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1653
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1654
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1655
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1656
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1657
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1658
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1659
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1660
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1661
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1662
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1663
end Section14Records_2_1632_1664

#print axioms solution
