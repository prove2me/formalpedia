-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_0000_0128
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T00:31:21.791608+00:00
-- url     : https://prove2.me/submissions/7a689378-ed42-45d3-9ef4-493d54c5ae5b

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0000_0032
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_0_32
private theorem valid0 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,9,10,13,14],[5],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid5 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid6 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],4⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨4,[1,2,4,5,6,8,9,10,12,13,14,16],4⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid7 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],5⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid8 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[130,134],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid9 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[146],7⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨7,[1,2,3,5,6,7,13,14,15],7⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid10 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],8⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨8,[1,2,4,5,6,8,9,10,12,13,14,16],8⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid11 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[150],9⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨9,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],9⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid12 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[174],54⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨54,[1,2,3,5,6,7,13,14,15],54⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid13 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[186,190],55⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨55,[1,2,4,5,6,8,9,10,12,13,14,16],55⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid14 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],56⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨56,[1,2,3,5,6,7,9,10,11,13,14,15],56⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid15 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid16 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,2,13,14],[131,135],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid17 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid18 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,5,6,13],[194,198],56⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨56,[1,2,3,5,6,7,9,10,11,13,14,15],56⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid19 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,5,9,13],[4],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid20 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,5,13],[16,20,40,44,56,60],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid21 : RecordDataValid section14Catalog 1 (⟨1,(-1),[1,5,13],[195,199,211,215,235,239,251,255],56⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨56,[1,2,3,5,6,7,9,10,11,13,14,15],56⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid22 : RecordDataValid section14Catalog 1 (⟨3,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid23 : RecordDataValid section14Catalog 1 (⟨3,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid24 : RecordDataValid section14Catalog 1 (⟨3,(2),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid25 : RecordDataValid section14Catalog 1 (⟨3,(3),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid26 : RecordDataValid section14Catalog 1 (⟨3,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid27 : RecordDataValid section14Catalog 1 (⟨3,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid28 : RecordDataValid section14Catalog 1 (⟨3,(6),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid29 : RecordDataValid section14Catalog 1 (⟨3,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid30 : RecordDataValid section14Catalog 1 (⟨3,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid31 : RecordDataValid section14Catalog 1 (⟨3,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0000_0032 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 0).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 0).take 32 = [⟨1,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],1⟩,⟨1,(-1),[1,2,5,6,9,10,13,14],[5],1⟩,⟨1,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨1,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],1⟩,⟨1,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨1,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨1,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],4⟩,⟨1,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],5⟩,⟨1,(-1),[1,2,5,6,13,14],[130,134],6⟩,⟨1,(-1),[1,2,5,6,13,14],[146],7⟩,⟨1,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],8⟩,⟨1,(-1),[1,2,5,6,13,14],[150],9⟩,⟨1,(-1),[1,2,5,6,13,14],[174],54⟩,⟨1,(-1),[1,2,5,6,13,14],[186,190],55⟩,⟨1,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],56⟩,⟨1,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨1,(-1),[1,2,13,14],[131,135],6⟩,⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩,⟨1,(-1),[1,5,6,13],[194,198],56⟩,⟨1,(-1),[1,5,9,13],[4],1⟩,⟨1,(-1),[1,5,13],[16,20,40,44,56,60],1⟩,⟨1,(-1),[1,5,13],[195,199,211,215,235,239,251,255],56⟩,⟨3,(0),[1,2,5,6,13,14],[170],3⟩,⟨3,(1),[1,2,5,6,13,14],[170],3⟩,⟨3,(2),[1,2,5,6,13,14],[170],3⟩,⟨3,(3),[1,2,5,6,13,14],[170],3⟩,⟨3,(4),[1,2,5,6,13,14],[170],3⟩,⟨3,(5),[1,2,5,6,13,14],[170],3⟩,⟨3,(6),[1,2,5,6,13,14],[170],3⟩,⟨3,(7),[1,2,5,6,13,14],[170],3⟩,⟨3,(8),[1,2,5,6,13,14],[170],3⟩,⟨3,(9),[1,2,5,6,13,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid0
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3
  · exact recordValid_of_data section14Catalog 1 _ hnum valid4
  · exact recordValid_of_data section14Catalog 1 _ hnum valid5
  · exact recordValid_of_data section14Catalog 1 _ hnum valid6
  · exact recordValid_of_data section14Catalog 1 _ hnum valid7
  · exact recordValid_of_data section14Catalog 1 _ hnum valid8
  · exact recordValid_of_data section14Catalog 1 _ hnum valid9
  · exact recordValid_of_data section14Catalog 1 _ hnum valid10
  · exact recordValid_of_data section14Catalog 1 _ hnum valid11
  · exact recordValid_of_data section14Catalog 1 _ hnum valid12
  · exact recordValid_of_data section14Catalog 1 _ hnum valid13
  · exact recordValid_of_data section14Catalog 1 _ hnum valid14
  · exact recordValid_of_data section14Catalog 1 _ hnum valid15
  · exact recordValid_of_data section14Catalog 1 _ hnum valid16
  · exact recordValid_of_data section14Catalog 1 _ hnum valid17
  · exact recordValid_of_data section14Catalog 1 _ hnum valid18
  · exact recordValid_of_data section14Catalog 1 _ hnum valid19
  · exact recordValid_of_data section14Catalog 1 _ hnum valid20
  · exact recordValid_of_data section14Catalog 1 _ hnum valid21
  · exact recordValid_of_data section14Catalog 1 _ hnum valid22
  · exact recordValid_of_data section14Catalog 1 _ hnum valid23
  · exact recordValid_of_data section14Catalog 1 _ hnum valid24
  · exact recordValid_of_data section14Catalog 1 _ hnum valid25
  · exact recordValid_of_data section14Catalog 1 _ hnum valid26
  · exact recordValid_of_data section14Catalog 1 _ hnum valid27
  · exact recordValid_of_data section14Catalog 1 _ hnum valid28
  · exact recordValid_of_data section14Catalog 1 _ hnum valid29
  · exact recordValid_of_data section14Catalog 1 _ hnum valid30
  · exact recordValid_of_data section14Catalog 1 _ hnum valid31
end Section14Records_1_0_32

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0000_0032


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0032_0064
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_32_64
private theorem valid32 : RecordDataValid section14Catalog 1 (⟨3,(10),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid33 : RecordDataValid section14Catalog 1 (⟨3,(11),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid34 : RecordDataValid section14Catalog 1 (⟨3,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid35 : RecordDataValid section14Catalog 1 (⟨3,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid36 : RecordDataValid section14Catalog 1 (⟨3,(14),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid37 : RecordDataValid section14Catalog 1 (⟨3,(15),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid38 : RecordDataValid section14Catalog 1 (⟨3,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid39 : RecordDataValid section14Catalog 1 (⟨3,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid40 : RecordDataValid section14Catalog 1 (⟨3,(18),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid41 : RecordDataValid section14Catalog 1 (⟨3,(19),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid42 : RecordDataValid section14Catalog 1 (⟨3,(20),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid43 : RecordDataValid section14Catalog 1 (⟨3,(21),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid44 : RecordDataValid section14Catalog 1 (⟨3,(22),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid45 : RecordDataValid section14Catalog 1 (⟨3,(23),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid46 : RecordDataValid section14Catalog 1 (⟨3,(24),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid47 : RecordDataValid section14Catalog 1 (⟨5,(0),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid48 : RecordDataValid section14Catalog 1 (⟨5,(1),[1,2,5,6,13,14],[170],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid49 : RecordDataValid section14Catalog 1 (⟨5,(2),[1,2,6,13,14],[170],12⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨12,[1,2,3,4,6,7,13,14,15,16],12⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid50 : RecordDataValid section14Catalog 1 (⟨5,(3),[1,2,6,13,14],[170],13⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨13,[1,2,3,4,6,7,13,14,15,16],13⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid51 : RecordDataValid section14Catalog 1 (⟨5,(4),[1,2,6,13,14],[170],14⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨14,[1,2,3,4,6,7,11,13,14,15,16],14⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid52 : RecordDataValid section14Catalog 1 (⟨5,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid53 : RecordDataValid section14Catalog 1 (⟨5,(6),[1,2,5,6,13,14],[170],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid54 : RecordDataValid section14Catalog 1 (⟨5,(7),[1,2,5,6,13,14],[170],15⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨15,[1,2,3,4,5,6,7,8,13,14,15,16],15⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid55 : RecordDataValid section14Catalog 1 (⟨5,(8),[1,2,5,6,13,14],[170],16⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨16,[1,2,3,4,5,6,7,8,13,14,15,16],16⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid56 : RecordDataValid section14Catalog 1 (⟨5,(9),[1,2,5,6,13,14],[170],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid57 : RecordDataValid section14Catalog 1 (⟨5,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid58 : RecordDataValid section14Catalog 1 (⟨5,(11),[1,2,5,6,13,14],[170],19⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨19,[1,2,3,4,5,6,7,8,13,14,15,16],19⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid59 : RecordDataValid section14Catalog 1 (⟨5,(12),[1,2,5,6,13,14],[170],20⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨20,[1,2,3,4,5,6,7,8,13,14,15,16],20⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid60 : RecordDataValid section14Catalog 1 (⟨5,(13),[1,2,5,6,13,14],[170],20⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨20,[1,2,3,4,5,6,7,8,13,14,15,16],20⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid61 : RecordDataValid section14Catalog 1 (⟨5,(14),[1,2,5,6,13,14],[170],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid62 : RecordDataValid section14Catalog 1 (⟨5,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid63 : RecordDataValid section14Catalog 1 (⟨5,(16),[1,2,5,6,13,14],[170],22⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨22,[1,2,3,4,5,6,7,8,13,14,15,16],22⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0032_0064 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 32).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 32).take 32 = [⟨3,(10),[1,2,5,6,13,14],[170],3⟩,⟨3,(11),[1,2,5,6,13,14],[170],3⟩,⟨3,(12),[1,2,5,6,13,14],[170],3⟩,⟨3,(13),[1,2,5,6,13,14],[170],3⟩,⟨3,(14),[1,2,5,6,13,14],[170],3⟩,⟨3,(15),[1,2,5,6,13,14],[170],3⟩,⟨3,(16),[1,2,5,6,13,14],[170],3⟩,⟨3,(17),[1,2,5,6,13,14],[170],3⟩,⟨3,(18),[1,2,5,6,13,14],[170],3⟩,⟨3,(19),[1,2,5,6,13,14],[170],3⟩,⟨3,(20),[1,2,5,6,13,14],[170],3⟩,⟨3,(21),[1,2,5,6,13,14],[170],3⟩,⟨3,(22),[1,2,5,6,13,14],[170],3⟩,⟨3,(23),[1,2,5,6,13,14],[170],3⟩,⟨3,(24),[1,2,5,6,13,14],[170],3⟩,⟨5,(0),[1,2,5,6,13,14],[170],10⟩,⟨5,(1),[1,2,5,6,13,14],[170],11⟩,⟨5,(2),[1,2,6,13,14],[170],12⟩,⟨5,(3),[1,2,6,13,14],[170],13⟩,⟨5,(4),[1,2,6,13,14],[170],14⟩,⟨5,(5),[1,2,5,6,13,14],[170],10⟩,⟨5,(6),[1,2,5,6,13,14],[170],11⟩,⟨5,(7),[1,2,5,6,13,14],[170],15⟩,⟨5,(8),[1,2,5,6,13,14],[170],16⟩,⟨5,(9),[1,2,5,6,13,14],[170],17⟩,⟨5,(10),[1,2,5,6,13,14],[170],18⟩,⟨5,(11),[1,2,5,6,13,14],[170],19⟩,⟨5,(12),[1,2,5,6,13,14],[170],20⟩,⟨5,(13),[1,2,5,6,13,14],[170],20⟩,⟨5,(14),[1,2,5,6,13,14],[170],17⟩,⟨5,(15),[1,2,5,6,13,14],[170],21⟩,⟨5,(16),[1,2,5,6,13,14],[170],22⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid32
  · exact recordValid_of_data section14Catalog 1 _ hnum valid33
  · exact recordValid_of_data section14Catalog 1 _ hnum valid34
  · exact recordValid_of_data section14Catalog 1 _ hnum valid35
  · exact recordValid_of_data section14Catalog 1 _ hnum valid36
  · exact recordValid_of_data section14Catalog 1 _ hnum valid37
  · exact recordValid_of_data section14Catalog 1 _ hnum valid38
  · exact recordValid_of_data section14Catalog 1 _ hnum valid39
  · exact recordValid_of_data section14Catalog 1 _ hnum valid40
  · exact recordValid_of_data section14Catalog 1 _ hnum valid41
  · exact recordValid_of_data section14Catalog 1 _ hnum valid42
  · exact recordValid_of_data section14Catalog 1 _ hnum valid43
  · exact recordValid_of_data section14Catalog 1 _ hnum valid44
  · exact recordValid_of_data section14Catalog 1 _ hnum valid45
  · exact recordValid_of_data section14Catalog 1 _ hnum valid46
  · exact recordValid_of_data section14Catalog 1 _ hnum valid47
  · exact recordValid_of_data section14Catalog 1 _ hnum valid48
  · exact recordValid_of_data section14Catalog 1 _ hnum valid49
  · exact recordValid_of_data section14Catalog 1 _ hnum valid50
  · exact recordValid_of_data section14Catalog 1 _ hnum valid51
  · exact recordValid_of_data section14Catalog 1 _ hnum valid52
  · exact recordValid_of_data section14Catalog 1 _ hnum valid53
  · exact recordValid_of_data section14Catalog 1 _ hnum valid54
  · exact recordValid_of_data section14Catalog 1 _ hnum valid55
  · exact recordValid_of_data section14Catalog 1 _ hnum valid56
  · exact recordValid_of_data section14Catalog 1 _ hnum valid57
  · exact recordValid_of_data section14Catalog 1 _ hnum valid58
  · exact recordValid_of_data section14Catalog 1 _ hnum valid59
  · exact recordValid_of_data section14Catalog 1 _ hnum valid60
  · exact recordValid_of_data section14Catalog 1 _ hnum valid61
  · exact recordValid_of_data section14Catalog 1 _ hnum valid62
  · exact recordValid_of_data section14Catalog 1 _ hnum valid63
end Section14Records_1_32_64

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0032_0064


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0064_0096
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_64_96
private theorem valid64 : RecordDataValid section14Catalog 1 (⟨5,(17),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid65 : RecordDataValid section14Catalog 1 (⟨5,(18),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid66 : RecordDataValid section14Catalog 1 (⟨5,(19),[1,2,5,6,13,14],[170],23⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid67 : RecordDataValid section14Catalog 1 (⟨5,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid68 : RecordDataValid section14Catalog 1 (⟨5,(21),[1,2,5,6,13,14],[170],25⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨25,[1,2,3,4,5,6,7,8,13,14,15,16],25⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid69 : RecordDataValid section14Catalog 1 (⟨5,(22),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid70 : RecordDataValid section14Catalog 1 (⟨5,(23),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid71 : RecordDataValid section14Catalog 1 (⟨5,(24),[1,2,5,6,13,14],[170],26⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid72 : RecordDataValid section14Catalog 1 (⟨9,(0),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid73 : RecordDataValid section14Catalog 1 (⟨9,(1),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid74 : RecordDataValid section14Catalog 1 (⟨9,(2),[1,2,5,6,13,14],[170],28⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨28,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],28⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid75 : RecordDataValid section14Catalog 1 (⟨9,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid76 : RecordDataValid section14Catalog 1 (⟨9,(4),[1,2,5,6,13,14],[170],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid77 : RecordDataValid section14Catalog 1 (⟨9,(5),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid78 : RecordDataValid section14Catalog 1 (⟨9,(6),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid79 : RecordDataValid section14Catalog 1 (⟨9,(7),[1,2,5,6,13,14],[170],31⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨31,[1,2,4,5,6,8,9,10,12,13,14,16],31⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid80 : RecordDataValid section14Catalog 1 (⟨9,(8),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid81 : RecordDataValid section14Catalog 1 (⟨9,(9),[1,2,5,6,13,14],[170],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid82 : RecordDataValid section14Catalog 1 (⟨9,(10),[1,2,5,6,13,14],[170],6⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid83 : RecordDataValid section14Catalog 1 (⟨9,(11),[1,2,5,6,13,14],[170],27⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid84 : RecordDataValid section14Catalog 1 (⟨9,(12),[1,2,5,6,13,14],[170],33⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨33,[1,2,4,5,6,8,9,10,12,13,14,16],33⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid85 : RecordDataValid section14Catalog 1 (⟨9,(13),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid86 : RecordDataValid section14Catalog 1 (⟨9,(14),[1,2,5,6,13,14],[170],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid87 : RecordDataValid section14Catalog 1 (⟨9,(15),[1,2,5,6,13,14],[170],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid88 : RecordDataValid section14Catalog 1 (⟨9,(16),[1,2,5,6,13,14],[170],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid89 : RecordDataValid section14Catalog 1 (⟨9,(17),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid90 : RecordDataValid section14Catalog 1 (⟨9,(18),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid91 : RecordDataValid section14Catalog 1 (⟨9,(19),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid92 : RecordDataValid section14Catalog 1 (⟨9,(20),[1,2,5,6,13,14],[170],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid93 : RecordDataValid section14Catalog 1 (⟨9,(21),[1,2,5,6,13,14],[170],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid94 : RecordDataValid section14Catalog 1 (⟨9,(22),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid95 : RecordDataValid section14Catalog 1 (⟨9,(23),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0064_0096 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 64).take 32 = [⟨5,(17),[1,2,5,6,13,14],[170],23⟩,⟨5,(18),[1,2,5,6,13,14],[170],23⟩,⟨5,(19),[1,2,5,6,13,14],[170],23⟩,⟨5,(20),[1,2,5,6,13,14],[170],24⟩,⟨5,(21),[1,2,5,6,13,14],[170],25⟩,⟨5,(22),[1,2,5,6,13,14],[170],26⟩,⟨5,(23),[1,2,5,6,13,14],[170],26⟩,⟨5,(24),[1,2,5,6,13,14],[170],26⟩,⟨9,(0),[1,2,5,6,13,14],[170],6⟩,⟨9,(1),[1,2,5,6,13,14],[170],27⟩,⟨9,(2),[1,2,5,6,13,14],[170],28⟩,⟨9,(3),[1,2,5,6,13,14],[170],29⟩,⟨9,(4),[1,2,5,6,13,14],[170],30⟩,⟨9,(5),[1,2,5,6,13,14],[170],6⟩,⟨9,(6),[1,2,5,6,13,14],[170],27⟩,⟨9,(7),[1,2,5,6,13,14],[170],31⟩,⟨9,(8),[1,2,5,6,13,14],[170],29⟩,⟨9,(9),[1,2,5,6,13,14],[170],32⟩,⟨9,(10),[1,2,5,6,13,14],[170],6⟩,⟨9,(11),[1,2,5,6,13,14],[170],27⟩,⟨9,(12),[1,2,5,6,13,14],[170],33⟩,⟨9,(13),[1,2,5,6,13,14],[170],29⟩,⟨9,(14),[1,2,5,6,13,14],[170],34⟩,⟨9,(15),[1,2,5,6,13,14],[170],35⟩,⟨9,(16),[1,2,5,6,13,14],[170],36⟩,⟨9,(17),[1,2,5,6,13,14],[170],37⟩,⟨9,(18),[1,2,5,6,13,14],[170],29⟩,⟨9,(19),[1,2,5,6,13,14],[170],37⟩,⟨9,(20),[1,2,5,6,13,14],[170],38⟩,⟨9,(21),[1,2,5,6,13,14],[170],39⟩,⟨9,(22),[1,2,5,6,13,14],[170],40⟩,⟨9,(23),[1,2,5,6,13,14],[170],29⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid64
  · exact recordValid_of_data section14Catalog 1 _ hnum valid65
  · exact recordValid_of_data section14Catalog 1 _ hnum valid66
  · exact recordValid_of_data section14Catalog 1 _ hnum valid67
  · exact recordValid_of_data section14Catalog 1 _ hnum valid68
  · exact recordValid_of_data section14Catalog 1 _ hnum valid69
  · exact recordValid_of_data section14Catalog 1 _ hnum valid70
  · exact recordValid_of_data section14Catalog 1 _ hnum valid71
  · exact recordValid_of_data section14Catalog 1 _ hnum valid72
  · exact recordValid_of_data section14Catalog 1 _ hnum valid73
  · exact recordValid_of_data section14Catalog 1 _ hnum valid74
  · exact recordValid_of_data section14Catalog 1 _ hnum valid75
  · exact recordValid_of_data section14Catalog 1 _ hnum valid76
  · exact recordValid_of_data section14Catalog 1 _ hnum valid77
  · exact recordValid_of_data section14Catalog 1 _ hnum valid78
  · exact recordValid_of_data section14Catalog 1 _ hnum valid79
  · exact recordValid_of_data section14Catalog 1 _ hnum valid80
  · exact recordValid_of_data section14Catalog 1 _ hnum valid81
  · exact recordValid_of_data section14Catalog 1 _ hnum valid82
  · exact recordValid_of_data section14Catalog 1 _ hnum valid83
  · exact recordValid_of_data section14Catalog 1 _ hnum valid84
  · exact recordValid_of_data section14Catalog 1 _ hnum valid85
  · exact recordValid_of_data section14Catalog 1 _ hnum valid86
  · exact recordValid_of_data section14Catalog 1 _ hnum valid87
  · exact recordValid_of_data section14Catalog 1 _ hnum valid88
  · exact recordValid_of_data section14Catalog 1 _ hnum valid89
  · exact recordValid_of_data section14Catalog 1 _ hnum valid90
  · exact recordValid_of_data section14Catalog 1 _ hnum valid91
  · exact recordValid_of_data section14Catalog 1 _ hnum valid92
  · exact recordValid_of_data section14Catalog 1 _ hnum valid93
  · exact recordValid_of_data section14Catalog 1 _ hnum valid94
  · exact recordValid_of_data section14Catalog 1 _ hnum valid95
end Section14Records_1_64_96

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0064_0096


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0096_0128
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_96_128
private theorem valid96 : RecordDataValid section14Catalog 1 (⟨9,(24),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid97 : RecordDataValid section14Catalog 1 (⟨11,(0),[1,2,5,6],[170],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid98 : RecordDataValid section14Catalog 1 (⟨11,(1),[1,2,5,6],[170],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid99 : RecordDataValid section14Catalog 1 (⟨11,(2),[1,2,5,6],[170],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid100 : RecordDataValid section14Catalog 1 (⟨11,(3),[1,2,5,6],[170],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid101 : RecordDataValid section14Catalog 1 (⟨11,(4),[1,2,5,6],[170],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid102 : RecordDataValid section14Catalog 1 (⟨11,(5),[1,2,5,6],[170],45⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨45,[1,2,3,4,5,6,7,8],45⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid103 : RecordDataValid section14Catalog 1 (⟨11,(6),[1,2,5,6],[170],45⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨45,[1,2,3,4,5,6,7,8],45⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid104 : RecordDataValid section14Catalog 1 (⟨11,(7),[1,2,5,6],[170],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid105 : RecordDataValid section14Catalog 1 (⟨11,(8),[1,2,5,6],[170],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid106 : RecordDataValid section14Catalog 1 (⟨11,(9),[1,2,5,6],[170],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid107 : RecordDataValid section14Catalog 1 (⟨11,(10),[1,2,5,6],[170],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid108 : RecordDataValid section14Catalog 1 (⟨11,(11),[1,2,5,6],[170],41⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨41,[1,2,3,4,5,6,7,8],41⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid109 : RecordDataValid section14Catalog 1 (⟨11,(12),[1,2,5,6],[170],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid110 : RecordDataValid section14Catalog 1 (⟨11,(13),[1,2,5,6],[170],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid111 : RecordDataValid section14Catalog 1 (⟨11,(14),[1,2,5,6],[170],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid112 : RecordDataValid section14Catalog 1 (⟨11,(15),[1,2,5,6],[170],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid113 : RecordDataValid section14Catalog 1 (⟨11,(16),[1,2,5,6],[170],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid114 : RecordDataValid section14Catalog 1 (⟨11,(17),[1,2,5,6],[170],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid115 : RecordDataValid section14Catalog 1 (⟨11,(18),[1,2,5,6],[170],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid116 : RecordDataValid section14Catalog 1 (⟨11,(19),[1,2,5,6],[170],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid117 : RecordDataValid section14Catalog 1 (⟨11,(20),[1,2,5,6],[170],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid118 : RecordDataValid section14Catalog 1 (⟨11,(21),[1,2,5,6],[170],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid119 : RecordDataValid section14Catalog 1 (⟨11,(22),[1,2,5,6],[170],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid120 : RecordDataValid section14Catalog 1 (⟨11,(23),[1,2,5,6],[170],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid121 : RecordDataValid section14Catalog 1 (⟨11,(24),[1,2,5,6],[170],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid122 : RecordDataValid section14Catalog 1 (⟨14,(5),[1,2,5,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid123 : RecordDataValid section14Catalog 1 (⟨14,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid124 : RecordDataValid section14Catalog 1 (⟨14,(8),[1,2,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid125 : RecordDataValid section14Catalog 1 (⟨14,(9),[1,2],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid126 : RecordDataValid section14Catalog 1 (⟨14,(15),[1,2,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid127 : RecordDataValid section14Catalog 1 (⟨14,(16),[1,2,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_0096_0128 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 96).take 32 = [⟨9,(24),[1,2,5,6,13,14],[170],40⟩,⟨11,(0),[1,2,5,6],[170],41⟩,⟨11,(1),[1,2,5,6],[170],41⟩,⟨11,(2),[1,2,5,6],[170],42⟩,⟨11,(3),[1,2,5,6],[170],43⟩,⟨11,(4),[1,2,5,6],[170],44⟩,⟨11,(5),[1,2,5,6],[170],45⟩,⟨11,(6),[1,2,5,6],[170],45⟩,⟨11,(7),[1,2,5,6],[170],42⟩,⟨11,(8),[1,2,5,6],[170],43⟩,⟨11,(9),[1,2,5,6],[170],44⟩,⟨11,(10),[1,2,5,6],[170],41⟩,⟨11,(11),[1,2,5,6],[170],41⟩,⟨11,(12),[1,2,5,6],[170],42⟩,⟨11,(13),[1,2,5,6],[170],43⟩,⟨11,(14),[1,2,5,6],[170],44⟩,⟨11,(15),[1,2,5,6],[170],46⟩,⟨11,(16),[1,2,5,6],[170],46⟩,⟨11,(17),[1,2,5,6],[170],42⟩,⟨11,(18),[1,2,5,6],[170],43⟩,⟨11,(19),[1,2,5,6],[170],44⟩,⟨11,(20),[1,2,5,6],[170],47⟩,⟨11,(21),[1,2,5,6],[170],47⟩,⟨11,(22),[1,2,5,6],[170],47⟩,⟨11,(23),[1,2,5,6],[170],43⟩,⟨11,(24),[1,2,5,6],[170],44⟩,⟨14,(5),[1,2,5,6,14],[170],3⟩,⟨14,(7),[1,2,5,6,13,14],[170],3⟩,⟨14,(8),[1,2,6,14],[170],3⟩,⟨14,(9),[1,2],[170],3⟩,⟨14,(15),[1,2,6,14],[170],3⟩,⟨14,(16),[1,2,6,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid96
  · exact recordValid_of_data section14Catalog 1 _ hnum valid97
  · exact recordValid_of_data section14Catalog 1 _ hnum valid98
  · exact recordValid_of_data section14Catalog 1 _ hnum valid99
  · exact recordValid_of_data section14Catalog 1 _ hnum valid100
  · exact recordValid_of_data section14Catalog 1 _ hnum valid101
  · exact recordValid_of_data section14Catalog 1 _ hnum valid102
  · exact recordValid_of_data section14Catalog 1 _ hnum valid103
  · exact recordValid_of_data section14Catalog 1 _ hnum valid104
  · exact recordValid_of_data section14Catalog 1 _ hnum valid105
  · exact recordValid_of_data section14Catalog 1 _ hnum valid106
  · exact recordValid_of_data section14Catalog 1 _ hnum valid107
  · exact recordValid_of_data section14Catalog 1 _ hnum valid108
  · exact recordValid_of_data section14Catalog 1 _ hnum valid109
  · exact recordValid_of_data section14Catalog 1 _ hnum valid110
  · exact recordValid_of_data section14Catalog 1 _ hnum valid111
  · exact recordValid_of_data section14Catalog 1 _ hnum valid112
  · exact recordValid_of_data section14Catalog 1 _ hnum valid113
  · exact recordValid_of_data section14Catalog 1 _ hnum valid114
  · exact recordValid_of_data section14Catalog 1 _ hnum valid115
  · exact recordValid_of_data section14Catalog 1 _ hnum valid116
  · exact recordValid_of_data section14Catalog 1 _ hnum valid117
  · exact recordValid_of_data section14Catalog 1 _ hnum valid118
  · exact recordValid_of_data section14Catalog 1 _ hnum valid119
  · exact recordValid_of_data section14Catalog 1 _ hnum valid120
  · exact recordValid_of_data section14Catalog 1 _ hnum valid121
  · exact recordValid_of_data section14Catalog 1 _ hnum valid122
  · exact recordValid_of_data section14Catalog 1 _ hnum valid123
  · exact recordValid_of_data section14Catalog 1 _ hnum valid124
  · exact recordValid_of_data section14Catalog 1 _ hnum valid125
  · exact recordValid_of_data section14Catalog 1 _ hnum valid126
  · exact recordValid_of_data section14Catalog 1 _ hnum valid127
end Section14Records_1_96_128

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_0096_0128

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 0).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 0 64 128 (by decide) (by decide) (all_of_interval_split P xs 0 32 64 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_0000_0032 hnum) (Freiman.workReverse20260919_s0001_records_0032_0064 hnum)) (all_of_interval_split P xs 64 96 128 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_0064_0096 hnum) (Freiman.workReverse20260919_s0001_records_0096_0128 hnum)))

#print axioms solution
