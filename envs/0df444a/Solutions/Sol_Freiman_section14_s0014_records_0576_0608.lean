-- Prove2me | solution 1 for Freiman.section14_s0014_records_0576_0608
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:32:13.173978+00:00
-- url     : https://prove2.me/submissions/23d59542-7298-458b-b085-f08f6e714df5

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
namespace Section14Records_14_576_608
private theorem valid576 : RecordDataValid section14Catalog 14 (⟨36,(16),[1,2,5,6,13,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid577 : RecordDataValid section14Catalog 14 (⟨36,(16),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid578 : RecordDataValid section14Catalog 14 (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid579 : RecordDataValid section14Catalog 14 (⟨36,(16),[1,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid580 : RecordDataValid section14Catalog 14 (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid581 : RecordDataValid section14Catalog 14 (⟨36,(17),[1,2,13,14],[190],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid582 : RecordDataValid section14Catalog 14 (⟨36,(17),[1,2,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid583 : RecordDataValid section14Catalog 14 (⟨36,(19),[1,2,13,14],[190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid584 : RecordDataValid section14Catalog 14 (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid585 : RecordDataValid section14Catalog 14 (⟨36,(19),[13,14],[147],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid586 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid587 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid588 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,9,10,13,14],[5],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid589 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid590 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid591 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[41,57],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid592 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[45],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid593 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[104,120],67⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨67,[1,2,5,6,13,14],67⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid594 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[105,121],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid595 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[108],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid596 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[109],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid597 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨206,[1,2,5,6,13,14],206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid598 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[175],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid599 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[234,250],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid600 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[238],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid601 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[17,21,61],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid602 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[64,68,80,84,124],247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨247,[1,2,4,5,6,8,9,10,12,13,14,16],247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid603 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[65,69,81,85,125],248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨248,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid604 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[130,134],249⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨249,[1,2,4,5,6,8,9,10,12,13,14,16],249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid605 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[146],250⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨250,[1,2,3,5,6,7,13,14,15],250⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid606 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[147,151,191],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid607 : RecordDataValid section14Catalog 14 (⟨38,(-1),[1,2,5,6,13,14],[210,214,254],340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨340,[1,2,3,5,6,7,9,10,11,13,14,15],341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 14 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 576).take 32 = [⟨36,(16),[1,2,5,6,13,14],[150],3⟩,⟨36,(16),[1,2,13,14],[190],3⟩,⟨36,(16),[1,5,6,13,14],[131,146],3⟩,⟨36,(16),[1,13,14],[147],3⟩,⟨36,(17),[1,2,6,14],[131,146,150],3⟩,⟨36,(17),[1,2,13,14],[190],48⟩,⟨36,(17),[1,2,14],[147],3⟩,⟨36,(19),[1,2,13,14],[190],143⟩,⟨36,(19),[5,6,13,14],[131,146,150],143⟩,⟨36,(19),[13,14],[147],143⟩,⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩,⟨38,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨38,(-1),[1,2,5,6,9,10,13,14],[5],246⟩,⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨38,(-1),[1,2,5,6,13,14],[41,57],60⟩,⟨38,(-1),[1,2,5,6,13,14],[45],61⟩,⟨38,(-1),[1,2,5,6,13,14],[104,120],67⟩,⟨38,(-1),[1,2,5,6,13,14],[105,121],68⟩,⟨38,(-1),[1,2,5,6,13,14],[108],69⟩,⟨38,(-1),[1,2,5,6,13,14],[109],70⟩,⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩,⟨38,(-1),[1,2,5,6,13,14],[175],207⟩,⟨38,(-1),[1,2,5,6,13,14],[234,250],243⟩,⟨38,(-1),[1,2,5,6,13,14],[238],244⟩,⟨38,(-1),[1,2,5,6,13,14],[17,21,61],246⟩,⟨38,(-1),[1,2,5,6,13,14],[64,68,80,84,124],247⟩,⟨38,(-1),[1,2,5,6,13,14],[65,69,81,85,125],248⟩,⟨38,(-1),[1,2,5,6,13,14],[130,134],249⟩,⟨38,(-1),[1,2,5,6,13,14],[146],250⟩,⟨38,(-1),[1,2,5,6,13,14],[147,151,191],251⟩,⟨38,(-1),[1,2,5,6,13,14],[210,214,254],340⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 14 _ hnum valid576
  · exact recordValid_of_data section14Catalog 14 _ hnum valid577
  · exact recordValid_of_data section14Catalog 14 _ hnum valid578
  · exact recordValid_of_data section14Catalog 14 _ hnum valid579
  · exact recordValid_of_data section14Catalog 14 _ hnum valid580
  · exact recordValid_of_data section14Catalog 14 _ hnum valid581
  · exact recordValid_of_data section14Catalog 14 _ hnum valid582
  · exact recordValid_of_data section14Catalog 14 _ hnum valid583
  · exact recordValid_of_data section14Catalog 14 _ hnum valid584
  · exact recordValid_of_data section14Catalog 14 _ hnum valid585
  · exact recordValid_of_data section14Catalog 14 _ hnum valid586
  · exact recordValid_of_data section14Catalog 14 _ hnum valid587
  · exact recordValid_of_data section14Catalog 14 _ hnum valid588
  · exact recordValid_of_data section14Catalog 14 _ hnum valid589
  · exact recordValid_of_data section14Catalog 14 _ hnum valid590
  · exact recordValid_of_data section14Catalog 14 _ hnum valid591
  · exact recordValid_of_data section14Catalog 14 _ hnum valid592
  · exact recordValid_of_data section14Catalog 14 _ hnum valid593
  · exact recordValid_of_data section14Catalog 14 _ hnum valid594
  · exact recordValid_of_data section14Catalog 14 _ hnum valid595
  · exact recordValid_of_data section14Catalog 14 _ hnum valid596
  · exact recordValid_of_data section14Catalog 14 _ hnum valid597
  · exact recordValid_of_data section14Catalog 14 _ hnum valid598
  · exact recordValid_of_data section14Catalog 14 _ hnum valid599
  · exact recordValid_of_data section14Catalog 14 _ hnum valid600
  · exact recordValid_of_data section14Catalog 14 _ hnum valid601
  · exact recordValid_of_data section14Catalog 14 _ hnum valid602
  · exact recordValid_of_data section14Catalog 14 _ hnum valid603
  · exact recordValid_of_data section14Catalog 14 _ hnum valid604
  · exact recordValid_of_data section14Catalog 14 _ hnum valid605
  · exact recordValid_of_data section14Catalog 14 _ hnum valid606
  · exact recordValid_of_data section14Catalog 14 _ hnum valid607
end Section14Records_14_576_608

#print axioms solution
