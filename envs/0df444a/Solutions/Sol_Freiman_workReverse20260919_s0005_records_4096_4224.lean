-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4096_4224
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:38:43.070997+00:00
-- url     : https://prove2.me/submissions/986271b6-9734-4997-a9ac-714acf62f745

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4096_4128
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4096_4128
private theorem valid4096 : RecordDataValid section14Catalog 5 (⟨242,(21),[1,2,5,6],[170],877⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨877,[1,2,4,5,6,8,9,10,12],878⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4097 : RecordDataValid section14Catalog 5 (⟨242,(21),[5,6],[174],877⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨877,[1,2,4,5,6,8,9,10,12],878⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4098 : RecordDataValid section14Catalog 5 (⟨242,(22),[1,2,5,6],[170],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4099 : RecordDataValid section14Catalog 5 (⟨242,(22),[5,6],[174],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4100 : RecordDataValid section14Catalog 5 (⟨242,(23),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4101 : RecordDataValid section14Catalog 5 (⟨242,(23),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4102 : RecordDataValid section14Catalog 5 (⟨242,(24),[1,2,5,6],[170],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4103 : RecordDataValid section14Catalog 5 (⟨242,(24),[5,6],[174],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4104 : RecordDataValid section14Catalog 5 (⟨243,(5),[1,2,5,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4105 : RecordDataValid section14Catalog 5 (⟨243,(5),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4106 : RecordDataValid section14Catalog 5 (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4107 : RecordDataValid section14Catalog 5 (⟨243,(7),[5],[174],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4108 : RecordDataValid section14Catalog 5 (⟨243,(8),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4109 : RecordDataValid section14Catalog 5 (⟨243,(8),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4110 : RecordDataValid section14Catalog 5 (⟨243,(9),[5,6],[174],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4111 : RecordDataValid section14Catalog 5 (⟨243,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4112 : RecordDataValid section14Catalog 5 (⟨243,(15),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4113 : RecordDataValid section14Catalog 5 (⟨243,(15),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4114 : RecordDataValid section14Catalog 5 (⟨243,(16),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4115 : RecordDataValid section14Catalog 5 (⟨243,(16),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4116 : RecordDataValid section14Catalog 5 (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4117 : RecordDataValid section14Catalog 5 (⟨243,(17),[5,6],[174],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4118 : RecordDataValid section14Catalog 5 (⟨243,(19),[2,5,6,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4119 : RecordDataValid section14Catalog 5 (⟨243,(19),[5,6],[174],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4120 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4121 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4122 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4123 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4124 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4125 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4126 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4127 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4096_4128 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4096).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4096).take 32 = [⟨242,(21),[1,2,5,6],[170],877⟩,⟨242,(21),[5,6],[174],877⟩,⟨242,(22),[1,2,5,6],[170],287⟩,⟨242,(22),[5,6],[174],287⟩,⟨242,(23),[1,2,5,6],[170],101⟩,⟨242,(23),[5,6],[174],101⟩,⟨242,(24),[1,2,5,6],[170],287⟩,⟨242,(24),[5,6],[174],287⟩,⟨243,(5),[1,2,5,6,14],[170],3⟩,⟨243,(5),[5,6],[174],3⟩,⟨243,(7),[1,2,5,6,13,14],[170],3⟩,⟨243,(7),[5],[174],48⟩,⟨243,(8),[1,5,6,13,14],[170],3⟩,⟨243,(8),[5,6],[174],3⟩,⟨243,(9),[5,6],[174],143⟩,⟨243,(9),[5,6,13,14],[170],143⟩,⟨243,(15),[5,6],[174],3⟩,⟨243,(15),[5,13],[170],48⟩,⟨243,(16),[1,5,6,13,14],[170],3⟩,⟨243,(16),[5,6],[174],3⟩,⟨243,(17),[1,2,5,6,13,14],[170],48⟩,⟨243,(17),[5,6],[174],48⟩,⟨243,(19),[2,5,6,14],[170],143⟩,⟨243,(19),[5,6],[174],143⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩,⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩,⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩,⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩,⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4096
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4097
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4098
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4099
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4100
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4101
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4102
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4103
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4104
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4105
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4106
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4107
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4108
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4109
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4110
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4111
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4112
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4113
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4114
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4115
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4116
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4117
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4118
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4119
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4120
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4121
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4122
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4123
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4124
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4125
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4126
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4127
end Section14Records_5_4096_4128

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4096_4128


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4128_4160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4128_4160
private theorem valid4128 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[146],885⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨885,[1,2,3,5,6,7,13,14,15],887⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4129 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4130 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[150],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4131 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[174],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4132 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[186],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4133 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4134 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4135 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,2,5,6,14],[190],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4136 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,5,6,13],[194,198],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4137 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,5,9,13],[0,4],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4138 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4139 : RecordDataValid section14Catalog 5 (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4140 : RecordDataValid section14Catalog 5 (⟨245,(-1),[5,6],[131,135],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4141 : RecordDataValid section14Catalog 5 (⟨247,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4142 : RecordDataValid section14Catalog 5 (⟨247,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4143 : RecordDataValid section14Catalog 5 (⟨247,(2),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4144 : RecordDataValid section14Catalog 5 (⟨247,(3),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4145 : RecordDataValid section14Catalog 5 (⟨247,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4146 : RecordDataValid section14Catalog 5 (⟨247,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4147 : RecordDataValid section14Catalog 5 (⟨247,(6),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4148 : RecordDataValid section14Catalog 5 (⟨247,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4149 : RecordDataValid section14Catalog 5 (⟨247,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4150 : RecordDataValid section14Catalog 5 (⟨247,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4151 : RecordDataValid section14Catalog 5 (⟨247,(10),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4152 : RecordDataValid section14Catalog 5 (⟨247,(11),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4153 : RecordDataValid section14Catalog 5 (⟨247,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4154 : RecordDataValid section14Catalog 5 (⟨247,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4155 : RecordDataValid section14Catalog 5 (⟨247,(14),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4156 : RecordDataValid section14Catalog 5 (⟨247,(15),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4157 : RecordDataValid section14Catalog 5 (⟨247,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4158 : RecordDataValid section14Catalog 5 (⟨247,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4159 : RecordDataValid section14Catalog 5 (⟨247,(18),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4128_4160 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4128).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4128).take 32 = [⟨245,(-1),[1,2,5,6,13,14],[146],885⟩,⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩,⟨245,(-1),[1,2,5,6,13,14],[150],887⟩,⟨245,(-1),[1,2,5,6,13,14],[174],908⟩,⟨245,(-1),[1,2,5,6,13,14],[186],909⟩,⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩,⟨245,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨245,(-1),[1,2,5,6,14],[190],909⟩,⟨245,(-1),[1,5,6,13],[194,198],910⟩,⟨245,(-1),[1,5,9,13],[0,4],881⟩,⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩,⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩,⟨245,(-1),[5,6],[131,135],886⟩,⟨247,(0),[1,2,5,6,13,14],[170],3⟩,⟨247,(1),[1,2,5,6,13,14],[170],3⟩,⟨247,(2),[1,2,5,6,13,14],[170],3⟩,⟨247,(3),[1,2,5,6,13,14],[170],3⟩,⟨247,(4),[1,2,5,6,13,14],[170],3⟩,⟨247,(5),[1,2,5,6,13,14],[170],3⟩,⟨247,(6),[1,2,5,6,13,14],[170],3⟩,⟨247,(7),[1,2,5,6,13,14],[170],3⟩,⟨247,(8),[1,2,5,6,13,14],[170],3⟩,⟨247,(9),[1,2,5,6,13,14],[170],3⟩,⟨247,(10),[1,2,5,6,13,14],[170],3⟩,⟨247,(11),[1,2,5,6,13,14],[170],3⟩,⟨247,(12),[1,2,5,6,13,14],[170],3⟩,⟨247,(13),[1,2,5,6,13,14],[170],3⟩,⟨247,(14),[1,2,5,6,13,14],[170],3⟩,⟨247,(15),[1,2,5,6,13,14],[170],3⟩,⟨247,(16),[1,2,5,6,13,14],[170],3⟩,⟨247,(17),[1,2,5,6,13,14],[170],3⟩,⟨247,(18),[1,2,5,6,13,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4128
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4129
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4130
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4131
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4132
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4133
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4134
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4135
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4136
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4137
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4138
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4139
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4140
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4141
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4142
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4143
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4144
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4145
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4146
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4147
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4148
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4149
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4150
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4151
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4152
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4153
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4154
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4155
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4156
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4157
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4158
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4159
end Section14Records_5_4128_4160

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4128_4160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4160_4192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4160_4192
private theorem valid4160 : RecordDataValid section14Catalog 5 (⟨247,(19),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4161 : RecordDataValid section14Catalog 5 (⟨247,(20),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4162 : RecordDataValid section14Catalog 5 (⟨247,(21),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4163 : RecordDataValid section14Catalog 5 (⟨247,(22),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4164 : RecordDataValid section14Catalog 5 (⟨247,(23),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4165 : RecordDataValid section14Catalog 5 (⟨247,(24),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4166 : RecordDataValid section14Catalog 5 (⟨249,(0),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4167 : RecordDataValid section14Catalog 5 (⟨249,(1),[2,5,6,14],[170],924⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨924,[2,3,5,6,7,14,15],928⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4168 : RecordDataValid section14Catalog 5 (⟨249,(2),[1,2,5,6,13,14],[170],888⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4169 : RecordDataValid section14Catalog 5 (⟨249,(3),[1,2,5,6,13,14],[170],889⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4170 : RecordDataValid section14Catalog 5 (⟨249,(4),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4171 : RecordDataValid section14Catalog 5 (⟨249,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4172 : RecordDataValid section14Catalog 5 (⟨249,(6),[2,5,6,14],[170],924⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨924,[2,3,5,6,7,14,15],928⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4173 : RecordDataValid section14Catalog 5 (⟨249,(7),[1,2,5,6,13,14],[170],888⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4174 : RecordDataValid section14Catalog 5 (⟨249,(8),[1,2,5,6,13,14],[170],889⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4175 : RecordDataValid section14Catalog 5 (⟨249,(9),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4176 : RecordDataValid section14Catalog 5 (⟨249,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4177 : RecordDataValid section14Catalog 5 (⟨249,(11),[2,5,6,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4178 : RecordDataValid section14Catalog 5 (⟨249,(12),[1,2,5,6,13,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4179 : RecordDataValid section14Catalog 5 (⟨249,(13),[1,2,5,6,13,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4180 : RecordDataValid section14Catalog 5 (⟨249,(14),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4181 : RecordDataValid section14Catalog 5 (⟨249,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4182 : RecordDataValid section14Catalog 5 (⟨249,(16),[2,5,6,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4183 : RecordDataValid section14Catalog 5 (⟨249,(17),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4184 : RecordDataValid section14Catalog 5 (⟨249,(18),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4185 : RecordDataValid section14Catalog 5 (⟨249,(19),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4186 : RecordDataValid section14Catalog 5 (⟨249,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4187 : RecordDataValid section14Catalog 5 (⟨249,(21),[2,5,6,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4188 : RecordDataValid section14Catalog 5 (⟨249,(22),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4189 : RecordDataValid section14Catalog 5 (⟨249,(23),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4190 : RecordDataValid section14Catalog 5 (⟨249,(24),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4191 : RecordDataValid section14Catalog 5 (⟨253,(0),[1,2,5,6,13,14],[170],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4160_4192 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4160).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4160).take 32 = [⟨247,(19),[1,2,5,6,13,14],[170],3⟩,⟨247,(20),[1,2,5,6,13,14],[170],3⟩,⟨247,(21),[1,2,5,6,13,14],[170],3⟩,⟨247,(22),[1,2,5,6,13,14],[170],3⟩,⟨247,(23),[1,2,5,6,13,14],[170],3⟩,⟨247,(24),[1,2,5,6,13,14],[170],3⟩,⟨249,(0),[1,2,5,6,13,14],[170],10⟩,⟨249,(1),[2,5,6,14],[170],924⟩,⟨249,(2),[1,2,5,6,13,14],[170],888⟩,⟨249,(3),[1,2,5,6,13,14],[170],889⟩,⟨249,(4),[1,2,5,6,13,14],[170],890⟩,⟨249,(5),[1,2,5,6,13,14],[170],10⟩,⟨249,(6),[2,5,6,14],[170],924⟩,⟨249,(7),[1,2,5,6,13,14],[170],888⟩,⟨249,(8),[1,2,5,6,13,14],[170],889⟩,⟨249,(9),[1,2,5,6,13,14],[170],890⟩,⟨249,(10),[1,2,5,6,13,14],[170],18⟩,⟨249,(11),[2,5,6,14],[170],891⟩,⟨249,(12),[1,2,5,6,13,14],[170],891⟩,⟨249,(13),[1,2,5,6,13,14],[170],891⟩,⟨249,(14),[1,2,5,6,13,14],[170],890⟩,⟨249,(15),[1,2,5,6,13,14],[170],21⟩,⟨249,(16),[2,5,6,14],[170],892⟩,⟨249,(17),[1,2,5,6,13,14],[170],892⟩,⟨249,(18),[1,2,5,6,13,14],[170],892⟩,⟨249,(19),[1,2,5,6,13,14],[170],892⟩,⟨249,(20),[1,2,5,6,13,14],[170],24⟩,⟨249,(21),[2,5,6,14],[170],893⟩,⟨249,(22),[1,2,5,6,13,14],[170],893⟩,⟨249,(23),[1,2,5,6,13,14],[170],893⟩,⟨249,(24),[1,2,5,6,13,14],[170],893⟩,⟨253,(0),[1,2,5,6,13,14],[170],884⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4160
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4161
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4162
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4163
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4164
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4165
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4166
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4167
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4168
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4169
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4170
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4171
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4172
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4173
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4174
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4175
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4176
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4177
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4178
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4179
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4180
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4181
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4182
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4183
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4184
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4185
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4186
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4187
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4188
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4189
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4190
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4191
end Section14Records_5_4160_4192

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4160_4192


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4192_4224
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4192_4224
private theorem valid4192 : RecordDataValid section14Catalog 5 (⟨253,(1),[1,2,5,6,13,14],[170],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4193 : RecordDataValid section14Catalog 5 (⟨253,(2),[1,2,5,6,13,14],[170],895⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨895,[1,2,3,4,5,6,7,8,9,10,13,14,16],897⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4194 : RecordDataValid section14Catalog 5 (⟨253,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4195 : RecordDataValid section14Catalog 5 (⟨253,(4),[1,2,5,6,13,14],[170],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4196 : RecordDataValid section14Catalog 5 (⟨253,(5),[1,2,5,6,13,14],[170],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4197 : RecordDataValid section14Catalog 5 (⟨253,(6),[1,2,5,6,13,14],[170],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4198 : RecordDataValid section14Catalog 5 (⟨253,(7),[1,2,5,6,13,14],[170],896⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨896,[1,2,4,5,6,10,13,14,16],898⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4199 : RecordDataValid section14Catalog 5 (⟨253,(8),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4200 : RecordDataValid section14Catalog 5 (⟨253,(9),[1,2,5,6,13,14],[170],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4201 : RecordDataValid section14Catalog 5 (⟨253,(10),[1,2,5,6,13,14],[170],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4202 : RecordDataValid section14Catalog 5 (⟨253,(11),[1,2,5,6,13,14],[170],897⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨897,[1,2,4,5,6,8,9,10,12,13,14,16],899⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4203 : RecordDataValid section14Catalog 5 (⟨253,(12),[1,2,5,6,13,14],[170],898⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨898,[1,2,4,5,6,8,9,10,12,13,14,16],900⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4204 : RecordDataValid section14Catalog 5 (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4205 : RecordDataValid section14Catalog 5 (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4206 : RecordDataValid section14Catalog 5 (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4207 : RecordDataValid section14Catalog 5 (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4208 : RecordDataValid section14Catalog 5 (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4209 : RecordDataValid section14Catalog 5 (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4210 : RecordDataValid section14Catalog 5 (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4211 : RecordDataValid section14Catalog 5 (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4212 : RecordDataValid section14Catalog 5 (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4213 : RecordDataValid section14Catalog 5 (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4214 : RecordDataValid section14Catalog 5 (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4215 : RecordDataValid section14Catalog 5 (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4216 : RecordDataValid section14Catalog 5 (⟨255,(0),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4217 : RecordDataValid section14Catalog 5 (⟨255,(1),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4218 : RecordDataValid section14Catalog 5 (⟨255,(2),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4219 : RecordDataValid section14Catalog 5 (⟨255,(3),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4220 : RecordDataValid section14Catalog 5 (⟨255,(4),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4221 : RecordDataValid section14Catalog 5 (⟨255,(5),[1,2,5,6],[170],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4222 : RecordDataValid section14Catalog 5 (⟨255,(6),[1,2,5,6],[170],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4223 : RecordDataValid section14Catalog 5 (⟨255,(7),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4192_4224 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4192).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4192).take 32 = [⟨253,(1),[1,2,5,6,13,14],[170],894⟩,⟨253,(2),[1,2,5,6,13,14],[170],895⟩,⟨253,(3),[1,2,5,6,13,14],[170],29⟩,⟨253,(4),[1,2,5,6,13,14],[170],30⟩,⟨253,(5),[1,2,5,6,13,14],[170],884⟩,⟨253,(6),[1,2,5,6,13,14],[170],894⟩,⟨253,(7),[1,2,5,6,13,14],[170],896⟩,⟨253,(8),[1,2,5,6,13,14],[170],29⟩,⟨253,(9),[1,2,5,6,13,14],[170],32⟩,⟨253,(10),[1,2,5,6,13,14],[170],84⟩,⟨253,(11),[1,2,5,6,13,14],[170],897⟩,⟨253,(12),[1,2,5,6,13,14],[170],898⟩,⟨253,(13),[1,2,5,6,13,14],[170],29⟩,⟨253,(14),[1,2,5,6,13,14],[170],34⟩,⟨253,(15),[1,2,5,6,13,14],[170],35⟩,⟨253,(16),[1,2,5,6,13,14],[170],36⟩,⟨253,(17),[1,2,5,6,13,14],[170],37⟩,⟨253,(18),[1,2,5,6,13,14],[170],29⟩,⟨253,(19),[1,2,5,6,13,14],[170],37⟩,⟨253,(20),[1,2,5,6,13,14],[170],38⟩,⟨253,(21),[1,2,5,6,13,14],[170],39⟩,⟨253,(22),[1,2,5,6,13,14],[170],40⟩,⟨253,(23),[1,2,5,6,13,14],[170],29⟩,⟨253,(24),[1,2,5,6,13,14],[170],40⟩,⟨255,(0),[1,2,5,6],[170],899⟩,⟨255,(1),[1,2,5,6],[170],899⟩,⟨255,(2),[1,2,5,6],[170],900⟩,⟨255,(3),[1,2,5,6],[170],901⟩,⟨255,(4),[1,2,5,6],[170],902⟩,⟨255,(5),[1,2,5,6],[170],903⟩,⟨255,(6),[1,2,5,6],[170],903⟩,⟨255,(7),[1,2,5,6],[170],900⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4192
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4193
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4194
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4195
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4196
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4197
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4198
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4199
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4200
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4201
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4202
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4203
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4204
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4205
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4206
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4207
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4208
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4209
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4210
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4211
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4212
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4213
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4214
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4215
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4216
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4217
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4218
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4219
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4220
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4221
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4222
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4223
end Section14Records_5_4192_4224

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4192_4224

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4096).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 4096 4160 4224 (by decide) (by decide) (all_of_interval_split P xs 4096 4128 4160 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4096_4128 hnum) (Freiman.workReverse20260919_s0005_records_4128_4160 hnum)) (all_of_interval_split P xs 4160 4192 4224 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4160_4192 hnum) (Freiman.workReverse20260919_s0005_records_4192_4224 hnum)))

#print axioms solution
