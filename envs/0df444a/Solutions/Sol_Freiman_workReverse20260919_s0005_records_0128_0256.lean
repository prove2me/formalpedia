-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_0128_0256
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:10:41.485358+00:00
-- url     : https://prove2.me/submissions/792b2ae3-dfb3-48f2-81f6-c5bad650e1b5

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0128_0160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_128_160
private theorem valid128 : RecordDataValid section14Catalog 5 (⟨14,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid129 : RecordDataValid section14Catalog 5 (⟨14,(19),[2,5,6,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid130 : RecordDataValid section14Catalog 5 (⟨15,(1),[1,2,5,6],[170],49⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨49,[1,2,4,5,6,8,9,10,12],49⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid131 : RecordDataValid section14Catalog 5 (⟨15,(3),[1,2,5,6],[170],50⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨50,[1,2,4,5,6,8,9,10,12],50⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid132 : RecordDataValid section14Catalog 5 (⟨15,(5),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid133 : RecordDataValid section14Catalog 5 (⟨15,(7),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid134 : RecordDataValid section14Catalog 5 (⟨15,(11),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid135 : RecordDataValid section14Catalog 5 (⟨15,(13),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid136 : RecordDataValid section14Catalog 5 (⟨15,(15),[2,5],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid137 : RecordDataValid section14Catalog 5 (⟨15,(17),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid138 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid139 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,9,10,13,14],[1],57⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨57,[1,2,5,6,9,10,13,14],57⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid140 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid141 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid142 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨58,[1,2,3,5,6,7,13,14,15],58⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid143 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid144 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[45],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid145 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[61],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid146 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[64],63⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨63,[1,2,4,5,6,8,9,10,12,13,14,16],63⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid147 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[65],64⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨64,[1,2,4,5,6,8,9,10,12,13,14,16],64⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid148 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[80,84],65⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨65,[1,2,4,5,6,8,9,10,12,13,14,16],65⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid149 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[81,85],66⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨66,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],66⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid150 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨67,[1,2,5,6,13,14],67⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid151 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid152 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[108],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid153 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[109],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid154 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[124],71⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨71,[1,2,4,5,6,8,9,10,12,13,14,16],71⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid155 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[125],72⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨72,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],72⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid156 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[174],205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨205,[1,2,4,5,6,8,9,10,12,13,14,16],205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid157 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨206,[1,2,5,6,13,14],206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid158 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[175],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid159 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[186],208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨208,[1,2,3,5,6,7,13,14,15],208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0128_0160 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 128).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 128).take 32 = [⟨14,(17),[1,2,5,6,13,14],[170],48⟩,⟨14,(19),[2,5,6,14],[170],143⟩,⟨15,(1),[1,2,5,6],[170],49⟩,⟨15,(3),[1,2,5,6],[170],50⟩,⟨15,(5),[5,6],[170],143⟩,⟨15,(7),[5,6],[170],143⟩,⟨15,(11),[5,6],[170],143⟩,⟨15,(13),[5,6],[170],143⟩,⟨15,(15),[2,5],[170],143⟩,⟨15,(17),[5,6],[170],143⟩,⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨16,(-1),[1,2,5,6,9,10,13,14],[1],57⟩,⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩,⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩,⟨16,(-1),[1,2,5,6,13,14],[45],61⟩,⟨16,(-1),[1,2,5,6,13,14],[61],62⟩,⟨16,(-1),[1,2,5,6,13,14],[64],63⟩,⟨16,(-1),[1,2,5,6,13,14],[65],64⟩,⟨16,(-1),[1,2,5,6,13,14],[80,84],65⟩,⟨16,(-1),[1,2,5,6,13,14],[81,85],66⟩,⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩,⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩,⟨16,(-1),[1,2,5,6,13,14],[108],69⟩,⟨16,(-1),[1,2,5,6,13,14],[109],70⟩,⟨16,(-1),[1,2,5,6,13,14],[124],71⟩,⟨16,(-1),[1,2,5,6,13,14],[125],72⟩,⟨16,(-1),[1,2,5,6,13,14],[174],205⟩,⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩,⟨16,(-1),[1,2,5,6,13,14],[175],207⟩,⟨16,(-1),[1,2,5,6,13,14],[186],208⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid128
  · exact recordValid_of_data section14Catalog 5 _ hnum valid129
  · exact recordValid_of_data section14Catalog 5 _ hnum valid130
  · exact recordValid_of_data section14Catalog 5 _ hnum valid131
  · exact recordValid_of_data section14Catalog 5 _ hnum valid132
  · exact recordValid_of_data section14Catalog 5 _ hnum valid133
  · exact recordValid_of_data section14Catalog 5 _ hnum valid134
  · exact recordValid_of_data section14Catalog 5 _ hnum valid135
  · exact recordValid_of_data section14Catalog 5 _ hnum valid136
  · exact recordValid_of_data section14Catalog 5 _ hnum valid137
  · exact recordValid_of_data section14Catalog 5 _ hnum valid138
  · exact recordValid_of_data section14Catalog 5 _ hnum valid139
  · exact recordValid_of_data section14Catalog 5 _ hnum valid140
  · exact recordValid_of_data section14Catalog 5 _ hnum valid141
  · exact recordValid_of_data section14Catalog 5 _ hnum valid142
  · exact recordValid_of_data section14Catalog 5 _ hnum valid143
  · exact recordValid_of_data section14Catalog 5 _ hnum valid144
  · exact recordValid_of_data section14Catalog 5 _ hnum valid145
  · exact recordValid_of_data section14Catalog 5 _ hnum valid146
  · exact recordValid_of_data section14Catalog 5 _ hnum valid147
  · exact recordValid_of_data section14Catalog 5 _ hnum valid148
  · exact recordValid_of_data section14Catalog 5 _ hnum valid149
  · exact recordValid_of_data section14Catalog 5 _ hnum valid150
  · exact recordValid_of_data section14Catalog 5 _ hnum valid151
  · exact recordValid_of_data section14Catalog 5 _ hnum valid152
  · exact recordValid_of_data section14Catalog 5 _ hnum valid153
  · exact recordValid_of_data section14Catalog 5 _ hnum valid154
  · exact recordValid_of_data section14Catalog 5 _ hnum valid155
  · exact recordValid_of_data section14Catalog 5 _ hnum valid156
  · exact recordValid_of_data section14Catalog 5 _ hnum valid157
  · exact recordValid_of_data section14Catalog 5 _ hnum valid158
  · exact recordValid_of_data section14Catalog 5 _ hnum valid159
end Section14Records_5_128_160

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0128_0160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0160_0192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_160_192
private theorem valid160 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[191],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid161 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨240,[1,2,5,6,9,10,13,14],240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid162 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨241,[1,2,3,5,6,7,13,14,15],241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid163 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[210],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid164 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid165 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[238],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid166 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,13,14],[254],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid167 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid168 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,13,14],[4,20],58⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨58,[1,2,3,5,6,7,13,14,15],58⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid169 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,13,14],[211],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid170 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,2,5,13,14],[235,251],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid171 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,5,9,13],[0],57⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨57,[1,2,5,6,9,10,13,14],57⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid172 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,5,13],[16,17],59⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨59,[1,5,9,10,13],59⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid173 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,5,13],[40,56],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid174 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,5,13],[44],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid175 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,5,13],[60],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid176 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,5,13],[239],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid177 : RecordDataValid section14Catalog 5 (⟨16,(-1),[1,5,13],[255],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid178 : RecordDataValid section14Catalog 5 (⟨16,(-1),[2,5,6,14],[170],208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨208,[1,2,3,5,6,7,13,14,15],208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid179 : RecordDataValid section14Catalog 5 (⟨16,(-1),[5],[151],1397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1397,[5,6,9,10],1402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid180 : RecordDataValid section14Catalog 5 (⟨16,(-1),[5,6],[214,215],241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨241,[1,2,3,5,6,7,13,14,15],241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid181 : RecordDataValid section14Catalog 5 (⟨16,(-1),[5,6],[68],1394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1394,[5,6],1399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid182 : RecordDataValid section14Catalog 5 (⟨16,(-1),[5,6],[69],1395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1395,[5,6],1400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid183 : RecordDataValid section14Catalog 5 (⟨16,(-1),[5,6],[147],1397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1397,[5,6,9,10],1402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid184 : RecordDataValid section14Catalog 5 (⟨16,(-1),[5,6],[190],1398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1398,[5,6,7,8,9,10,12],1403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid185 : RecordDataValid section14Catalog 5 (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid186 : RecordDataValid section14Catalog 5 (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid187 : RecordDataValid section14Catalog 5 (⟨18,(0),[1,5],[130],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid188 : RecordDataValid section14Catalog 5 (⟨18,(0),[1,5],[134],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid189 : RecordDataValid section14Catalog 5 (⟨18,(0),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid190 : RecordDataValid section14Catalog 5 (⟨18,(0),[5],[146],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid191 : RecordDataValid section14Catalog 5 (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0160_0192 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 160).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 160).take 32 = [⟨16,(-1),[1,2,5,6,13,14],[191],239⟩,⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩,⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩,⟨16,(-1),[1,2,5,6,13,14],[210],242⟩,⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩,⟨16,(-1),[1,2,5,6,13,14],[238],244⟩,⟨16,(-1),[1,2,5,6,13,14],[254],245⟩,⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨16,(-1),[1,2,5,13,14],[4,20],58⟩,⟨16,(-1),[1,2,5,13,14],[211],242⟩,⟨16,(-1),[1,2,5,13,14],[235,251],243⟩,⟨16,(-1),[1,5,9,13],[0],57⟩,⟨16,(-1),[1,5,13],[16,17],59⟩,⟨16,(-1),[1,5,13],[40,56],60⟩,⟨16,(-1),[1,5,13],[44],61⟩,⟨16,(-1),[1,5,13],[60],62⟩,⟨16,(-1),[1,5,13],[239],244⟩,⟨16,(-1),[1,5,13],[255],245⟩,⟨16,(-1),[2,5,6,14],[170],208⟩,⟨16,(-1),[5],[151],1397⟩,⟨16,(-1),[5,6],[214,215],241⟩,⟨16,(-1),[5,6],[68],1394⟩,⟨16,(-1),[5,6],[69],1395⟩,⟨16,(-1),[5,6],[147],1397⟩,⟨16,(-1),[5,6],[190],1398⟩,⟨18,(0),[1,2,5,6,13,14],[131],106⟩,⟨18,(0),[1,2,5,6,13,14],[150],125⟩,⟨18,(0),[1,5],[130],73⟩,⟨18,(0),[1,5],[134],125⟩,⟨18,(0),[1,5,13],[135],125⟩,⟨18,(0),[5],[146],160⟩,⟨18,(1),[1,2,5,6,13,14],[131],106⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid160
  · exact recordValid_of_data section14Catalog 5 _ hnum valid161
  · exact recordValid_of_data section14Catalog 5 _ hnum valid162
  · exact recordValid_of_data section14Catalog 5 _ hnum valid163
  · exact recordValid_of_data section14Catalog 5 _ hnum valid164
  · exact recordValid_of_data section14Catalog 5 _ hnum valid165
  · exact recordValid_of_data section14Catalog 5 _ hnum valid166
  · exact recordValid_of_data section14Catalog 5 _ hnum valid167
  · exact recordValid_of_data section14Catalog 5 _ hnum valid168
  · exact recordValid_of_data section14Catalog 5 _ hnum valid169
  · exact recordValid_of_data section14Catalog 5 _ hnum valid170
  · exact recordValid_of_data section14Catalog 5 _ hnum valid171
  · exact recordValid_of_data section14Catalog 5 _ hnum valid172
  · exact recordValid_of_data section14Catalog 5 _ hnum valid173
  · exact recordValid_of_data section14Catalog 5 _ hnum valid174
  · exact recordValid_of_data section14Catalog 5 _ hnum valid175
  · exact recordValid_of_data section14Catalog 5 _ hnum valid176
  · exact recordValid_of_data section14Catalog 5 _ hnum valid177
  · exact recordValid_of_data section14Catalog 5 _ hnum valid178
  · exact recordValid_of_data section14Catalog 5 _ hnum valid179
  · exact recordValid_of_data section14Catalog 5 _ hnum valid180
  · exact recordValid_of_data section14Catalog 5 _ hnum valid181
  · exact recordValid_of_data section14Catalog 5 _ hnum valid182
  · exact recordValid_of_data section14Catalog 5 _ hnum valid183
  · exact recordValid_of_data section14Catalog 5 _ hnum valid184
  · exact recordValid_of_data section14Catalog 5 _ hnum valid185
  · exact recordValid_of_data section14Catalog 5 _ hnum valid186
  · exact recordValid_of_data section14Catalog 5 _ hnum valid187
  · exact recordValid_of_data section14Catalog 5 _ hnum valid188
  · exact recordValid_of_data section14Catalog 5 _ hnum valid189
  · exact recordValid_of_data section14Catalog 5 _ hnum valid190
  · exact recordValid_of_data section14Catalog 5 _ hnum valid191
end Section14Records_5_160_192

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0160_0192


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0192_0224
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_192_224
private theorem valid192 : RecordDataValid section14Catalog 5 (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid193 : RecordDataValid section14Catalog 5 (⟨18,(1),[1,5],[130],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid194 : RecordDataValid section14Catalog 5 (⟨18,(1),[1,5],[134],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid195 : RecordDataValid section14Catalog 5 (⟨18,(1),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid196 : RecordDataValid section14Catalog 5 (⟨18,(1),[5],[146],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid197 : RecordDataValid section14Catalog 5 (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid198 : RecordDataValid section14Catalog 5 (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid199 : RecordDataValid section14Catalog 5 (⟨18,(2),[1,5],[130],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid200 : RecordDataValid section14Catalog 5 (⟨18,(2),[1,5],[134],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid201 : RecordDataValid section14Catalog 5 (⟨18,(2),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid202 : RecordDataValid section14Catalog 5 (⟨18,(2),[5],[146],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid203 : RecordDataValid section14Catalog 5 (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid204 : RecordDataValid section14Catalog 5 (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid205 : RecordDataValid section14Catalog 5 (⟨18,(3),[1,5],[130],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid206 : RecordDataValid section14Catalog 5 (⟨18,(3),[1,5],[134],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid207 : RecordDataValid section14Catalog 5 (⟨18,(3),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid208 : RecordDataValid section14Catalog 5 (⟨18,(3),[5],[146],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid209 : RecordDataValid section14Catalog 5 (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid210 : RecordDataValid section14Catalog 5 (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid211 : RecordDataValid section14Catalog 5 (⟨18,(4),[1,5],[130],73⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨73,[1,5,9,13],73⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid212 : RecordDataValid section14Catalog 5 (⟨18,(4),[1,5],[134],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid213 : RecordDataValid section14Catalog 5 (⟨18,(4),[1,5,13],[135],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid214 : RecordDataValid section14Catalog 5 (⟨18,(4),[5],[146],160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨160,[1,5,9,10,13],160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid215 : RecordDataValid section14Catalog 5 (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid216 : RecordDataValid section14Catalog 5 (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid217 : RecordDataValid section14Catalog 5 (⟨18,(5),[1,5],[130],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid218 : RecordDataValid section14Catalog 5 (⟨18,(5),[1,5],[134],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid219 : RecordDataValid section14Catalog 5 (⟨18,(5),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid220 : RecordDataValid section14Catalog 5 (⟨18,(5),[5],[146],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid221 : RecordDataValid section14Catalog 5 (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid222 : RecordDataValid section14Catalog 5 (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid223 : RecordDataValid section14Catalog 5 (⟨18,(6),[1,5],[130],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0192_0224 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 192).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 192).take 32 = [⟨18,(1),[1,2,5,6,13,14],[150],125⟩,⟨18,(1),[1,5],[130],73⟩,⟨18,(1),[1,5],[134],125⟩,⟨18,(1),[1,5,13],[135],125⟩,⟨18,(1),[5],[146],160⟩,⟨18,(2),[1,2,5,6,13,14],[131],106⟩,⟨18,(2),[1,2,5,6,13,14],[150],125⟩,⟨18,(2),[1,5],[130],73⟩,⟨18,(2),[1,5],[134],125⟩,⟨18,(2),[1,5,13],[135],125⟩,⟨18,(2),[5],[146],160⟩,⟨18,(3),[1,2,5,6,13,14],[131],106⟩,⟨18,(3),[1,2,5,6,13,14],[150],125⟩,⟨18,(3),[1,5],[130],73⟩,⟨18,(3),[1,5],[134],125⟩,⟨18,(3),[1,5,13],[135],125⟩,⟨18,(3),[5],[146],160⟩,⟨18,(4),[1,2,5,6,13,14],[131],106⟩,⟨18,(4),[1,2,5,6,13,14],[150],125⟩,⟨18,(4),[1,5],[130],73⟩,⟨18,(4),[1,5],[134],125⟩,⟨18,(4),[1,5,13],[135],125⟩,⟨18,(4),[5],[146],160⟩,⟨18,(5),[1,2,5,6,13,14],[131],107⟩,⟨18,(5),[1,2,5,6,13,14],[150],126⟩,⟨18,(5),[1,5],[130],74⟩,⟨18,(5),[1,5],[134],126⟩,⟨18,(5),[1,5,13],[135],126⟩,⟨18,(5),[5],[146],161⟩,⟨18,(6),[1,2,5,6,13,14],[131],107⟩,⟨18,(6),[1,2,5,6,13,14],[150],126⟩,⟨18,(6),[1,5],[130],74⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid192
  · exact recordValid_of_data section14Catalog 5 _ hnum valid193
  · exact recordValid_of_data section14Catalog 5 _ hnum valid194
  · exact recordValid_of_data section14Catalog 5 _ hnum valid195
  · exact recordValid_of_data section14Catalog 5 _ hnum valid196
  · exact recordValid_of_data section14Catalog 5 _ hnum valid197
  · exact recordValid_of_data section14Catalog 5 _ hnum valid198
  · exact recordValid_of_data section14Catalog 5 _ hnum valid199
  · exact recordValid_of_data section14Catalog 5 _ hnum valid200
  · exact recordValid_of_data section14Catalog 5 _ hnum valid201
  · exact recordValid_of_data section14Catalog 5 _ hnum valid202
  · exact recordValid_of_data section14Catalog 5 _ hnum valid203
  · exact recordValid_of_data section14Catalog 5 _ hnum valid204
  · exact recordValid_of_data section14Catalog 5 _ hnum valid205
  · exact recordValid_of_data section14Catalog 5 _ hnum valid206
  · exact recordValid_of_data section14Catalog 5 _ hnum valid207
  · exact recordValid_of_data section14Catalog 5 _ hnum valid208
  · exact recordValid_of_data section14Catalog 5 _ hnum valid209
  · exact recordValid_of_data section14Catalog 5 _ hnum valid210
  · exact recordValid_of_data section14Catalog 5 _ hnum valid211
  · exact recordValid_of_data section14Catalog 5 _ hnum valid212
  · exact recordValid_of_data section14Catalog 5 _ hnum valid213
  · exact recordValid_of_data section14Catalog 5 _ hnum valid214
  · exact recordValid_of_data section14Catalog 5 _ hnum valid215
  · exact recordValid_of_data section14Catalog 5 _ hnum valid216
  · exact recordValid_of_data section14Catalog 5 _ hnum valid217
  · exact recordValid_of_data section14Catalog 5 _ hnum valid218
  · exact recordValid_of_data section14Catalog 5 _ hnum valid219
  · exact recordValid_of_data section14Catalog 5 _ hnum valid220
  · exact recordValid_of_data section14Catalog 5 _ hnum valid221
  · exact recordValid_of_data section14Catalog 5 _ hnum valid222
  · exact recordValid_of_data section14Catalog 5 _ hnum valid223
end Section14Records_5_192_224

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0192_0224


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0224_0256
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_224_256
private theorem valid224 : RecordDataValid section14Catalog 5 (⟨18,(6),[1,5],[134],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid225 : RecordDataValid section14Catalog 5 (⟨18,(6),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid226 : RecordDataValid section14Catalog 5 (⟨18,(6),[5],[146],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid227 : RecordDataValid section14Catalog 5 (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid228 : RecordDataValid section14Catalog 5 (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid229 : RecordDataValid section14Catalog 5 (⟨18,(7),[1,5],[130],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid230 : RecordDataValid section14Catalog 5 (⟨18,(7),[1,5],[134],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid231 : RecordDataValid section14Catalog 5 (⟨18,(7),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid232 : RecordDataValid section14Catalog 5 (⟨18,(7),[5],[146],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid233 : RecordDataValid section14Catalog 5 (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid234 : RecordDataValid section14Catalog 5 (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid235 : RecordDataValid section14Catalog 5 (⟨18,(8),[1,5],[130],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid236 : RecordDataValid section14Catalog 5 (⟨18,(8),[1,5],[134],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid237 : RecordDataValid section14Catalog 5 (⟨18,(8),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid238 : RecordDataValid section14Catalog 5 (⟨18,(8),[5],[146],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid239 : RecordDataValid section14Catalog 5 (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid240 : RecordDataValid section14Catalog 5 (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid241 : RecordDataValid section14Catalog 5 (⟨18,(9),[1,5],[130],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid242 : RecordDataValid section14Catalog 5 (⟨18,(9),[1,5],[134],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid243 : RecordDataValid section14Catalog 5 (⟨18,(9),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid244 : RecordDataValid section14Catalog 5 (⟨18,(9),[5],[146],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid245 : RecordDataValid section14Catalog 5 (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid246 : RecordDataValid section14Catalog 5 (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid247 : RecordDataValid section14Catalog 5 (⟨18,(10),[1,5],[130],75⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨75,[1,5,9,13],75⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid248 : RecordDataValid section14Catalog 5 (⟨18,(10),[1,5],[134],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid249 : RecordDataValid section14Catalog 5 (⟨18,(10),[1,5,13],[135],127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨127,[1,2,3,5,6,7,13,14,15],127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid250 : RecordDataValid section14Catalog 5 (⟨18,(10),[5],[146],162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨162,[1,5,9,10,13],162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid251 : RecordDataValid section14Catalog 5 (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid252 : RecordDataValid section14Catalog 5 (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid253 : RecordDataValid section14Catalog 5 (⟨18,(11),[1,5],[130],76⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨76,[1,5,9,13],76⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid254 : RecordDataValid section14Catalog 5 (⟨18,(11),[1,5],[134],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid255 : RecordDataValid section14Catalog 5 (⟨18,(11),[1,5,13],[135],128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨128,[1,2,5,6,13,14],128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0224_0256 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 224).take 32 = [⟨18,(6),[1,5],[134],126⟩,⟨18,(6),[1,5,13],[135],126⟩,⟨18,(6),[5],[146],161⟩,⟨18,(7),[1,2,5,6,13,14],[131],107⟩,⟨18,(7),[1,2,5,6,13,14],[150],126⟩,⟨18,(7),[1,5],[130],74⟩,⟨18,(7),[1,5],[134],126⟩,⟨18,(7),[1,5,13],[135],126⟩,⟨18,(7),[5],[146],161⟩,⟨18,(8),[1,2,5,6,13,14],[131],107⟩,⟨18,(8),[1,2,5,6,13,14],[150],126⟩,⟨18,(8),[1,5],[130],74⟩,⟨18,(8),[1,5],[134],126⟩,⟨18,(8),[1,5,13],[135],126⟩,⟨18,(8),[5],[146],161⟩,⟨18,(9),[1,2,5,6,13,14],[131],107⟩,⟨18,(9),[1,2,5,6,13,14],[150],126⟩,⟨18,(9),[1,5],[130],74⟩,⟨18,(9),[1,5],[134],126⟩,⟨18,(9),[1,5,13],[135],126⟩,⟨18,(9),[5],[146],161⟩,⟨18,(10),[1,2,5,6,13,14],[131],108⟩,⟨18,(10),[1,2,5,6,13,14],[150],127⟩,⟨18,(10),[1,5],[130],75⟩,⟨18,(10),[1,5],[134],127⟩,⟨18,(10),[1,5,13],[135],127⟩,⟨18,(10),[5],[146],162⟩,⟨18,(11),[1,2,5,6,13,14],[131],109⟩,⟨18,(11),[1,2,5,6,13,14],[150],128⟩,⟨18,(11),[1,5],[130],76⟩,⟨18,(11),[1,5],[134],128⟩,⟨18,(11),[1,5,13],[135],128⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid224
  · exact recordValid_of_data section14Catalog 5 _ hnum valid225
  · exact recordValid_of_data section14Catalog 5 _ hnum valid226
  · exact recordValid_of_data section14Catalog 5 _ hnum valid227
  · exact recordValid_of_data section14Catalog 5 _ hnum valid228
  · exact recordValid_of_data section14Catalog 5 _ hnum valid229
  · exact recordValid_of_data section14Catalog 5 _ hnum valid230
  · exact recordValid_of_data section14Catalog 5 _ hnum valid231
  · exact recordValid_of_data section14Catalog 5 _ hnum valid232
  · exact recordValid_of_data section14Catalog 5 _ hnum valid233
  · exact recordValid_of_data section14Catalog 5 _ hnum valid234
  · exact recordValid_of_data section14Catalog 5 _ hnum valid235
  · exact recordValid_of_data section14Catalog 5 _ hnum valid236
  · exact recordValid_of_data section14Catalog 5 _ hnum valid237
  · exact recordValid_of_data section14Catalog 5 _ hnum valid238
  · exact recordValid_of_data section14Catalog 5 _ hnum valid239
  · exact recordValid_of_data section14Catalog 5 _ hnum valid240
  · exact recordValid_of_data section14Catalog 5 _ hnum valid241
  · exact recordValid_of_data section14Catalog 5 _ hnum valid242
  · exact recordValid_of_data section14Catalog 5 _ hnum valid243
  · exact recordValid_of_data section14Catalog 5 _ hnum valid244
  · exact recordValid_of_data section14Catalog 5 _ hnum valid245
  · exact recordValid_of_data section14Catalog 5 _ hnum valid246
  · exact recordValid_of_data section14Catalog 5 _ hnum valid247
  · exact recordValid_of_data section14Catalog 5 _ hnum valid248
  · exact recordValid_of_data section14Catalog 5 _ hnum valid249
  · exact recordValid_of_data section14Catalog 5 _ hnum valid250
  · exact recordValid_of_data section14Catalog 5 _ hnum valid251
  · exact recordValid_of_data section14Catalog 5 _ hnum valid252
  · exact recordValid_of_data section14Catalog 5 _ hnum valid253
  · exact recordValid_of_data section14Catalog 5 _ hnum valid254
  · exact recordValid_of_data section14Catalog 5 _ hnum valid255
end Section14Records_5_224_256

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0224_0256

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 128).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 128 192 256 (by decide) (by decide) (all_of_interval_split P xs 128 160 192 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_0128_0160 hnum) (Freiman.workReverse20260919_s0005_records_0160_0192 hnum)) (all_of_interval_split P xs 192 224 256 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_0192_0224 hnum) (Freiman.workReverse20260919_s0005_records_0224_0256 hnum)))

#print axioms solution
