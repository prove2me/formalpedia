-- Prove2me | solution 1 for Freiman.section14_s0011_records_0608_0672
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:34:18.209467+00:00
-- url     : https://prove2.me/submissions/82898868-fedb-47f9-81c9-34ed75d0b158

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
namespace Section14Records_11_608_672
private theorem valid608 : RecordDataValid section14Catalog 11 (⟨227,(1),[11],[2],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 11 (⟨227,(2),[11],[2],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 11 (⟨227,(3),[11],[2],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 11 (⟨227,(4),[11],[2],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 11 (⟨227,(5),[11],[2],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 11 (⟨227,(6),[11],[2],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 11 (⟨227,(7),[11],[2],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 11 (⟨227,(8),[11],[2],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 11 (⟨227,(9),[11],[2],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 11 (⟨227,(10),[11],[2],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 11 (⟨227,(11),[11],[2],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 11 (⟨227,(12),[11],[2],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 11 (⟨227,(13),[11],[2],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 11 (⟨227,(14),[11],[2],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 11 (⟨227,(15),[11],[2],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 11 (⟨227,(16),[11],[2],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 11 (⟨227,(17),[11],[2],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 11 (⟨227,(18),[11],[2],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 11 (⟨227,(19),[11],[2],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 11 (⟨227,(20),[11],[2],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 11 (⟨227,(21),[11],[2],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 11 (⟨227,(22),[11],[2],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 11 (⟨227,(23),[11],[2],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 11 (⟨227,(24),[11],[2],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 11 (⟨228,(0),[11],[2],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 11 (⟨228,(1),[11],[2],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 11 (⟨228,(2),[11],[2],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 11 (⟨228,(3),[11],[2],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 11 (⟨228,(4),[11],[2],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 11 (⟨228,(5),[11],[2],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 11 (⟨228,(6),[11],[2],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 11 (⟨228,(7),[11],[2],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid640 : RecordDataValid section14Catalog 11 (⟨228,(8),[11],[2],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid641 : RecordDataValid section14Catalog 11 (⟨228,(9),[11],[2],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid642 : RecordDataValid section14Catalog 11 (⟨228,(10),[11],[2],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid643 : RecordDataValid section14Catalog 11 (⟨228,(11),[11],[2],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid644 : RecordDataValid section14Catalog 11 (⟨228,(12),[11],[2],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid645 : RecordDataValid section14Catalog 11 (⟨228,(13),[11],[2],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid646 : RecordDataValid section14Catalog 11 (⟨228,(14),[11],[2],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid647 : RecordDataValid section14Catalog 11 (⟨228,(15),[11],[2],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid648 : RecordDataValid section14Catalog 11 (⟨228,(16),[11],[2],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid649 : RecordDataValid section14Catalog 11 (⟨228,(17),[11],[2],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid650 : RecordDataValid section14Catalog 11 (⟨228,(18),[11],[2],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid651 : RecordDataValid section14Catalog 11 (⟨228,(19),[11],[2],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid652 : RecordDataValid section14Catalog 11 (⟨228,(20),[11],[2],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid653 : RecordDataValid section14Catalog 11 (⟨228,(21),[11],[2],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid654 : RecordDataValid section14Catalog 11 (⟨228,(22),[11],[2],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid655 : RecordDataValid section14Catalog 11 (⟨228,(23),[11],[2],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid656 : RecordDataValid section14Catalog 11 (⟨228,(24),[11],[2],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid657 : RecordDataValid section14Catalog 11 (⟨230,(0),[11],[2],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid658 : RecordDataValid section14Catalog 11 (⟨230,(1),[11],[2],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid659 : RecordDataValid section14Catalog 11 (⟨230,(2),[11],[2],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid660 : RecordDataValid section14Catalog 11 (⟨230,(3),[11],[2],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid661 : RecordDataValid section14Catalog 11 (⟨230,(4),[11],[2],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid662 : RecordDataValid section14Catalog 11 (⟨230,(5),[11],[2],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid663 : RecordDataValid section14Catalog 11 (⟨230,(6),[11],[2],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid664 : RecordDataValid section14Catalog 11 (⟨230,(7),[11],[2],922⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨922,[2,3,7,11,14,15],926⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid665 : RecordDataValid section14Catalog 11 (⟨230,(8),[11],[2],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid666 : RecordDataValid section14Catalog 11 (⟨230,(9),[11],[2],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid667 : RecordDataValid section14Catalog 11 (⟨230,(10),[11],[2],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid668 : RecordDataValid section14Catalog 11 (⟨230,(11),[11],[2],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid669 : RecordDataValid section14Catalog 11 (⟨230,(12),[11],[2],923⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨923,[2,3,6,7,11,14,15],927⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid670 : RecordDataValid section14Catalog 11 (⟨230,(13),[11],[2],821⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid671 : RecordDataValid section14Catalog 11 (⟨230,(14),[11],[2],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 608).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 608).take 64 = [⟨227,(1),[11],[2],774⟩,⟨227,(2),[11],[2],775⟩,⟨227,(3),[11],[2],776⟩,⟨227,(4),[11],[2],775⟩,⟨227,(5),[11],[2],773⟩,⟨227,(6),[11],[2],774⟩,⟨227,(7),[11],[2],775⟩,⟨227,(8),[11],[2],776⟩,⟨227,(9),[11],[2],775⟩,⟨227,(10),[11],[2],777⟩,⟨227,(11),[11],[2],778⟩,⟨227,(12),[11],[2],779⟩,⟨227,(13),[11],[2],780⟩,⟨227,(14),[11],[2],779⟩,⟨227,(15),[11],[2],781⟩,⟨227,(16),[11],[2],782⟩,⟨227,(17),[11],[2],783⟩,⟨227,(18),[11],[2],784⟩,⟨227,(19),[11],[2],783⟩,⟨227,(20),[11],[2],785⟩,⟨227,(21),[11],[2],786⟩,⟨227,(22),[11],[2],787⟩,⟨227,(23),[11],[2],788⟩,⟨227,(24),[11],[2],787⟩,⟨228,(0),[11],[2],789⟩,⟨228,(1),[11],[2],790⟩,⟨228,(2),[11],[2],791⟩,⟨228,(3),[11],[2],792⟩,⟨228,(4),[11],[2],793⟩,⟨228,(5),[11],[2],794⟩,⟨228,(6),[11],[2],795⟩,⟨228,(7),[11],[2],796⟩,⟨228,(8),[11],[2],797⟩,⟨228,(9),[11],[2],796⟩,⟨228,(10),[11],[2],798⟩,⟨228,(11),[11],[2],799⟩,⟨228,(12),[11],[2],800⟩,⟨228,(13),[11],[2],801⟩,⟨228,(14),[11],[2],800⟩,⟨228,(15),[11],[2],802⟩,⟨228,(16),[11],[2],803⟩,⟨228,(17),[11],[2],804⟩,⟨228,(18),[11],[2],805⟩,⟨228,(19),[11],[2],804⟩,⟨228,(20),[11],[2],806⟩,⟨228,(21),[11],[2],807⟩,⟨228,(22),[11],[2],808⟩,⟨228,(23),[11],[2],809⟩,⟨228,(24),[11],[2],808⟩,⟨230,(0),[11],[2],810⟩,⟨230,(1),[11],[2],811⟩,⟨230,(2),[11],[2],812⟩,⟨230,(3),[11],[2],813⟩,⟨230,(4),[11],[2],814⟩,⟨230,(5),[11],[2],810⟩,⟨230,(6),[11],[2],811⟩,⟨230,(7),[11],[2],922⟩,⟨230,(8),[11],[2],816⟩,⟨230,(9),[11],[2],817⟩,⟨230,(10),[11],[2],818⟩,⟨230,(11),[11],[2],819⟩,⟨230,(12),[11],[2],923⟩,⟨230,(13),[11],[2],821⟩,⟨230,(14),[11],[2],817⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid608
  · exact recordValid_of_data section14Catalog 11 _ hnum valid609
  · exact recordValid_of_data section14Catalog 11 _ hnum valid610
  · exact recordValid_of_data section14Catalog 11 _ hnum valid611
  · exact recordValid_of_data section14Catalog 11 _ hnum valid612
  · exact recordValid_of_data section14Catalog 11 _ hnum valid613
  · exact recordValid_of_data section14Catalog 11 _ hnum valid614
  · exact recordValid_of_data section14Catalog 11 _ hnum valid615
  · exact recordValid_of_data section14Catalog 11 _ hnum valid616
  · exact recordValid_of_data section14Catalog 11 _ hnum valid617
  · exact recordValid_of_data section14Catalog 11 _ hnum valid618
  · exact recordValid_of_data section14Catalog 11 _ hnum valid619
  · exact recordValid_of_data section14Catalog 11 _ hnum valid620
  · exact recordValid_of_data section14Catalog 11 _ hnum valid621
  · exact recordValid_of_data section14Catalog 11 _ hnum valid622
  · exact recordValid_of_data section14Catalog 11 _ hnum valid623
  · exact recordValid_of_data section14Catalog 11 _ hnum valid624
  · exact recordValid_of_data section14Catalog 11 _ hnum valid625
  · exact recordValid_of_data section14Catalog 11 _ hnum valid626
  · exact recordValid_of_data section14Catalog 11 _ hnum valid627
  · exact recordValid_of_data section14Catalog 11 _ hnum valid628
  · exact recordValid_of_data section14Catalog 11 _ hnum valid629
  · exact recordValid_of_data section14Catalog 11 _ hnum valid630
  · exact recordValid_of_data section14Catalog 11 _ hnum valid631
  · exact recordValid_of_data section14Catalog 11 _ hnum valid632
  · exact recordValid_of_data section14Catalog 11 _ hnum valid633
  · exact recordValid_of_data section14Catalog 11 _ hnum valid634
  · exact recordValid_of_data section14Catalog 11 _ hnum valid635
  · exact recordValid_of_data section14Catalog 11 _ hnum valid636
  · exact recordValid_of_data section14Catalog 11 _ hnum valid637
  · exact recordValid_of_data section14Catalog 11 _ hnum valid638
  · exact recordValid_of_data section14Catalog 11 _ hnum valid639
  · exact recordValid_of_data section14Catalog 11 _ hnum valid640
  · exact recordValid_of_data section14Catalog 11 _ hnum valid641
  · exact recordValid_of_data section14Catalog 11 _ hnum valid642
  · exact recordValid_of_data section14Catalog 11 _ hnum valid643
  · exact recordValid_of_data section14Catalog 11 _ hnum valid644
  · exact recordValid_of_data section14Catalog 11 _ hnum valid645
  · exact recordValid_of_data section14Catalog 11 _ hnum valid646
  · exact recordValid_of_data section14Catalog 11 _ hnum valid647
  · exact recordValid_of_data section14Catalog 11 _ hnum valid648
  · exact recordValid_of_data section14Catalog 11 _ hnum valid649
  · exact recordValid_of_data section14Catalog 11 _ hnum valid650
  · exact recordValid_of_data section14Catalog 11 _ hnum valid651
  · exact recordValid_of_data section14Catalog 11 _ hnum valid652
  · exact recordValid_of_data section14Catalog 11 _ hnum valid653
  · exact recordValid_of_data section14Catalog 11 _ hnum valid654
  · exact recordValid_of_data section14Catalog 11 _ hnum valid655
  · exact recordValid_of_data section14Catalog 11 _ hnum valid656
  · exact recordValid_of_data section14Catalog 11 _ hnum valid657
  · exact recordValid_of_data section14Catalog 11 _ hnum valid658
  · exact recordValid_of_data section14Catalog 11 _ hnum valid659
  · exact recordValid_of_data section14Catalog 11 _ hnum valid660
  · exact recordValid_of_data section14Catalog 11 _ hnum valid661
  · exact recordValid_of_data section14Catalog 11 _ hnum valid662
  · exact recordValid_of_data section14Catalog 11 _ hnum valid663
  · exact recordValid_of_data section14Catalog 11 _ hnum valid664
  · exact recordValid_of_data section14Catalog 11 _ hnum valid665
  · exact recordValid_of_data section14Catalog 11 _ hnum valid666
  · exact recordValid_of_data section14Catalog 11 _ hnum valid667
  · exact recordValid_of_data section14Catalog 11 _ hnum valid668
  · exact recordValid_of_data section14Catalog 11 _ hnum valid669
  · exact recordValid_of_data section14Catalog 11 _ hnum valid670
  · exact recordValid_of_data section14Catalog 11 _ hnum valid671
end Section14Records_11_608_672

#print axioms solution
