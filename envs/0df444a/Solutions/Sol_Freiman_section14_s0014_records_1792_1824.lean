-- Prove2me | solution 1 for Freiman.section14_s0014_records_1792_1824
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T02:22:54.334984+00:00
-- url     : https://prove2.me/submissions/176d7969-4263-4e4e-a816-c89362dfaa99

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
namespace Section14Records_14_1792_1824
private theorem valid1792 : RecordDataValid section14Catalog 14 (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1793 : RecordDataValid section14Catalog 14 (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1794 : RecordDataValid section14Catalog 14 (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1795 : RecordDataValid section14Catalog 14 (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1796 : RecordDataValid section14Catalog 14 (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1797 : RecordDataValid section14Catalog 14 (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1798 : RecordDataValid section14Catalog 14 (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1799 : RecordDataValid section14Catalog 14 (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1800 : RecordDataValid section14Catalog 14 (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1801 : RecordDataValid section14Catalog 14 (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1802 : RecordDataValid section14Catalog 14 (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1803 : RecordDataValid section14Catalog 14 (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1804 : RecordDataValid section14Catalog 14 (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1805 : RecordDataValid section14Catalog 14 (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1806 : RecordDataValid section14Catalog 14 (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1807 : RecordDataValid section14Catalog 14 (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1808 : RecordDataValid section14Catalog 14 (⟨243,(5),[1,2,5,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1809 : RecordDataValid section14Catalog 14 (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1810 : RecordDataValid section14Catalog 14 (⟨243,(8),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1811 : RecordDataValid section14Catalog 14 (⟨243,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1812 : RecordDataValid section14Catalog 14 (⟨243,(15),[1,2,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1813 : RecordDataValid section14Catalog 14 (⟨243,(16),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1814 : RecordDataValid section14Catalog 14 (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1815 : RecordDataValid section14Catalog 14 (⟨243,(19),[2,5,6,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1816 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1817 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1818 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1819 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1820 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1821 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1822 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1823 : RecordDataValid section14Catalog 14 (⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 14 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1792).take 32 = [⟨238,(0),[1,2,5,6,13,14],[170],869⟩,⟨238,(1),[1,2,5,6,13,14],[170],870⟩,⟨238,(2),[1,2,5,6,13,14],[170],607⟩,⟨238,(3),[1,2,5,6,13,14],[170],871⟩,⟨238,(4),[1,2,5,6,13,14],[170],609⟩,⟨238,(5),[1,2,5,6,13,14],[170],610⟩,⟨238,(6),[1,2,5,6,13,14],[170],611⟩,⟨238,(7),[1,2,5,6,13,14],[170],612⟩,⟨238,(8),[1,2,5,6,13,14],[170],613⟩,⟨238,(9),[1,2,5,6,13,14],[170],614⟩,⟨238,(10),[1,2,5,6,13,14],[170],615⟩,⟨238,(11),[1,2,5,6,13,14],[170],616⟩,⟨238,(12),[1,2,5,6,13,14],[170],617⟩,⟨238,(13),[1,2,5,6,13,14],[170],618⟩,⟨238,(14),[1,2,5,6,13,14],[170],619⟩,⟨238,(15),[1,2,5,6,13,14],[170],620⟩,⟨243,(5),[1,2,5,6,14],[170],3⟩,⟨243,(7),[1,2,5,6,13,14],[170],3⟩,⟨243,(8),[1,5,6,13,14],[170],3⟩,⟨243,(9),[5,6,13,14],[170],143⟩,⟨243,(15),[1,2,6,14],[170],3⟩,⟨243,(16),[1,5,6,13,14],[170],3⟩,⟨243,(17),[1,2,5,6,13,14],[170],48⟩,⟨243,(19),[2,5,6,14],[170],143⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩,⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩,⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩,⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩,⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1792
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1793
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1794
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1795
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1796
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1797
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1798
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1799
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1800
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1801
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1802
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1803
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1804
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1805
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1806
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1807
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1808
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1809
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1810
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1811
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1812
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1813
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1814
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1815
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1816
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1817
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1818
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1819
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1820
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1821
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1822
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1823
end Section14Records_14_1792_1824

#print axioms solution
