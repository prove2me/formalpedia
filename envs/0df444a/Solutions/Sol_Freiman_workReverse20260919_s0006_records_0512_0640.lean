-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_0512_0640
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:47:41.929378+00:00
-- url     : https://prove2.me/submissions/d5242160-c50c-4014-90b2-3e54fb4ea35a

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0512_0544
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_512_544
private theorem valid512 : RecordDataValid section14Catalog 6 (⟨28,(5),[6],[146],1521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1521,[6],1526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid513 : RecordDataValid section14Catalog 6 (⟨28,(6),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid514 : RecordDataValid section14Catalog 6 (⟨28,(6),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid515 : RecordDataValid section14Catalog 6 (⟨28,(6),[2,6],[130],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid516 : RecordDataValid section14Catalog 6 (⟨28,(6),[6],[146],1521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1521,[6],1526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid517 : RecordDataValid section14Catalog 6 (⟨28,(7),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid518 : RecordDataValid section14Catalog 6 (⟨28,(7),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid519 : RecordDataValid section14Catalog 6 (⟨28,(7),[2,6],[130],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid520 : RecordDataValid section14Catalog 6 (⟨28,(7),[6],[146],1521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1521,[6],1526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid521 : RecordDataValid section14Catalog 6 (⟨28,(8),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid522 : RecordDataValid section14Catalog 6 (⟨28,(8),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid523 : RecordDataValid section14Catalog 6 (⟨28,(8),[2,6],[130],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid524 : RecordDataValid section14Catalog 6 (⟨28,(8),[6],[146],1521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1521,[6],1526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid525 : RecordDataValid section14Catalog 6 (⟨28,(9),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid526 : RecordDataValid section14Catalog 6 (⟨28,(9),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid527 : RecordDataValid section14Catalog 6 (⟨28,(9),[2,6],[130],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid528 : RecordDataValid section14Catalog 6 (⟨28,(9),[6],[146],1521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1521,[6],1526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid529 : RecordDataValid section14Catalog 6 (⟨28,(10),[1,2,5,6],[131],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid530 : RecordDataValid section14Catalog 6 (⟨28,(10),[1,2,5,6],[150],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid531 : RecordDataValid section14Catalog 6 (⟨28,(10),[2,6],[130],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid532 : RecordDataValid section14Catalog 6 (⟨28,(10),[6],[146],1522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1522,[6],1527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid533 : RecordDataValid section14Catalog 6 (⟨28,(11),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid534 : RecordDataValid section14Catalog 6 (⟨28,(11),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid535 : RecordDataValid section14Catalog 6 (⟨28,(11),[2,6],[130],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid536 : RecordDataValid section14Catalog 6 (⟨28,(11),[6],[146],1523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1523,[6],1528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid537 : RecordDataValid section14Catalog 6 (⟨28,(12),[1,2,5,6],[131],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid538 : RecordDataValid section14Catalog 6 (⟨28,(12),[1,2,5,6],[150],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid539 : RecordDataValid section14Catalog 6 (⟨28,(12),[2,6],[130],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid540 : RecordDataValid section14Catalog 6 (⟨28,(12),[6],[146],1524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1524,[6],1529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid541 : RecordDataValid section14Catalog 6 (⟨28,(13),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid542 : RecordDataValid section14Catalog 6 (⟨28,(13),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid543 : RecordDataValid section14Catalog 6 (⟨28,(13),[2,6],[130],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0512_0544 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 512).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 512).take 32 = [⟨28,(5),[6],[146],1521⟩,⟨28,(6),[1,2,5,6],[131],114⟩,⟨28,(6),[1,2,5,6],[150],133⟩,⟨28,(6),[2,6],[130],114⟩,⟨28,(6),[6],[146],1521⟩,⟨28,(7),[1,2,5,6],[131],114⟩,⟨28,(7),[1,2,5,6],[150],133⟩,⟨28,(7),[2,6],[130],114⟩,⟨28,(7),[6],[146],1521⟩,⟨28,(8),[1,2,5,6],[131],114⟩,⟨28,(8),[1,2,5,6],[150],133⟩,⟨28,(8),[2,6],[130],114⟩,⟨28,(8),[6],[146],1521⟩,⟨28,(9),[1,2,5,6],[131],114⟩,⟨28,(9),[1,2,5,6],[150],133⟩,⟨28,(9),[2,6],[130],114⟩,⟨28,(9),[6],[146],1521⟩,⟨28,(10),[1,2,5,6],[131],115⟩,⟨28,(10),[1,2,5,6],[150],134⟩,⟨28,(10),[2,6],[130],115⟩,⟨28,(10),[6],[146],1522⟩,⟨28,(11),[1,2,5,6],[131],116⟩,⟨28,(11),[1,2,5,6],[150],135⟩,⟨28,(11),[2,6],[130],116⟩,⟨28,(11),[6],[146],1523⟩,⟨28,(12),[1,2,5,6],[131],117⟩,⟨28,(12),[1,2,5,6],[150],136⟩,⟨28,(12),[2,6],[130],117⟩,⟨28,(12),[6],[146],1524⟩,⟨28,(13),[1,2,5,6],[131],116⟩,⟨28,(13),[1,2,5,6],[150],135⟩,⟨28,(13),[2,6],[130],116⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid512
  · exact recordValid_of_data section14Catalog 6 _ hnum valid513
  · exact recordValid_of_data section14Catalog 6 _ hnum valid514
  · exact recordValid_of_data section14Catalog 6 _ hnum valid515
  · exact recordValid_of_data section14Catalog 6 _ hnum valid516
  · exact recordValid_of_data section14Catalog 6 _ hnum valid517
  · exact recordValid_of_data section14Catalog 6 _ hnum valid518
  · exact recordValid_of_data section14Catalog 6 _ hnum valid519
  · exact recordValid_of_data section14Catalog 6 _ hnum valid520
  · exact recordValid_of_data section14Catalog 6 _ hnum valid521
  · exact recordValid_of_data section14Catalog 6 _ hnum valid522
  · exact recordValid_of_data section14Catalog 6 _ hnum valid523
  · exact recordValid_of_data section14Catalog 6 _ hnum valid524
  · exact recordValid_of_data section14Catalog 6 _ hnum valid525
  · exact recordValid_of_data section14Catalog 6 _ hnum valid526
  · exact recordValid_of_data section14Catalog 6 _ hnum valid527
  · exact recordValid_of_data section14Catalog 6 _ hnum valid528
  · exact recordValid_of_data section14Catalog 6 _ hnum valid529
  · exact recordValid_of_data section14Catalog 6 _ hnum valid530
  · exact recordValid_of_data section14Catalog 6 _ hnum valid531
  · exact recordValid_of_data section14Catalog 6 _ hnum valid532
  · exact recordValid_of_data section14Catalog 6 _ hnum valid533
  · exact recordValid_of_data section14Catalog 6 _ hnum valid534
  · exact recordValid_of_data section14Catalog 6 _ hnum valid535
  · exact recordValid_of_data section14Catalog 6 _ hnum valid536
  · exact recordValid_of_data section14Catalog 6 _ hnum valid537
  · exact recordValid_of_data section14Catalog 6 _ hnum valid538
  · exact recordValid_of_data section14Catalog 6 _ hnum valid539
  · exact recordValid_of_data section14Catalog 6 _ hnum valid540
  · exact recordValid_of_data section14Catalog 6 _ hnum valid541
  · exact recordValid_of_data section14Catalog 6 _ hnum valid542
  · exact recordValid_of_data section14Catalog 6 _ hnum valid543
end Section14Records_6_512_544

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0512_0544


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0544_0576
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_544_576
private theorem valid544 : RecordDataValid section14Catalog 6 (⟨28,(13),[6],[146],1523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1523,[6],1528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid545 : RecordDataValid section14Catalog 6 (⟨28,(14),[1,2,5,6],[131],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid546 : RecordDataValid section14Catalog 6 (⟨28,(14),[1,2,5,6],[150],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid547 : RecordDataValid section14Catalog 6 (⟨28,(14),[2,6],[130],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid548 : RecordDataValid section14Catalog 6 (⟨28,(14),[6],[146],1525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1525,[6],1530⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid549 : RecordDataValid section14Catalog 6 (⟨28,(15),[1,2,5,6],[131],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid550 : RecordDataValid section14Catalog 6 (⟨28,(15),[1,2,5,6],[150],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid551 : RecordDataValid section14Catalog 6 (⟨28,(15),[2,6],[130],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid552 : RecordDataValid section14Catalog 6 (⟨28,(15),[6],[146],1522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1522,[6],1527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid553 : RecordDataValid section14Catalog 6 (⟨28,(16),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid554 : RecordDataValid section14Catalog 6 (⟨28,(16),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid555 : RecordDataValid section14Catalog 6 (⟨28,(16),[2,6],[130],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid556 : RecordDataValid section14Catalog 6 (⟨28,(16),[6],[146],1526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1526,[6],1531⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid557 : RecordDataValid section14Catalog 6 (⟨28,(17),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid558 : RecordDataValid section14Catalog 6 (⟨28,(17),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid559 : RecordDataValid section14Catalog 6 (⟨28,(17),[2,6],[130],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid560 : RecordDataValid section14Catalog 6 (⟨28,(17),[6],[146],1526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1526,[6],1531⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid561 : RecordDataValid section14Catalog 6 (⟨28,(18),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid562 : RecordDataValid section14Catalog 6 (⟨28,(18),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid563 : RecordDataValid section14Catalog 6 (⟨28,(18),[2,6],[130],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid564 : RecordDataValid section14Catalog 6 (⟨28,(18),[6],[146],1526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1526,[6],1531⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid565 : RecordDataValid section14Catalog 6 (⟨28,(19),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid566 : RecordDataValid section14Catalog 6 (⟨28,(19),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid567 : RecordDataValid section14Catalog 6 (⟨28,(19),[2,6],[130],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid568 : RecordDataValid section14Catalog 6 (⟨28,(19),[6],[146],1526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1526,[6],1531⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid569 : RecordDataValid section14Catalog 6 (⟨28,(20),[1,2,5,6],[131],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid570 : RecordDataValid section14Catalog 6 (⟨28,(20),[1,2,5,6],[150],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid571 : RecordDataValid section14Catalog 6 (⟨28,(20),[2,6],[130],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid572 : RecordDataValid section14Catalog 6 (⟨28,(20),[6],[146],1522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1522,[6],1527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid573 : RecordDataValid section14Catalog 6 (⟨28,(21),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid574 : RecordDataValid section14Catalog 6 (⟨28,(21),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid575 : RecordDataValid section14Catalog 6 (⟨28,(21),[2,6],[130],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0544_0576 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 544).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 544).take 32 = [⟨28,(13),[6],[146],1523⟩,⟨28,(14),[1,2,5,6],[131],118⟩,⟨28,(14),[1,2,5,6],[150],137⟩,⟨28,(14),[2,6],[130],118⟩,⟨28,(14),[6],[146],1525⟩,⟨28,(15),[1,2,5,6],[131],115⟩,⟨28,(15),[1,2,5,6],[150],134⟩,⟨28,(15),[2,6],[130],115⟩,⟨28,(15),[6],[146],1522⟩,⟨28,(16),[1,2,5,6],[131],119⟩,⟨28,(16),[1,2,5,6],[150],138⟩,⟨28,(16),[2,6],[130],119⟩,⟨28,(16),[6],[146],1526⟩,⟨28,(17),[1,2,5,6],[131],119⟩,⟨28,(17),[1,2,5,6],[150],138⟩,⟨28,(17),[2,6],[130],119⟩,⟨28,(17),[6],[146],1526⟩,⟨28,(18),[1,2,5,6],[131],119⟩,⟨28,(18),[1,2,5,6],[150],138⟩,⟨28,(18),[2,6],[130],119⟩,⟨28,(18),[6],[146],1526⟩,⟨28,(19),[1,2,5,6],[131],119⟩,⟨28,(19),[1,2,5,6],[150],138⟩,⟨28,(19),[2,6],[130],119⟩,⟨28,(19),[6],[146],1526⟩,⟨28,(20),[1,2,5,6],[131],115⟩,⟨28,(20),[1,2,5,6],[150],134⟩,⟨28,(20),[2,6],[130],115⟩,⟨28,(20),[6],[146],1522⟩,⟨28,(21),[1,2,5,6],[131],116⟩,⟨28,(21),[1,2,5,6],[150],135⟩,⟨28,(21),[2,6],[130],116⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid544
  · exact recordValid_of_data section14Catalog 6 _ hnum valid545
  · exact recordValid_of_data section14Catalog 6 _ hnum valid546
  · exact recordValid_of_data section14Catalog 6 _ hnum valid547
  · exact recordValid_of_data section14Catalog 6 _ hnum valid548
  · exact recordValid_of_data section14Catalog 6 _ hnum valid549
  · exact recordValid_of_data section14Catalog 6 _ hnum valid550
  · exact recordValid_of_data section14Catalog 6 _ hnum valid551
  · exact recordValid_of_data section14Catalog 6 _ hnum valid552
  · exact recordValid_of_data section14Catalog 6 _ hnum valid553
  · exact recordValid_of_data section14Catalog 6 _ hnum valid554
  · exact recordValid_of_data section14Catalog 6 _ hnum valid555
  · exact recordValid_of_data section14Catalog 6 _ hnum valid556
  · exact recordValid_of_data section14Catalog 6 _ hnum valid557
  · exact recordValid_of_data section14Catalog 6 _ hnum valid558
  · exact recordValid_of_data section14Catalog 6 _ hnum valid559
  · exact recordValid_of_data section14Catalog 6 _ hnum valid560
  · exact recordValid_of_data section14Catalog 6 _ hnum valid561
  · exact recordValid_of_data section14Catalog 6 _ hnum valid562
  · exact recordValid_of_data section14Catalog 6 _ hnum valid563
  · exact recordValid_of_data section14Catalog 6 _ hnum valid564
  · exact recordValid_of_data section14Catalog 6 _ hnum valid565
  · exact recordValid_of_data section14Catalog 6 _ hnum valid566
  · exact recordValid_of_data section14Catalog 6 _ hnum valid567
  · exact recordValid_of_data section14Catalog 6 _ hnum valid568
  · exact recordValid_of_data section14Catalog 6 _ hnum valid569
  · exact recordValid_of_data section14Catalog 6 _ hnum valid570
  · exact recordValid_of_data section14Catalog 6 _ hnum valid571
  · exact recordValid_of_data section14Catalog 6 _ hnum valid572
  · exact recordValid_of_data section14Catalog 6 _ hnum valid573
  · exact recordValid_of_data section14Catalog 6 _ hnum valid574
  · exact recordValid_of_data section14Catalog 6 _ hnum valid575
end Section14Records_6_544_576

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0544_0576


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0576_0608
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_576_608
private theorem valid576 : RecordDataValid section14Catalog 6 (⟨28,(21),[6],[146],1523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1523,[6],1528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid577 : RecordDataValid section14Catalog 6 (⟨28,(22),[1,2,5,6],[131],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid578 : RecordDataValid section14Catalog 6 (⟨28,(22),[1,2,5,6],[150],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid579 : RecordDataValid section14Catalog 6 (⟨28,(22),[2,6],[130],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid580 : RecordDataValid section14Catalog 6 (⟨28,(22),[6],[146],1524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1524,[6],1529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid581 : RecordDataValid section14Catalog 6 (⟨28,(23),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid582 : RecordDataValid section14Catalog 6 (⟨28,(23),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid583 : RecordDataValid section14Catalog 6 (⟨28,(23),[2,6],[130],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid584 : RecordDataValid section14Catalog 6 (⟨28,(23),[6],[146],1523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1523,[6],1528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid585 : RecordDataValid section14Catalog 6 (⟨28,(24),[1,2,5,6],[131],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid586 : RecordDataValid section14Catalog 6 (⟨28,(24),[1,2,5,6],[150],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid587 : RecordDataValid section14Catalog 6 (⟨28,(24),[2,6],[130],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid588 : RecordDataValid section14Catalog 6 (⟨28,(24),[6],[146],1525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1525,[6],1530⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid589 : RecordDataValid section14Catalog 6 (⟨30,(0),[1,2,5,6],[146,150],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid590 : RecordDataValid section14Catalog 6 (⟨30,(0),[1,6],[131],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid591 : RecordDataValid section14Catalog 6 (⟨30,(0),[5,6],[130],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid592 : RecordDataValid section14Catalog 6 (⟨30,(1),[1,2,5,6],[146,150],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid593 : RecordDataValid section14Catalog 6 (⟨30,(1),[5,6],[130],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid594 : RecordDataValid section14Catalog 6 (⟨30,(1),[6],[131],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid595 : RecordDataValid section14Catalog 6 (⟨30,(2),[1,2,5,6],[130],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid596 : RecordDataValid section14Catalog 6 (⟨30,(2),[1,2,5,6],[146],154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨154,[1,2,3,5,6,7],154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid597 : RecordDataValid section14Catalog 6 (⟨30,(2),[1,2,5,6],[150],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid598 : RecordDataValid section14Catalog 6 (⟨30,(2),[1,5,6],[131],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid599 : RecordDataValid section14Catalog 6 (⟨30,(3),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid600 : RecordDataValid section14Catalog 6 (⟨30,(3),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid601 : RecordDataValid section14Catalog 6 (⟨30,(3),[5,6],[131],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid602 : RecordDataValid section14Catalog 6 (⟨30,(3),[5,6],[150],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid603 : RecordDataValid section14Catalog 6 (⟨30,(4),[1,2,5,6],[130],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid604 : RecordDataValid section14Catalog 6 (⟨30,(4),[1,2,5,6],[146],156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨156,[1,2,3,5,6,7],156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid605 : RecordDataValid section14Catalog 6 (⟨30,(4),[5,6],[131],182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨182,[1,2,5,6,9,10],182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid606 : RecordDataValid section14Catalog 6 (⟨30,(4),[5,6],[150],231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨231,[1,2,3,4,5,6,7,8,9,10,11,12],231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid607 : RecordDataValid section14Catalog 6 (⟨30,(5),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0576_0608 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 576).take 32 = [⟨28,(21),[6],[146],1523⟩,⟨28,(22),[1,2,5,6],[131],117⟩,⟨28,(22),[1,2,5,6],[150],136⟩,⟨28,(22),[2,6],[130],117⟩,⟨28,(22),[6],[146],1524⟩,⟨28,(23),[1,2,5,6],[131],116⟩,⟨28,(23),[1,2,5,6],[150],135⟩,⟨28,(23),[2,6],[130],116⟩,⟨28,(23),[6],[146],1523⟩,⟨28,(24),[1,2,5,6],[131],118⟩,⟨28,(24),[1,2,5,6],[150],137⟩,⟨28,(24),[2,6],[130],118⟩,⟨28,(24),[6],[146],1525⟩,⟨30,(0),[1,2,5,6],[146,150],152⟩,⟨30,(0),[1,6],[131],120⟩,⟨30,(0),[5,6],[130],152⟩,⟨30,(1),[1,2,5,6],[146,150],153⟩,⟨30,(1),[5,6],[130],153⟩,⟨30,(1),[6],[131],181⟩,⟨30,(2),[1,2,5,6],[130],92⟩,⟨30,(2),[1,2,5,6],[146],154⟩,⟨30,(2),[1,2,5,6],[150],200⟩,⟨30,(2),[1,5,6],[131],120⟩,⟨30,(3),[1,2,5,6],[130],93⟩,⟨30,(3),[1,2,5,6],[146],155⟩,⟨30,(3),[5,6],[131],181⟩,⟨30,(3),[5,6],[150],230⟩,⟨30,(4),[1,2,5,6],[130],94⟩,⟨30,(4),[1,2,5,6],[146],156⟩,⟨30,(4),[5,6],[131],182⟩,⟨30,(4),[5,6],[150],231⟩,⟨30,(5),[1,2,5,6],[130],93⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid576
  · exact recordValid_of_data section14Catalog 6 _ hnum valid577
  · exact recordValid_of_data section14Catalog 6 _ hnum valid578
  · exact recordValid_of_data section14Catalog 6 _ hnum valid579
  · exact recordValid_of_data section14Catalog 6 _ hnum valid580
  · exact recordValid_of_data section14Catalog 6 _ hnum valid581
  · exact recordValid_of_data section14Catalog 6 _ hnum valid582
  · exact recordValid_of_data section14Catalog 6 _ hnum valid583
  · exact recordValid_of_data section14Catalog 6 _ hnum valid584
  · exact recordValid_of_data section14Catalog 6 _ hnum valid585
  · exact recordValid_of_data section14Catalog 6 _ hnum valid586
  · exact recordValid_of_data section14Catalog 6 _ hnum valid587
  · exact recordValid_of_data section14Catalog 6 _ hnum valid588
  · exact recordValid_of_data section14Catalog 6 _ hnum valid589
  · exact recordValid_of_data section14Catalog 6 _ hnum valid590
  · exact recordValid_of_data section14Catalog 6 _ hnum valid591
  · exact recordValid_of_data section14Catalog 6 _ hnum valid592
  · exact recordValid_of_data section14Catalog 6 _ hnum valid593
  · exact recordValid_of_data section14Catalog 6 _ hnum valid594
  · exact recordValid_of_data section14Catalog 6 _ hnum valid595
  · exact recordValid_of_data section14Catalog 6 _ hnum valid596
  · exact recordValid_of_data section14Catalog 6 _ hnum valid597
  · exact recordValid_of_data section14Catalog 6 _ hnum valid598
  · exact recordValid_of_data section14Catalog 6 _ hnum valid599
  · exact recordValid_of_data section14Catalog 6 _ hnum valid600
  · exact recordValid_of_data section14Catalog 6 _ hnum valid601
  · exact recordValid_of_data section14Catalog 6 _ hnum valid602
  · exact recordValid_of_data section14Catalog 6 _ hnum valid603
  · exact recordValid_of_data section14Catalog 6 _ hnum valid604
  · exact recordValid_of_data section14Catalog 6 _ hnum valid605
  · exact recordValid_of_data section14Catalog 6 _ hnum valid606
  · exact recordValid_of_data section14Catalog 6 _ hnum valid607
end Section14Records_6_576_608

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0576_0608


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0608_0640
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_608_640
private theorem valid608 : RecordDataValid section14Catalog 6 (⟨30,(5),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 6 (⟨30,(5),[5,6],[131],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 6 (⟨30,(5),[5,6],[150],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 6 (⟨30,(6),[1,2,5,6],[130],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 6 (⟨30,(6),[1,2,5,6],[146],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 6 (⟨30,(6),[5,6],[131],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 6 (⟨30,(6),[5,6],[150],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 6 (⟨30,(7),[1,2,5,6],[130],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 6 (⟨30,(7),[1,2,5,6],[146],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 6 (⟨30,(7),[5,6],[131],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 6 (⟨30,(7),[5,6],[150],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 6 (⟨30,(8),[1,2,5,6],[130],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 6 (⟨30,(8),[1,2,5,6],[146],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 6 (⟨30,(8),[5,6],[131],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 6 (⟨30,(8),[5,6],[150],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 6 (⟨30,(9),[1,2,5,6],[130],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 6 (⟨30,(9),[1,2,5,6],[146],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 6 (⟨30,(9),[5,6],[131],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 6 (⟨30,(9),[5,6],[150],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 6 (⟨33,(0),[1,2,5,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 6 (⟨33,(0),[1,2,5,6,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 6 (⟨33,(0),[1,5,6],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 6 (⟨33,(1),[1,5,6],[130,131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 6 (⟨33,(1),[2,5,6,14],[146,150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 6 (⟨33,(2),[1,5,6,13,14],[146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 6 (⟨33,(2),[2,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 6 (⟨33,(2),[2,6,13,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 6 (⟨33,(3),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 6 (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 6 (⟨33,(4),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 6 (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 6 (⟨33,(4),[1,5,6],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0608_0640 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 608).take 32 = [⟨30,(5),[1,2,5,6],[146],155⟩,⟨30,(5),[5,6],[131],181⟩,⟨30,(5),[5,6],[150],230⟩,⟨30,(6),[1,2,5,6],[130],95⟩,⟨30,(6),[1,2,5,6],[146],157⟩,⟨30,(6),[5,6],[131],183⟩,⟨30,(6),[5,6],[150],232⟩,⟨30,(7),[1,2,5,6],[130],95⟩,⟨30,(7),[1,2,5,6],[146],157⟩,⟨30,(7),[5,6],[131],183⟩,⟨30,(7),[5,6],[150],232⟩,⟨30,(8),[1,2,5,6],[130],96⟩,⟨30,(8),[1,2,5,6],[146],158⟩,⟨30,(8),[5,6],[131],184⟩,⟨30,(8),[5,6],[150],233⟩,⟨30,(9),[1,2,5,6],[130],96⟩,⟨30,(9),[1,2,5,6],[146],158⟩,⟨30,(9),[5,6],[131],184⟩,⟨30,(9),[5,6],[150],233⟩,⟨33,(0),[1,2,5,6],[130],97⟩,⟨33,(0),[1,2,5,6,14],[131],97⟩,⟨33,(0),[1,5,6],[146,150],98⟩,⟨33,(1),[1,5,6],[130,131],98⟩,⟨33,(1),[2,5,6,14],[146,150],159⟩,⟨33,(2),[1,5,6,13,14],[146,150],3⟩,⟨33,(2),[2,6],[130],97⟩,⟨33,(2),[2,6,13,14],[131],97⟩,⟨33,(3),[1,5,6],[130],3⟩,⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(4),[1,2,5,6],[130],2⟩,⟨33,(4),[1,2,5,6,13,14],[131],2⟩,⟨33,(4),[1,5,6],[146,150],98⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid608
  · exact recordValid_of_data section14Catalog 6 _ hnum valid609
  · exact recordValid_of_data section14Catalog 6 _ hnum valid610
  · exact recordValid_of_data section14Catalog 6 _ hnum valid611
  · exact recordValid_of_data section14Catalog 6 _ hnum valid612
  · exact recordValid_of_data section14Catalog 6 _ hnum valid613
  · exact recordValid_of_data section14Catalog 6 _ hnum valid614
  · exact recordValid_of_data section14Catalog 6 _ hnum valid615
  · exact recordValid_of_data section14Catalog 6 _ hnum valid616
  · exact recordValid_of_data section14Catalog 6 _ hnum valid617
  · exact recordValid_of_data section14Catalog 6 _ hnum valid618
  · exact recordValid_of_data section14Catalog 6 _ hnum valid619
  · exact recordValid_of_data section14Catalog 6 _ hnum valid620
  · exact recordValid_of_data section14Catalog 6 _ hnum valid621
  · exact recordValid_of_data section14Catalog 6 _ hnum valid622
  · exact recordValid_of_data section14Catalog 6 _ hnum valid623
  · exact recordValid_of_data section14Catalog 6 _ hnum valid624
  · exact recordValid_of_data section14Catalog 6 _ hnum valid625
  · exact recordValid_of_data section14Catalog 6 _ hnum valid626
  · exact recordValid_of_data section14Catalog 6 _ hnum valid627
  · exact recordValid_of_data section14Catalog 6 _ hnum valid628
  · exact recordValid_of_data section14Catalog 6 _ hnum valid629
  · exact recordValid_of_data section14Catalog 6 _ hnum valid630
  · exact recordValid_of_data section14Catalog 6 _ hnum valid631
  · exact recordValid_of_data section14Catalog 6 _ hnum valid632
  · exact recordValid_of_data section14Catalog 6 _ hnum valid633
  · exact recordValid_of_data section14Catalog 6 _ hnum valid634
  · exact recordValid_of_data section14Catalog 6 _ hnum valid635
  · exact recordValid_of_data section14Catalog 6 _ hnum valid636
  · exact recordValid_of_data section14Catalog 6 _ hnum valid637
  · exact recordValid_of_data section14Catalog 6 _ hnum valid638
  · exact recordValid_of_data section14Catalog 6 _ hnum valid639
end Section14Records_6_608_640

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0608_0640

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 512).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 512 576 640 (by decide) (by decide) (all_of_interval_split P xs 512 544 576 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0512_0544 hnum) (Freiman.workReverse20260919_s0006_records_0544_0576 hnum)) (all_of_interval_split P xs 576 608 640 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0576_0608 hnum) (Freiman.workReverse20260919_s0006_records_0608_0640 hnum)))

#print axioms solution
