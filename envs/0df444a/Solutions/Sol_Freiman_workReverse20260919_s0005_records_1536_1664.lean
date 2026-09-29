-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_1536_1664
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:11:44.185633+00:00
-- url     : https://prove2.me/submissions/e75ed91b-d672-4067-be4f-1ec9f7bfa41d

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1536_1568
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1536_1568
private theorem valid1536 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,6],[131,135],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1537 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,6,13],[194,198],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1538 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,9,13],[4],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1539 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,13],[40,56],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1540 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,13],[44],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1541 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,13],[239],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1542 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,13],[16,20],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1543 : RecordDataValid section14Catalog 5 (⟨60,(-1),[1,5,13],[195,199,211,215],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1544 : RecordDataValid section14Catalog 5 (⟨60,(-1),[2,5,6,14],[170],367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨367,[1,2,3,5,6,7,13,14,15],368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1545 : RecordDataValid section14Catalog 5 (⟨60,(-1),[5],[60],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1546 : RecordDataValid section14Catalog 5 (⟨60,(-1),[5],[255],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1547 : RecordDataValid section14Catalog 5 (⟨60,(-1),[5,6],[61],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1548 : RecordDataValid section14Catalog 5 (⟨60,(-1),[5,6],[124],71⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨71,[1,2,4,5,6,8,9,10,12,13,14,16],71⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1549 : RecordDataValid section14Catalog 5 (⟨60,(-1),[5,6],[125],72⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨72,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],72⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1550 : RecordDataValid section14Catalog 5 (⟨60,(-1),[5,6],[191],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1551 : RecordDataValid section14Catalog 5 (⟨60,(-1),[5,6],[254],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1552 : RecordDataValid section14Catalog 5 (⟨62,(0),[1,2,5,6],[150],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1553 : RecordDataValid section14Catalog 5 (⟨62,(0),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1554 : RecordDataValid section14Catalog 5 (⟨62,(1),[1,2,5,6],[150],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1555 : RecordDataValid section14Catalog 5 (⟨62,(1),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1556 : RecordDataValid section14Catalog 5 (⟨62,(2),[1,2,5,6],[150],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1557 : RecordDataValid section14Catalog 5 (⟨62,(2),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1558 : RecordDataValid section14Catalog 5 (⟨62,(3),[1,2,5,6],[150],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1559 : RecordDataValid section14Catalog 5 (⟨62,(3),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1560 : RecordDataValid section14Catalog 5 (⟨62,(4),[1,2,5,6],[150],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1561 : RecordDataValid section14Catalog 5 (⟨62,(4),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1562 : RecordDataValid section14Catalog 5 (⟨62,(5),[1,2,5,6],[150],348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨348,[1,2,3,5,6,7,9,10,11],349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1563 : RecordDataValid section14Catalog 5 (⟨62,(5),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1564 : RecordDataValid section14Catalog 5 (⟨62,(6),[1,2,5,6],[150],348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨348,[1,2,3,5,6,7,9,10,11],349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1565 : RecordDataValid section14Catalog 5 (⟨62,(6),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1566 : RecordDataValid section14Catalog 5 (⟨62,(7),[1,2,5,6],[150],348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨348,[1,2,3,5,6,7,9,10,11],349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1567 : RecordDataValid section14Catalog 5 (⟨62,(7),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1536_1568 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1536).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1536).take 32 = [⟨60,(-1),[1,5,6],[131,135],345⟩,⟨60,(-1),[1,5,6,13],[194,198],385⟩,⟨60,(-1),[1,5,9,13],[4],341⟩,⟨60,(-1),[1,5,13],[40,56],60⟩,⟨60,(-1),[1,5,13],[44],61⟩,⟨60,(-1),[1,5,13],[239],244⟩,⟨60,(-1),[1,5,13],[16,20],341⟩,⟨60,(-1),[1,5,13],[195,199,211,215],385⟩,⟨60,(-1),[2,5,6,14],[170],367⟩,⟨60,(-1),[5],[60],62⟩,⟨60,(-1),[5],[255],245⟩,⟨60,(-1),[5,6],[61],62⟩,⟨60,(-1),[5,6],[124],71⟩,⟨60,(-1),[5,6],[125],72⟩,⟨60,(-1),[5,6],[191],239⟩,⟨60,(-1),[5,6],[254],245⟩,⟨62,(0),[1,2,5,6],[150],347⟩,⟨62,(0),[1,2,5,6,13,14],[190],3⟩,⟨62,(1),[1,2,5,6],[150],347⟩,⟨62,(1),[1,2,5,6,13,14],[190],3⟩,⟨62,(2),[1,2,5,6],[150],347⟩,⟨62,(2),[1,2,5,6,13,14],[190],3⟩,⟨62,(3),[1,2,5,6],[150],347⟩,⟨62,(3),[1,2,5,6,13,14],[190],3⟩,⟨62,(4),[1,2,5,6],[150],347⟩,⟨62,(4),[1,2,5,6,13,14],[190],3⟩,⟨62,(5),[1,2,5,6],[150],348⟩,⟨62,(5),[1,2,5,6,13,14],[190],3⟩,⟨62,(6),[1,2,5,6],[150],348⟩,⟨62,(6),[1,2,5,6,13,14],[190],3⟩,⟨62,(7),[1,2,5,6],[150],348⟩,⟨62,(7),[1,2,5,6,13,14],[190],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1536
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1537
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1538
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1539
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1540
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1541
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1542
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1543
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1544
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1545
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1546
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1547
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1548
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1549
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1550
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1551
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1552
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1553
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1554
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1555
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1556
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1557
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1558
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1559
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1560
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1561
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1562
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1563
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1564
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1565
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1566
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1567
end Section14Records_5_1536_1568

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1536_1568


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1568_1600
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 5 (⟨62,(8),[1,2,5,6],[150],348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨348,[1,2,3,5,6,7,9,10,11],349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 5 (⟨62,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 5 (⟨62,(9),[1,2,5,6],[150],348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨348,[1,2,3,5,6,7,9,10,11],349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 5 (⟨62,(9),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 5 (⟨62,(10),[1,2,5,6],[150],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 5 (⟨62,(10),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 5 (⟨62,(11),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 5 (⟨62,(11),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 5 (⟨62,(12),[1,2,5,6],[150],351⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨351,[1,2,3,5,6,7,9,10,11],352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 5 (⟨62,(12),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 5 (⟨62,(13),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 5 (⟨62,(13),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 5 (⟨62,(14),[1,2,5,6],[150],352⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨352,[1,2,5,6,9,10],353⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 5 (⟨62,(14),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 5 (⟨62,(15),[1,2,5,6],[150],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 5 (⟨62,(15),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 5 (⟨62,(16),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 5 (⟨62,(16),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 5 (⟨62,(17),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 5 (⟨62,(17),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 5 (⟨62,(18),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 5 (⟨62,(18),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 5 (⟨62,(19),[1,2,5,6],[150],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 5 (⟨62,(19),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 5 (⟨62,(20),[1,2,5,6],[150],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 5 (⟨62,(20),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 5 (⟨62,(21),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 5 (⟨62,(21),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 5 (⟨62,(22),[1,2,5,6],[150],351⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨351,[1,2,3,5,6,7,9,10,11],352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 5 (⟨62,(22),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 5 (⟨62,(23),[1,2,5,6],[150],350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨350,[1,2,5,6,9,10],351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 5 (⟨62,(23),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1568_1600 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1568).take 32 = [⟨62,(8),[1,2,5,6],[150],348⟩,⟨62,(8),[1,2,5,6,13,14],[190],3⟩,⟨62,(9),[1,2,5,6],[150],348⟩,⟨62,(9),[1,2,5,6,13,14],[190],3⟩,⟨62,(10),[1,2,5,6],[150],349⟩,⟨62,(10),[1,2,5,6,13,14],[190],3⟩,⟨62,(11),[1,2,5,6],[150],350⟩,⟨62,(11),[1,2,5,6,13,14],[190],3⟩,⟨62,(12),[1,2,5,6],[150],351⟩,⟨62,(12),[1,2,5,6,13,14],[190],3⟩,⟨62,(13),[1,2,5,6],[150],350⟩,⟨62,(13),[1,2,5,6,13,14],[190],3⟩,⟨62,(14),[1,2,5,6],[150],352⟩,⟨62,(14),[1,2,5,6,13,14],[190],3⟩,⟨62,(15),[1,2,5,6],[150],349⟩,⟨62,(15),[1,2,5,6,13,14],[190],3⟩,⟨62,(16),[1,2,5,6],[150],353⟩,⟨62,(16),[1,2,5,6,13,14],[190],3⟩,⟨62,(17),[1,2,5,6],[150],353⟩,⟨62,(17),[1,2,5,6,13,14],[190],3⟩,⟨62,(18),[1,2,5,6],[150],353⟩,⟨62,(18),[1,2,5,6,13,14],[190],3⟩,⟨62,(19),[1,2,5,6],[150],353⟩,⟨62,(19),[1,2,5,6,13,14],[190],3⟩,⟨62,(20),[1,2,5,6],[150],349⟩,⟨62,(20),[1,2,5,6,13,14],[190],3⟩,⟨62,(21),[1,2,5,6],[150],350⟩,⟨62,(21),[1,2,5,6,13,14],[190],3⟩,⟨62,(22),[1,2,5,6],[150],351⟩,⟨62,(22),[1,2,5,6,13,14],[190],3⟩,⟨62,(23),[1,2,5,6],[150],350⟩,⟨62,(23),[1,2,5,6,13,14],[190],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1599
end Section14Records_5_1568_1600

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1568_1600


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1600_1632
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1600_1632
private theorem valid1600 : RecordDataValid section14Catalog 5 (⟨62,(24),[1,2,5,6],[150],352⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨352,[1,2,5,6,9,10],353⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1601 : RecordDataValid section14Catalog 5 (⟨62,(24),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1602 : RecordDataValid section14Catalog 5 (⟨64,(0),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1603 : RecordDataValid section14Catalog 5 (⟨64,(0),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1604 : RecordDataValid section14Catalog 5 (⟨64,(1),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1605 : RecordDataValid section14Catalog 5 (⟨64,(1),[1,2,5,6,13,14],[190],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1606 : RecordDataValid section14Catalog 5 (⟨64,(2),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1607 : RecordDataValid section14Catalog 5 (⟨64,(2),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1608 : RecordDataValid section14Catalog 5 (⟨64,(3),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1609 : RecordDataValid section14Catalog 5 (⟨64,(3),[1,2,5,6,13,14],[190],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1610 : RecordDataValid section14Catalog 5 (⟨64,(4),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1611 : RecordDataValid section14Catalog 5 (⟨64,(4),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1612 : RecordDataValid section14Catalog 5 (⟨64,(5),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1613 : RecordDataValid section14Catalog 5 (⟨64,(5),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1614 : RecordDataValid section14Catalog 5 (⟨64,(6),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1615 : RecordDataValid section14Catalog 5 (⟨64,(6),[1,2,5,6,13,14],[190],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1616 : RecordDataValid section14Catalog 5 (⟨64,(7),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1617 : RecordDataValid section14Catalog 5 (⟨64,(7),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1618 : RecordDataValid section14Catalog 5 (⟨64,(8),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1619 : RecordDataValid section14Catalog 5 (⟨64,(8),[1,2,5,6,13,14],[190],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1620 : RecordDataValid section14Catalog 5 (⟨64,(9),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1621 : RecordDataValid section14Catalog 5 (⟨64,(9),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1622 : RecordDataValid section14Catalog 5 (⟨64,(10),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1623 : RecordDataValid section14Catalog 5 (⟨64,(10),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1624 : RecordDataValid section14Catalog 5 (⟨64,(11),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1625 : RecordDataValid section14Catalog 5 (⟨64,(11),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1626 : RecordDataValid section14Catalog 5 (⟨64,(12),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1627 : RecordDataValid section14Catalog 5 (⟨64,(12),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1628 : RecordDataValid section14Catalog 5 (⟨64,(13),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1629 : RecordDataValid section14Catalog 5 (⟨64,(13),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1630 : RecordDataValid section14Catalog 5 (⟨64,(14),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1631 : RecordDataValid section14Catalog 5 (⟨64,(14),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1600_1632 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1600).take 32 = [⟨62,(24),[1,2,5,6],[150],352⟩,⟨62,(24),[1,2,5,6,13,14],[190],3⟩,⟨64,(0),[1,2,5,6],[150],3⟩,⟨64,(0),[1,2,5,6,13,14],[190],368⟩,⟨64,(1),[1,2,5,6],[150],3⟩,⟨64,(1),[1,2,5,6,13,14],[190],369⟩,⟨64,(2),[1,2,5,6],[150],3⟩,⟨64,(2),[1,2,5,6,13,14],[190],368⟩,⟨64,(3),[1,2,5,6],[150],3⟩,⟨64,(3),[1,2,5,6,13,14],[190],370⟩,⟨64,(4),[1,2,5,6],[150],3⟩,⟨64,(4),[1,2,5,6,13,14],[190],371⟩,⟨64,(5),[1,2,5,6],[150],3⟩,⟨64,(5),[1,2,5,6,13,14],[190],368⟩,⟨64,(6),[1,2,5,6],[150],3⟩,⟨64,(6),[1,2,5,6,13,14],[190],369⟩,⟨64,(7),[1,2,5,6],[150],3⟩,⟨64,(7),[1,2,5,6,13,14],[190],368⟩,⟨64,(8),[1,2,5,6],[150],3⟩,⟨64,(8),[1,2,5,6,13,14],[190],370⟩,⟨64,(9),[1,2,5,6],[150],3⟩,⟨64,(9),[1,2,5,6,13,14],[190],371⟩,⟨64,(10),[1,2,5,6],[150],3⟩,⟨64,(10),[1,2,5,6,13,14],[190],372⟩,⟨64,(11),[1,2,5,6],[150],3⟩,⟨64,(11),[1,2,5,6,13,14],[190],372⟩,⟨64,(12),[1,2,5,6],[150],3⟩,⟨64,(12),[1,2,5,6,13,14],[190],372⟩,⟨64,(13),[1,2,5,6],[150],3⟩,⟨64,(13),[1,2,5,6,13,14],[190],372⟩,⟨64,(14),[1,2,5,6],[150],3⟩,⟨64,(14),[1,2,5,6,13,14],[190],371⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1600
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1601
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1602
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1603
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1604
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1605
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1606
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1607
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1608
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1609
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1610
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1611
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1612
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1613
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1614
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1615
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1616
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1617
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1618
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1619
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1620
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1621
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1622
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1623
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1624
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1625
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1626
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1627
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1628
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1629
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1630
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1631
end Section14Records_5_1600_1632

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1600_1632


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1632_1664
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1632_1664
private theorem valid1632 : RecordDataValid section14Catalog 5 (⟨64,(15),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1633 : RecordDataValid section14Catalog 5 (⟨64,(15),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1634 : RecordDataValid section14Catalog 5 (⟨64,(16),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1635 : RecordDataValid section14Catalog 5 (⟨64,(16),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1636 : RecordDataValid section14Catalog 5 (⟨64,(17),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1637 : RecordDataValid section14Catalog 5 (⟨64,(17),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1638 : RecordDataValid section14Catalog 5 (⟨64,(18),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1639 : RecordDataValid section14Catalog 5 (⟨64,(18),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1640 : RecordDataValid section14Catalog 5 (⟨64,(19),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1641 : RecordDataValid section14Catalog 5 (⟨64,(19),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1642 : RecordDataValid section14Catalog 5 (⟨64,(20),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1643 : RecordDataValid section14Catalog 5 (⟨64,(20),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1644 : RecordDataValid section14Catalog 5 (⟨64,(21),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1645 : RecordDataValid section14Catalog 5 (⟨64,(21),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1646 : RecordDataValid section14Catalog 5 (⟨64,(22),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1647 : RecordDataValid section14Catalog 5 (⟨64,(22),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1648 : RecordDataValid section14Catalog 5 (⟨64,(23),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1649 : RecordDataValid section14Catalog 5 (⟨64,(23),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1650 : RecordDataValid section14Catalog 5 (⟨64,(24),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1651 : RecordDataValid section14Catalog 5 (⟨64,(24),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1652 : RecordDataValid section14Catalog 5 (⟨67,(0),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1653 : RecordDataValid section14Catalog 5 (⟨67,(0),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1654 : RecordDataValid section14Catalog 5 (⟨67,(1),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1655 : RecordDataValid section14Catalog 5 (⟨67,(1),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1656 : RecordDataValid section14Catalog 5 (⟨67,(2),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1657 : RecordDataValid section14Catalog 5 (⟨67,(2),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1658 : RecordDataValid section14Catalog 5 (⟨67,(3),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1659 : RecordDataValid section14Catalog 5 (⟨67,(3),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1660 : RecordDataValid section14Catalog 5 (⟨67,(4),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1661 : RecordDataValid section14Catalog 5 (⟨67,(4),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1662 : RecordDataValid section14Catalog 5 (⟨67,(5),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1663 : RecordDataValid section14Catalog 5 (⟨67,(5),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1632_1664 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1632).take 32 = [⟨64,(15),[1,2,5,6],[150],3⟩,⟨64,(15),[1,2,5,6,13,14],[190],373⟩,⟨64,(16),[1,2,5,6],[150],3⟩,⟨64,(16),[1,2,5,6,13,14],[190],373⟩,⟨64,(17),[1,2,5,6],[150],3⟩,⟨64,(17),[1,2,5,6,13,14],[190],373⟩,⟨64,(18),[1,2,5,6],[150],3⟩,⟨64,(18),[1,2,5,6,13,14],[190],373⟩,⟨64,(19),[1,2,5,6],[150],3⟩,⟨64,(19),[1,2,5,6,13,14],[190],373⟩,⟨64,(20),[1,2,5,6],[150],3⟩,⟨64,(20),[1,2,5,6,13,14],[190],374⟩,⟨64,(21),[1,2,5,6],[150],3⟩,⟨64,(21),[1,2,5,6,13,14],[190],374⟩,⟨64,(22),[1,2,5,6],[150],3⟩,⟨64,(22),[1,2,5,6,13,14],[190],374⟩,⟨64,(23),[1,2,5,6],[150],3⟩,⟨64,(23),[1,2,5,6,13,14],[190],374⟩,⟨64,(24),[1,2,5,6],[150],3⟩,⟨64,(24),[1,2,5,6,13,14],[190],374⟩,⟨67,(0),[1,2,5,6],[150],2⟩,⟨67,(0),[1,2,5,6,13,14],[190],2⟩,⟨67,(1),[1,2,5,6],[150],2⟩,⟨67,(1),[1,2,5,6,13,14],[190],2⟩,⟨67,(2),[1,2,5,6],[150],2⟩,⟨67,(2),[1,2,5,6,13,14],[190],2⟩,⟨67,(3),[1,2,5,6],[150],2⟩,⟨67,(3),[1,2,5,6,13,14],[190],2⟩,⟨67,(4),[1,2,5,6],[150],2⟩,⟨67,(4),[1,2,5,6,13,14],[190],2⟩,⟨67,(5),[1,2,5,6],[150],2⟩,⟨67,(5),[1,2,5,6,13,14],[190],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1632
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1633
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1634
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1635
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1636
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1637
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1638
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1639
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1640
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1641
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1642
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1643
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1644
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1645
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1646
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1647
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1648
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1649
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1650
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1651
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1652
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1653
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1654
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1655
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1656
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1657
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1658
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1659
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1660
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1661
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1662
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1663
end Section14Records_5_1632_1664

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1632_1664

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1536).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 1536 1600 1664 (by decide) (by decide) (all_of_interval_split P xs 1536 1568 1600 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_1536_1568 hnum) (Freiman.workReverse20260919_s0005_records_1568_1600 hnum)) (all_of_interval_split P xs 1600 1632 1664 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_1600_1632 hnum) (Freiman.workReverse20260919_s0005_records_1632_1664 hnum)))

#print axioms solution
