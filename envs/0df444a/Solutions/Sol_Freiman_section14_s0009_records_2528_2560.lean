-- Prove2me | solution 1 for Freiman.section14_s0009_records_2528_2560
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:35:16.814977+00:00
-- url     : https://prove2.me/submissions/4ba145d1-9a7e-4041-ba75-49635cb01667

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
namespace Section14Records_9_2528_2560
private theorem valid2528 : RecordDataValid section14Catalog 9 (⟨280,(6),[9],[42],1429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1429,[5,8,9,12],1434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2529 : RecordDataValid section14Catalog 9 (⟨280,(7),[9],[42],1429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1429,[5,8,9,12],1434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2530 : RecordDataValid section14Catalog 9 (⟨280,(8),[9],[42],1427⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1427,[5,8,9,12],1432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2531 : RecordDataValid section14Catalog 9 (⟨280,(9),[9],[42],1428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1428,[5,8,9,12],1433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2532 : RecordDataValid section14Catalog 9 (⟨283,(0),[9],[42],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2533 : RecordDataValid section14Catalog 9 (⟨283,(1),[9],[42],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2534 : RecordDataValid section14Catalog 9 (⟨283,(2),[9],[42],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2535 : RecordDataValid section14Catalog 9 (⟨283,(3),[9],[42],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2536 : RecordDataValid section14Catalog 9 (⟨283,(4),[9],[42],1123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1123,[3,5,7,8,9,11,12,15],1127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2537 : RecordDataValid section14Catalog 9 (⟨283,(5),[9],[42],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2538 : RecordDataValid section14Catalog 9 (⟨283,(6),[9],[42],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2539 : RecordDataValid section14Catalog 9 (⟨283,(7),[9],[42],1124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1124,[3,5,7,8,9,11,12,15],1128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2540 : RecordDataValid section14Catalog 9 (⟨283,(8),[9],[42],1125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1125,[3,5,7,8,9,11,12,15],1129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2541 : RecordDataValid section14Catalog 9 (⟨283,(9),[9],[42],1126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1126,[3,5,7,8,9,11,12,15],1130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2542 : RecordDataValid section14Catalog 9 (⟨285,(0),[9],[42],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2543 : RecordDataValid section14Catalog 9 (⟨285,(1),[9],[42],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2544 : RecordDataValid section14Catalog 9 (⟨285,(2),[9],[42],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2545 : RecordDataValid section14Catalog 9 (⟨285,(3),[9],[42],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2546 : RecordDataValid section14Catalog 9 (⟨285,(4),[9],[42],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2547 : RecordDataValid section14Catalog 9 (⟨285,(5),[9],[42],1434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1434,[5,8,9,12],1439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2548 : RecordDataValid section14Catalog 9 (⟨285,(6),[9],[42],1434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1434,[5,8,9,12],1439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2549 : RecordDataValid section14Catalog 9 (⟨285,(7),[9],[42],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2550 : RecordDataValid section14Catalog 9 (⟨285,(8),[9],[42],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2551 : RecordDataValid section14Catalog 9 (⟨285,(9),[9],[42],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2552 : RecordDataValid section14Catalog 9 (⟨285,(10),[9],[42],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2553 : RecordDataValid section14Catalog 9 (⟨285,(11),[9],[42],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2554 : RecordDataValid section14Catalog 9 (⟨285,(12),[9],[42],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2555 : RecordDataValid section14Catalog 9 (⟨285,(13),[9],[42],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2556 : RecordDataValid section14Catalog 9 (⟨285,(14),[9],[42],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2557 : RecordDataValid section14Catalog 9 (⟨285,(15),[9],[42],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2558 : RecordDataValid section14Catalog 9 (⟨285,(16),[9],[42],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2559 : RecordDataValid section14Catalog 9 (⟨285,(17),[9],[42],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2528).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2528).take 32 = [⟨280,(6),[9],[42],1429⟩,⟨280,(7),[9],[42],1429⟩,⟨280,(8),[9],[42],1427⟩,⟨280,(9),[9],[42],1428⟩,⟨283,(0),[9],[42],1120⟩,⟨283,(1),[9],[42],1121⟩,⟨283,(2),[9],[42],1122⟩,⟨283,(3),[9],[42],1122⟩,⟨283,(4),[9],[42],1123⟩,⟨283,(5),[9],[42],1120⟩,⟨283,(6),[9],[42],1121⟩,⟨283,(7),[9],[42],1124⟩,⟨283,(8),[9],[42],1125⟩,⟨283,(9),[9],[42],1126⟩,⟨285,(0),[9],[42],1430⟩,⟨285,(1),[9],[42],1430⟩,⟨285,(2),[9],[42],1431⟩,⟨285,(3),[9],[42],1432⟩,⟨285,(4),[9],[42],1433⟩,⟨285,(5),[9],[42],1434⟩,⟨285,(6),[9],[42],1434⟩,⟨285,(7),[9],[42],1431⟩,⟨285,(8),[9],[42],1432⟩,⟨285,(9),[9],[42],1433⟩,⟨285,(10),[9],[42],1430⟩,⟨285,(11),[9],[42],1430⟩,⟨285,(12),[9],[42],1431⟩,⟨285,(13),[9],[42],1432⟩,⟨285,(14),[9],[42],1433⟩,⟨285,(15),[9],[42],1435⟩,⟨285,(16),[9],[42],1435⟩,⟨285,(17),[9],[42],1431⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2528
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2529
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2530
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2531
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2532
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2533
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2534
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2535
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2536
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2537
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2538
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2539
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2540
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2541
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2542
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2543
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2544
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2545
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2546
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2547
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2548
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2549
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2550
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2551
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2552
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2553
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2554
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2555
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2556
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2557
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2558
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2559
end Section14Records_9_2528_2560

#print axioms solution
