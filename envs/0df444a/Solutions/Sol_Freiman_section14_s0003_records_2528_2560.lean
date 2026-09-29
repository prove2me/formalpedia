-- Prove2me | solution 1 for Freiman.section14_s0003_records_2528_2560
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:49:06.285462+00:00
-- url     : https://prove2.me/submissions/47da5e03-fcdd-4137-8657-ac7c146ede4f

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
namespace Section14Records_3_2528_2560
private theorem valid2528 : RecordDataValid section14Catalog 3 (⟨453,(15),[3,7,15],[10],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2529 : RecordDataValid section14Catalog 3 (⟨455,(0),[3],[10],1177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1177,[3,7,11],1181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2530 : RecordDataValid section14Catalog 3 (⟨455,(1),[3,7],[10],1178⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1178,[3,7,11],1182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2531 : RecordDataValid section14Catalog 3 (⟨455,(2),[3,7],[10],1177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1177,[3,7,11],1181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2532 : RecordDataValid section14Catalog 3 (⟨455,(3),[3,7],[10],1179⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1179,[3,7,11],1183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2533 : RecordDataValid section14Catalog 3 (⟨458,(0),[3,7],[10],1180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1180,[3,7,11],1184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2534 : RecordDataValid section14Catalog 3 (⟨458,(1),[3,7],[10],1181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1181,[3,7,11],1185⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2535 : RecordDataValid section14Catalog 3 (⟨458,(2),[3,7],[10],1182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1182,[3,7,11],1186⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2536 : RecordDataValid section14Catalog 3 (⟨458,(3),[3,7],[10],1183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1183,[3,7,11],1187⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2537 : RecordDataValid section14Catalog 3 (⟨460,(0),[3,7,15],[10],1184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1184,[3,7,11,15],1188⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2538 : RecordDataValid section14Catalog 3 (⟨460,(1),[3,7,15],[10],958⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨958,[3,7,11,15],962⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2539 : RecordDataValid section14Catalog 3 (⟨460,(2),[3,7,15],[10],959⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨959,[3,7,11,15],963⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2540 : RecordDataValid section14Catalog 3 (⟨460,(3),[3,7,15],[10],960⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨960,[3,7,11,15],964⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2541 : RecordDataValid section14Catalog 3 (⟨460,(4),[3,7,15],[10],961⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨961,[3,7,11,15],965⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2542 : RecordDataValid section14Catalog 3 (⟨461,(8),[3,7,15],[10],1185⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1185,[3,7,11,15],1189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2543 : RecordDataValid section14Catalog 3 (⟨461,(9),[3,7,15],[10],1186⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1186,[3,7,11,15],1190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2544 : RecordDataValid section14Catalog 3 (⟨461,(10),[3,7,15],[10],1185⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1185,[3,7,11,15],1189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2545 : RecordDataValid section14Catalog 3 (⟨461,(11),[3,7,15],[10],1187⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1187,[3,7,11,15],1191⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2546 : RecordDataValid section14Catalog 3 (⟨462,(0),[3,7,15],[10],1188⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1188,[3,5,7,8,9,11,12,15],1192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2547 : RecordDataValid section14Catalog 3 (⟨462,(1),[3,7,15],[10],1189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1189,[3,5,7,8,9,11,12,15],1193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2548 : RecordDataValid section14Catalog 3 (⟨462,(2),[3,7,15],[10],1190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1190,[3,5,7,8,9,11,12,15],1194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2549 : RecordDataValid section14Catalog 3 (⟨462,(3),[3,7,15],[10],1191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1191,[3,5,7,8,9,11,12,15],1195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2550 : RecordDataValid section14Catalog 3 (⟨462,(4),[3,7,15],[10],1192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1192,[3,7,8,11,12,15],1196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2551 : RecordDataValid section14Catalog 3 (⟨464,(0),[3,7,15],[10],1193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1193,[3,7,11,15],1197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2552 : RecordDataValid section14Catalog 3 (⟨464,(1),[3,7,15],[10],1194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1194,[3,7,11,15],1198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2553 : RecordDataValid section14Catalog 3 (⟨464,(2),[3,7,15],[10],1195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1195,[3,7,11,15],1199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2554 : RecordDataValid section14Catalog 3 (⟨464,(3),[3,7,15],[10],1196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1196,[3,7,11,15],1200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2555 : RecordDataValid section14Catalog 3 (⟨465,(0),[3,7,15],[10],1197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1197,[3,7,11,15],1201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2556 : RecordDataValid section14Catalog 3 (⟨465,(1),[3,7,15],[10],1198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1198,[3,7,11,15],1202⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2557 : RecordDataValid section14Catalog 3 (⟨465,(2),[3,7,15],[10],1197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1197,[3,7,11,15],1201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2558 : RecordDataValid section14Catalog 3 (⟨465,(3),[3,7,15],[10],1199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1199,[3,7,11,15],1203⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2559 : RecordDataValid section14Catalog 3 (⟨466,(0),[3,7,15],[10],1200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1200,[3,5,7,8,9,11,12,15],1204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2528).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2528).take 32 = [⟨453,(15),[3,7,15],[10],1176⟩,⟨455,(0),[3],[10],1177⟩,⟨455,(1),[3,7],[10],1178⟩,⟨455,(2),[3,7],[10],1177⟩,⟨455,(3),[3,7],[10],1179⟩,⟨458,(0),[3,7],[10],1180⟩,⟨458,(1),[3,7],[10],1181⟩,⟨458,(2),[3,7],[10],1182⟩,⟨458,(3),[3,7],[10],1183⟩,⟨460,(0),[3,7,15],[10],1184⟩,⟨460,(1),[3,7,15],[10],958⟩,⟨460,(2),[3,7,15],[10],959⟩,⟨460,(3),[3,7,15],[10],960⟩,⟨460,(4),[3,7,15],[10],961⟩,⟨461,(8),[3,7,15],[10],1185⟩,⟨461,(9),[3,7,15],[10],1186⟩,⟨461,(10),[3,7,15],[10],1185⟩,⟨461,(11),[3,7,15],[10],1187⟩,⟨462,(0),[3,7,15],[10],1188⟩,⟨462,(1),[3,7,15],[10],1189⟩,⟨462,(2),[3,7,15],[10],1190⟩,⟨462,(3),[3,7,15],[10],1191⟩,⟨462,(4),[3,7,15],[10],1192⟩,⟨464,(0),[3,7,15],[10],1193⟩,⟨464,(1),[3,7,15],[10],1194⟩,⟨464,(2),[3,7,15],[10],1195⟩,⟨464,(3),[3,7,15],[10],1196⟩,⟨465,(0),[3,7,15],[10],1197⟩,⟨465,(1),[3,7,15],[10],1198⟩,⟨465,(2),[3,7,15],[10],1197⟩,⟨465,(3),[3,7,15],[10],1199⟩,⟨466,(0),[3,7,15],[10],1200⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2528
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2529
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2530
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2531
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2532
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2533
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2534
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2535
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2536
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2537
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2538
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2539
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2540
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2541
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2542
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2543
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2544
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2545
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2546
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2547
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2548
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2549
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2550
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2551
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2552
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2553
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2554
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2555
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2556
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2557
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2558
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2559
end Section14Records_3_2528_2560

#print axioms solution
