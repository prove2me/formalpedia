-- Prove2me | solution 1 for Freiman.section14_s0014_records_1120_1152
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:53:52.964989+00:00
-- url     : https://prove2.me/submissions/25db210a-56f7-4099-8184-2f44dd4eada7

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
namespace Section14Records_14_1120_1152
private theorem valid1120 : RecordDataValid section14Catalog 14 (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1121 : RecordDataValid section14Catalog 14 (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1122 : RecordDataValid section14Catalog 14 (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1123 : RecordDataValid section14Catalog 14 (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1124 : RecordDataValid section14Catalog 14 (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1125 : RecordDataValid section14Catalog 14 (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1126 : RecordDataValid section14Catalog 14 (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1127 : RecordDataValid section14Catalog 14 (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1128 : RecordDataValid section14Catalog 14 (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1129 : RecordDataValid section14Catalog 14 (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1130 : RecordDataValid section14Catalog 14 (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1131 : RecordDataValid section14Catalog 14 (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1132 : RecordDataValid section14Catalog 14 (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1133 : RecordDataValid section14Catalog 14 (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1134 : RecordDataValid section14Catalog 14 (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1135 : RecordDataValid section14Catalog 14 (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1136 : RecordDataValid section14Catalog 14 (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1137 : RecordDataValid section14Catalog 14 (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1138 : RecordDataValid section14Catalog 14 (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1139 : RecordDataValid section14Catalog 14 (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨647,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],648⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1140 : RecordDataValid section14Catalog 14 (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1141 : RecordDataValid section14Catalog 14 (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1142 : RecordDataValid section14Catalog 14 (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1143 : RecordDataValid section14Catalog 14 (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1144 : RecordDataValid section14Catalog 14 (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1145 : RecordDataValid section14Catalog 14 (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1146 : RecordDataValid section14Catalog 14 (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1147 : RecordDataValid section14Catalog 14 (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1148 : RecordDataValid section14Catalog 14 (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1149 : RecordDataValid section14Catalog 14 (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1150 : RecordDataValid section14Catalog 14 (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1151 : RecordDataValid section14Catalog 14 (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 14 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1120).take 32 = [⟨163,(6),[1,2,5,6,13,14],[170],409⟩,⟨163,(7),[1,2,5,6,13,14],[170],409⟩,⟨163,(8),[1,2,5,6,13,14],[170],410⟩,⟨163,(9),[1,2,5,6,13,14],[170],410⟩,⟨163,(10),[1,2,5,6,13,14],[170],410⟩,⟨163,(11),[1,2,5,6,13,14],[170],410⟩,⟨163,(12),[1,2,5,6,13,14],[170],411⟩,⟨163,(13),[1,2,5,6,13,14],[170],411⟩,⟨163,(14),[1,2,5,6,13,14],[170],411⟩,⟨163,(15),[1,2,5,6,13,14],[170],411⟩,⟨166,(0),[1,2,5,6,13,14],[170],644⟩,⟨166,(1),[1,2,5,6,13,14],[170],644⟩,⟨166,(2),[1,2,5,6,13,14],[170],644⟩,⟨166,(3),[1,2,5,6,13,14],[170],644⟩,⟨166,(4),[1,2,5,6,13,14],[170],645⟩,⟨166,(5),[1,2,5,6,13,14],[170],645⟩,⟨166,(6),[1,2,5,6,13,14],[170],645⟩,⟨166,(7),[1,2,5,6,13,14],[170],645⟩,⟨166,(8),[1,2,5,6,13,14],[170],646⟩,⟨166,(9),[1,2,5,6,13,14],[170],647⟩,⟨166,(10),[1,2,5,6,13,14],[170],646⟩,⟨166,(11),[1,2,5,6,13,14],[170],648⟩,⟨166,(12),[1,2,5,6,13,14],[170],649⟩,⟨166,(13),[1,2,5,6,13,14],[170],649⟩,⟨166,(14),[1,2,5,6,13,14],[170],649⟩,⟨166,(15),[1,2,5,6,13,14],[170],649⟩,⟨167,(0),[1,2,5,6,13,14],[170],418⟩,⟨167,(1),[1,2,5,6,13,14],[170],419⟩,⟨167,(2),[1,2,5,6,13,14],[170],420⟩,⟨167,(3),[1,2,5,6,13,14],[170],421⟩,⟨167,(4),[1,2,5,6,13,14],[170],422⟩,⟨167,(5),[1,2,5,6,13,14],[170],419⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1120
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1121
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1122
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1123
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1124
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1125
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1126
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1127
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1128
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1129
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1130
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1131
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1132
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1133
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1134
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1135
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1136
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1137
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1138
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1139
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1140
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1141
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1142
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1143
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1144
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1145
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1146
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1147
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1148
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1149
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1150
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1151
end Section14Records_14_1120_1152

#print axioms solution
