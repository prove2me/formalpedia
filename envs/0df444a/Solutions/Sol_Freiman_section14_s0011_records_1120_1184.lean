-- Prove2me | solution 1 for Freiman.section14_s0011_records_1120_1184
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:49:49.308184+00:00
-- url     : https://prove2.me/submissions/9ae85b31-8c45-4388-87ca-c11dae2a8e35

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
namespace Section14Records_11_1120_1184
private theorem valid1120 : RecordDataValid section14Catalog 11 (⟨443,(13),[11],[2],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1121 : RecordDataValid section14Catalog 11 (⟨443,(14),[11],[2],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1122 : RecordDataValid section14Catalog 11 (⟨443,(15),[11],[2],1150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1150,[3,7,11,15],1154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1123 : RecordDataValid section14Catalog 11 (⟨443,(16),[11],[2],1150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1150,[3,7,11,15],1154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1124 : RecordDataValid section14Catalog 11 (⟨443,(17),[11],[2],1146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1146,[3,7,11,15],1150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1125 : RecordDataValid section14Catalog 11 (⟨443,(18),[11],[2],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1126 : RecordDataValid section14Catalog 11 (⟨443,(19),[11],[2],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1127 : RecordDataValid section14Catalog 11 (⟨443,(20),[11],[2],1151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1151,[3,7,11,15],1155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1128 : RecordDataValid section14Catalog 11 (⟨443,(21),[11],[2],1151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1151,[3,7,11,15],1155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1129 : RecordDataValid section14Catalog 11 (⟨443,(22),[11],[2],1151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1151,[3,7,11,15],1155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1130 : RecordDataValid section14Catalog 11 (⟨443,(23),[11],[2],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1131 : RecordDataValid section14Catalog 11 (⟨443,(24),[11],[2],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1132 : RecordDataValid section14Catalog 11 (⟨446,(0),[11],[2],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1133 : RecordDataValid section14Catalog 11 (⟨446,(1),[11],[2],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1134 : RecordDataValid section14Catalog 11 (⟨446,(2),[11],[2],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1135 : RecordDataValid section14Catalog 11 (⟨446,(3),[11],[2],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1136 : RecordDataValid section14Catalog 11 (⟨446,(4),[11],[2],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1137 : RecordDataValid section14Catalog 11 (⟨446,(5),[11],[2],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1138 : RecordDataValid section14Catalog 11 (⟨446,(6),[11],[2],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1139 : RecordDataValid section14Catalog 11 (⟨446,(7),[11],[2],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1140 : RecordDataValid section14Catalog 11 (⟨446,(8),[11],[2],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1141 : RecordDataValid section14Catalog 11 (⟨446,(9),[11],[2],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1142 : RecordDataValid section14Catalog 11 (⟨446,(10),[11],[2],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1143 : RecordDataValid section14Catalog 11 (⟨446,(11),[11],[2],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1144 : RecordDataValid section14Catalog 11 (⟨446,(12),[11],[2],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1145 : RecordDataValid section14Catalog 11 (⟨446,(13),[11],[2],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1146 : RecordDataValid section14Catalog 11 (⟨446,(14),[11],[2],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1147 : RecordDataValid section14Catalog 11 (⟨446,(15),[11],[2],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1148 : RecordDataValid section14Catalog 11 (⟨446,(16),[11],[2],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1149 : RecordDataValid section14Catalog 11 (⟨446,(17),[11],[2],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1150 : RecordDataValid section14Catalog 11 (⟨446,(18),[11],[2],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1151 : RecordDataValid section14Catalog 11 (⟨446,(19),[11],[2],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1152 : RecordDataValid section14Catalog 11 (⟨446,(20),[11],[2],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1153 : RecordDataValid section14Catalog 11 (⟨446,(21),[11],[2],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1154 : RecordDataValid section14Catalog 11 (⟨446,(22),[11],[2],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1155 : RecordDataValid section14Catalog 11 (⟨446,(23),[11],[2],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1156 : RecordDataValid section14Catalog 11 (⟨446,(24),[11],[2],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1157 : RecordDataValid section14Catalog 11 (⟨448,(0),[11],[2],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1158 : RecordDataValid section14Catalog 11 (⟨448,(1),[11],[2],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1159 : RecordDataValid section14Catalog 11 (⟨448,(2),[11],[2],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1160 : RecordDataValid section14Catalog 11 (⟨448,(3),[11],[2],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1161 : RecordDataValid section14Catalog 11 (⟨448,(4),[11],[2],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1162 : RecordDataValid section14Catalog 11 (⟨448,(5),[11],[2],1163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1163,[3,7,11,15],1167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1163 : RecordDataValid section14Catalog 11 (⟨448,(6),[11],[2],1163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1163,[3,7,11,15],1167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1164 : RecordDataValid section14Catalog 11 (⟨448,(7),[11],[2],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1165 : RecordDataValid section14Catalog 11 (⟨448,(8),[11],[2],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1166 : RecordDataValid section14Catalog 11 (⟨448,(9),[11],[2],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1167 : RecordDataValid section14Catalog 11 (⟨448,(10),[11],[2],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1168 : RecordDataValid section14Catalog 11 (⟨448,(11),[11],[2],1159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1159,[3,7,11,15],1163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1169 : RecordDataValid section14Catalog 11 (⟨448,(12),[11],[2],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1170 : RecordDataValid section14Catalog 11 (⟨448,(13),[11],[2],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1171 : RecordDataValid section14Catalog 11 (⟨448,(14),[11],[2],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1172 : RecordDataValid section14Catalog 11 (⟨448,(15),[11],[2],1164⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1164,[3,7,11,15],1168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1173 : RecordDataValid section14Catalog 11 (⟨448,(16),[11],[2],1164⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1164,[3,7,11,15],1168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1174 : RecordDataValid section14Catalog 11 (⟨448,(17),[11],[2],1160⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1160,[3,7,11,15],1164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1175 : RecordDataValid section14Catalog 11 (⟨448,(18),[11],[2],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1176 : RecordDataValid section14Catalog 11 (⟨448,(19),[11],[2],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1177 : RecordDataValid section14Catalog 11 (⟨448,(20),[11],[2],1165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1165,[3,7,11,15],1169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1178 : RecordDataValid section14Catalog 11 (⟨448,(21),[11],[2],1165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1165,[3,7,11,15],1169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1179 : RecordDataValid section14Catalog 11 (⟨448,(22),[11],[2],1165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1165,[3,7,11,15],1169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1180 : RecordDataValid section14Catalog 11 (⟨448,(23),[11],[2],1161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1161,[3,7,11,15],1165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1181 : RecordDataValid section14Catalog 11 (⟨448,(24),[11],[2],1162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1162,[3,7,11,15],1166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1182 : RecordDataValid section14Catalog 11 (⟨450,(0),[11],[2],1166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1166,[3,7,11,15],1170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1183 : RecordDataValid section14Catalog 11 (⟨450,(1),[11],[2],1167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1167,[3,7,11,15],1171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1120).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1120).take 64 = [⟨443,(13),[11],[2],1147⟩,⟨443,(14),[11],[2],1148⟩,⟨443,(15),[11],[2],1150⟩,⟨443,(16),[11],[2],1150⟩,⟨443,(17),[11],[2],1146⟩,⟨443,(18),[11],[2],1147⟩,⟨443,(19),[11],[2],1148⟩,⟨443,(20),[11],[2],1151⟩,⟨443,(21),[11],[2],1151⟩,⟨443,(22),[11],[2],1151⟩,⟨443,(23),[11],[2],1147⟩,⟨443,(24),[11],[2],1148⟩,⟨446,(0),[11],[2],1152⟩,⟨446,(1),[11],[2],1153⟩,⟨446,(2),[11],[2],1154⟩,⟨446,(3),[11],[2],1154⟩,⟨446,(4),[11],[2],1154⟩,⟨446,(5),[11],[2],1152⟩,⟨446,(6),[11],[2],1153⟩,⟨446,(7),[11],[2],1155⟩,⟨446,(8),[11],[2],1156⟩,⟨446,(9),[11],[2],1155⟩,⟨446,(10),[11],[2],1152⟩,⟨446,(11),[11],[2],1153⟩,⟨446,(12),[11],[2],1157⟩,⟨446,(13),[11],[2],1156⟩,⟨446,(14),[11],[2],1157⟩,⟨446,(15),[11],[2],1152⟩,⟨446,(16),[11],[2],1153⟩,⟨446,(17),[11],[2],1155⟩,⟨446,(18),[11],[2],1156⟩,⟨446,(19),[11],[2],1155⟩,⟨446,(20),[11],[2],1152⟩,⟨446,(21),[11],[2],1153⟩,⟨446,(22),[11],[2],1158⟩,⟨446,(23),[11],[2],1156⟩,⟨446,(24),[11],[2],1158⟩,⟨448,(0),[11],[2],1159⟩,⟨448,(1),[11],[2],1159⟩,⟨448,(2),[11],[2],1160⟩,⟨448,(3),[11],[2],1161⟩,⟨448,(4),[11],[2],1162⟩,⟨448,(5),[11],[2],1163⟩,⟨448,(6),[11],[2],1163⟩,⟨448,(7),[11],[2],1160⟩,⟨448,(8),[11],[2],1161⟩,⟨448,(9),[11],[2],1162⟩,⟨448,(10),[11],[2],1159⟩,⟨448,(11),[11],[2],1159⟩,⟨448,(12),[11],[2],1160⟩,⟨448,(13),[11],[2],1161⟩,⟨448,(14),[11],[2],1162⟩,⟨448,(15),[11],[2],1164⟩,⟨448,(16),[11],[2],1164⟩,⟨448,(17),[11],[2],1160⟩,⟨448,(18),[11],[2],1161⟩,⟨448,(19),[11],[2],1162⟩,⟨448,(20),[11],[2],1165⟩,⟨448,(21),[11],[2],1165⟩,⟨448,(22),[11],[2],1165⟩,⟨448,(23),[11],[2],1161⟩,⟨448,(24),[11],[2],1162⟩,⟨450,(0),[11],[2],1166⟩,⟨450,(1),[11],[2],1167⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1120
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1121
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1122
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1123
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1124
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1125
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1126
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1127
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1128
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1129
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1130
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1131
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1132
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1133
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1134
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1135
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1136
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1137
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1138
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1139
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1140
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1141
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1142
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1143
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1144
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1145
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1146
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1147
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1148
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1149
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1150
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1151
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1152
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1153
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1154
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1155
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1156
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1157
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1158
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1159
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1160
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1161
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1162
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1163
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1164
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1165
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1166
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1167
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1168
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1169
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1170
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1171
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1172
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1173
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1174
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1175
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1176
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1177
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1178
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1179
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1180
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1181
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1182
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1183
end Section14Records_11_1120_1184

#print axioms solution
