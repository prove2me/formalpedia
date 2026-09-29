-- Prove2me | solution 1 for Freiman.section14_s0011_records_1184_1248
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:51:38.679906+00:00
-- url     : https://prove2.me/submissions/4f0977dc-b758-41a6-9f82-d94e4d32de10

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
namespace Section14Records_11_1184_1248
private theorem valid1184 : RecordDataValid section14Catalog 11 (⟨450,(2),[11],[2],1168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1168,[3,7,11,15],1172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1185 : RecordDataValid section14Catalog 11 (⟨450,(3),[11],[2],1169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1169,[3,7,11,15],1173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1186 : RecordDataValid section14Catalog 11 (⟨453,(0),[11],[2],1170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1170,[3,7,11,15],1174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1187 : RecordDataValid section14Catalog 11 (⟨453,(1),[11],[2],1171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1171,[3,7,11,15],1175⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1188 : RecordDataValid section14Catalog 11 (⟨453,(2),[11],[2],1170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1170,[3,7,11,15],1174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1189 : RecordDataValid section14Catalog 11 (⟨453,(3),[11],[2],1172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1172,[3,7,11,15],1176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1190 : RecordDataValid section14Catalog 11 (⟨453,(4),[11],[2],1173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1173,[3,7,11,15],1177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1191 : RecordDataValid section14Catalog 11 (⟨453,(5),[11],[2],1173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1173,[3,7,11,15],1177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1192 : RecordDataValid section14Catalog 11 (⟨453,(6),[11],[2],1173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1173,[3,7,11,15],1177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1193 : RecordDataValid section14Catalog 11 (⟨453,(7),[11],[2],1173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1173,[3,7,11,15],1177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1194 : RecordDataValid section14Catalog 11 (⟨453,(8),[11],[2],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1195 : RecordDataValid section14Catalog 11 (⟨453,(9),[11],[2],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1196 : RecordDataValid section14Catalog 11 (⟨453,(10),[11],[2],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1197 : RecordDataValid section14Catalog 11 (⟨453,(11),[11],[2],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1198 : RecordDataValid section14Catalog 11 (⟨453,(12),[11],[2],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1199 : RecordDataValid section14Catalog 11 (⟨453,(13),[11],[2],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1200 : RecordDataValid section14Catalog 11 (⟨453,(14),[11],[2],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1201 : RecordDataValid section14Catalog 11 (⟨453,(15),[11],[2],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1202 : RecordDataValid section14Catalog 11 (⟨455,(0),[11],[2],1629⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1629,[7,11],1634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1203 : RecordDataValid section14Catalog 11 (⟨455,(1),[11],[2],1178⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1178,[3,7,11],1182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1204 : RecordDataValid section14Catalog 11 (⟨455,(2),[11],[2],1177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1177,[3,7,11],1181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1205 : RecordDataValid section14Catalog 11 (⟨455,(3),[11],[2],1179⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1179,[3,7,11],1183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1206 : RecordDataValid section14Catalog 11 (⟨458,(0),[11],[2],1180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1180,[3,7,11],1184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1207 : RecordDataValid section14Catalog 11 (⟨458,(1),[11],[2],1181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1181,[3,7,11],1185⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1208 : RecordDataValid section14Catalog 11 (⟨458,(2),[11],[2],1182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1182,[3,7,11],1186⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1209 : RecordDataValid section14Catalog 11 (⟨458,(3),[11],[2],1183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1183,[3,7,11],1187⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1210 : RecordDataValid section14Catalog 11 (⟨460,(0),[11],[2],1184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1184,[3,7,11,15],1188⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1211 : RecordDataValid section14Catalog 11 (⟨460,(1),[11],[2],958⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨958,[3,7,11,15],962⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1212 : RecordDataValid section14Catalog 11 (⟨460,(2),[11],[2],959⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨959,[3,7,11,15],963⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1213 : RecordDataValid section14Catalog 11 (⟨460,(3),[11],[2],960⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨960,[3,7,11,15],964⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1214 : RecordDataValid section14Catalog 11 (⟨460,(4),[11],[2],961⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨961,[3,7,11,15],965⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1215 : RecordDataValid section14Catalog 11 (⟨461,(8),[11],[2],1185⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1185,[3,7,11,15],1189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1216 : RecordDataValid section14Catalog 11 (⟨461,(9),[11],[2],1186⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1186,[3,7,11,15],1190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1217 : RecordDataValid section14Catalog 11 (⟨461,(10),[11],[2],1185⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1185,[3,7,11,15],1189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1218 : RecordDataValid section14Catalog 11 (⟨461,(11),[11],[2],1187⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1187,[3,7,11,15],1191⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1219 : RecordDataValid section14Catalog 11 (⟨462,(0),[11],[2],1188⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1188,[3,5,7,8,9,11,12,15],1192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1220 : RecordDataValid section14Catalog 11 (⟨462,(1),[11],[2],1189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1189,[3,5,7,8,9,11,12,15],1193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1221 : RecordDataValid section14Catalog 11 (⟨462,(2),[11],[2],1190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1190,[3,5,7,8,9,11,12,15],1194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1222 : RecordDataValid section14Catalog 11 (⟨462,(3),[11],[2],1191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1191,[3,5,7,8,9,11,12,15],1195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1223 : RecordDataValid section14Catalog 11 (⟨462,(4),[11],[2],1192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1192,[3,7,8,11,12,15],1196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1224 : RecordDataValid section14Catalog 11 (⟨464,(0),[11],[2],1193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1193,[3,7,11,15],1197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1225 : RecordDataValid section14Catalog 11 (⟨464,(1),[11],[2],1194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1194,[3,7,11,15],1198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1226 : RecordDataValid section14Catalog 11 (⟨464,(2),[11],[2],1195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1195,[3,7,11,15],1199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1227 : RecordDataValid section14Catalog 11 (⟨464,(3),[11],[2],1196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1196,[3,7,11,15],1200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1228 : RecordDataValid section14Catalog 11 (⟨465,(0),[11],[2],1197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1197,[3,7,11,15],1201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1229 : RecordDataValid section14Catalog 11 (⟨465,(1),[11],[2],1198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1198,[3,7,11,15],1202⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1230 : RecordDataValid section14Catalog 11 (⟨465,(2),[11],[2],1197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1197,[3,7,11,15],1201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1231 : RecordDataValid section14Catalog 11 (⟨465,(3),[11],[2],1199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1199,[3,7,11,15],1203⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1232 : RecordDataValid section14Catalog 11 (⟨466,(0),[11],[2],1200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1200,[3,5,7,8,9,11,12,15],1204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1233 : RecordDataValid section14Catalog 11 (⟨466,(1),[11],[2],1201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1201,[3,5,7,8,9,11,12,15],1205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1234 : RecordDataValid section14Catalog 11 (⟨466,(2),[11],[2],1202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1202,[3,5,7,8,9,11,12,15],1206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1235 : RecordDataValid section14Catalog 11 (⟨466,(3),[11],[2],1203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1203,[3,5,7,8,9,11,15],1207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1236 : RecordDataValid section14Catalog 11 (⟨468,(0),[11],[2],1204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1204,[3,7,11,15],1208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1237 : RecordDataValid section14Catalog 11 (⟨468,(1),[11],[2],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1238 : RecordDataValid section14Catalog 11 (⟨468,(2),[11],[2],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1239 : RecordDataValid section14Catalog 11 (⟨468,(3),[11],[2],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1240 : RecordDataValid section14Catalog 11 (⟨468,(4),[11],[2],1208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1208,[3,7,11,15],1212⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1241 : RecordDataValid section14Catalog 11 (⟨468,(5),[11],[2],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1242 : RecordDataValid section14Catalog 11 (⟨468,(6),[11],[2],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1243 : RecordDataValid section14Catalog 11 (⟨468,(7),[11],[2],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1244 : RecordDataValid section14Catalog 11 (⟨468,(8),[11],[2],1204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1204,[3,7,11,15],1208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1245 : RecordDataValid section14Catalog 11 (⟨468,(9),[11],[2],1209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1209,[3,7,11,15],1213⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1246 : RecordDataValid section14Catalog 11 (⟨468,(10),[11],[2],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1247 : RecordDataValid section14Catalog 11 (⟨468,(11),[11],[2],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1184).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1184).take 64 = [⟨450,(2),[11],[2],1168⟩,⟨450,(3),[11],[2],1169⟩,⟨453,(0),[11],[2],1170⟩,⟨453,(1),[11],[2],1171⟩,⟨453,(2),[11],[2],1170⟩,⟨453,(3),[11],[2],1172⟩,⟨453,(4),[11],[2],1173⟩,⟨453,(5),[11],[2],1173⟩,⟨453,(6),[11],[2],1173⟩,⟨453,(7),[11],[2],1173⟩,⟨453,(8),[11],[2],1175⟩,⟨453,(9),[11],[2],1175⟩,⟨453,(10),[11],[2],1175⟩,⟨453,(11),[11],[2],1175⟩,⟨453,(12),[11],[2],1176⟩,⟨453,(13),[11],[2],1176⟩,⟨453,(14),[11],[2],1176⟩,⟨453,(15),[11],[2],1176⟩,⟨455,(0),[11],[2],1629⟩,⟨455,(1),[11],[2],1178⟩,⟨455,(2),[11],[2],1177⟩,⟨455,(3),[11],[2],1179⟩,⟨458,(0),[11],[2],1180⟩,⟨458,(1),[11],[2],1181⟩,⟨458,(2),[11],[2],1182⟩,⟨458,(3),[11],[2],1183⟩,⟨460,(0),[11],[2],1184⟩,⟨460,(1),[11],[2],958⟩,⟨460,(2),[11],[2],959⟩,⟨460,(3),[11],[2],960⟩,⟨460,(4),[11],[2],961⟩,⟨461,(8),[11],[2],1185⟩,⟨461,(9),[11],[2],1186⟩,⟨461,(10),[11],[2],1185⟩,⟨461,(11),[11],[2],1187⟩,⟨462,(0),[11],[2],1188⟩,⟨462,(1),[11],[2],1189⟩,⟨462,(2),[11],[2],1190⟩,⟨462,(3),[11],[2],1191⟩,⟨462,(4),[11],[2],1192⟩,⟨464,(0),[11],[2],1193⟩,⟨464,(1),[11],[2],1194⟩,⟨464,(2),[11],[2],1195⟩,⟨464,(3),[11],[2],1196⟩,⟨465,(0),[11],[2],1197⟩,⟨465,(1),[11],[2],1198⟩,⟨465,(2),[11],[2],1197⟩,⟨465,(3),[11],[2],1199⟩,⟨466,(0),[11],[2],1200⟩,⟨466,(1),[11],[2],1201⟩,⟨466,(2),[11],[2],1202⟩,⟨466,(3),[11],[2],1203⟩,⟨468,(0),[11],[2],1204⟩,⟨468,(1),[11],[2],1205⟩,⟨468,(2),[11],[2],1206⟩,⟨468,(3),[11],[2],1207⟩,⟨468,(4),[11],[2],1208⟩,⟨468,(5),[11],[2],1205⟩,⟨468,(6),[11],[2],1206⟩,⟨468,(7),[11],[2],1207⟩,⟨468,(8),[11],[2],1204⟩,⟨468,(9),[11],[2],1209⟩,⟨468,(10),[11],[2],1206⟩,⟨468,(11),[11],[2],1207⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1184
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1185
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1186
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1187
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1188
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1189
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1190
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1191
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1192
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1193
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1194
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1195
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1196
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1197
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1198
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1199
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1200
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1201
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1202
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1203
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1204
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1205
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1206
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1207
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1208
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1209
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1210
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1211
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1212
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1213
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1214
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1215
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1216
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1217
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1218
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1219
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1220
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1221
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1222
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1223
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1224
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1225
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1226
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1227
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1228
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1229
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1230
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1231
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1232
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1233
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1234
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1235
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1236
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1237
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1238
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1239
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1240
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1241
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1242
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1243
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1244
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1245
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1246
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1247
end Section14Records_11_1184_1248

#print axioms solution
