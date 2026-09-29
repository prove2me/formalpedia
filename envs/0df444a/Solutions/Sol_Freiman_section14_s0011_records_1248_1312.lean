-- Prove2me | solution 1 for Freiman.section14_s0011_records_1248_1312
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:53:11.043179+00:00
-- url     : https://prove2.me/submissions/74a1bffe-cf73-4e92-b701-880d52998f02

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
namespace Section14Records_11_1248_1312
private theorem valid1248 : RecordDataValid section14Catalog 11 (⟨468,(12),[11],[2],1210⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1210,[3,7,11,15],1214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1249 : RecordDataValid section14Catalog 11 (⟨468,(13),[11],[2],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1250 : RecordDataValid section14Catalog 11 (⟨468,(14),[11],[2],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1251 : RecordDataValid section14Catalog 11 (⟨468,(15),[11],[2],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1252 : RecordDataValid section14Catalog 11 (⟨470,(0),[11],[2],1211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1211,[3,5,7,8,9,11,12,15],1215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1253 : RecordDataValid section14Catalog 11 (⟨470,(1),[11],[2],1212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1212,[3,5,7,8,9,11,12,15],1216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1254 : RecordDataValid section14Catalog 11 (⟨470,(2),[11],[2],1213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1213,[3,5,7,8,9,11,12,15],1217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1255 : RecordDataValid section14Catalog 11 (⟨470,(3),[11],[2],1214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1214,[3,5,7,8,9,11,12,15],1218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1256 : RecordDataValid section14Catalog 11 (⟨470,(4),[11],[2],1215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1215,[3,5,7,8,9,11,12,15],1219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1257 : RecordDataValid section14Catalog 11 (⟨470,(5),[11],[2],1216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1216,[3,5,7,8,9,11,12,15],1220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1258 : RecordDataValid section14Catalog 11 (⟨470,(6),[11],[2],1217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1217,[3,5,7,8,9,11,12,15],1221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1259 : RecordDataValid section14Catalog 11 (⟨470,(7),[11],[2],1218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1218,[3,5,7,8,9,11,12,15],1222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1260 : RecordDataValid section14Catalog 11 (⟨470,(8),[11],[2],1219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1219,[3,7,11,15],1223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1261 : RecordDataValid section14Catalog 11 (⟨470,(9),[11],[2],1220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1220,[3,7,11,15],1224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1262 : RecordDataValid section14Catalog 11 (⟨470,(10),[11],[2],1221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1221,[3,7,11,15],1225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1263 : RecordDataValid section14Catalog 11 (⟨470,(11),[11],[2],1222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1222,[3,7,11,15],1226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1264 : RecordDataValid section14Catalog 11 (⟨470,(12),[11],[2],1223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1223,[3,7,11,15],1227⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1265 : RecordDataValid section14Catalog 11 (⟨470,(13),[11],[2],1220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1220,[3,7,11,15],1224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1266 : RecordDataValid section14Catalog 11 (⟨470,(14),[11],[2],1221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1221,[3,7,11,15],1225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1267 : RecordDataValid section14Catalog 11 (⟨470,(15),[11],[2],1222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1222,[3,7,11,15],1226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1268 : RecordDataValid section14Catalog 11 (⟨471,(0),[11],[2],1224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1224,[3,7,11,15],1228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1269 : RecordDataValid section14Catalog 11 (⟨471,(1),[11],[2],1224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1224,[3,7,11,15],1228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1270 : RecordDataValid section14Catalog 11 (⟨471,(2),[11],[2],1225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1225,[3,7,11,15],1229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1271 : RecordDataValid section14Catalog 11 (⟨471,(3),[11],[2],1225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1225,[3,7,11,15],1229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1272 : RecordDataValid section14Catalog 11 (⟨471,(4),[11],[2],1226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1226,[3,7,11,15],1230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1273 : RecordDataValid section14Catalog 11 (⟨471,(5),[11],[2],1226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1226,[3,7,11,15],1230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1274 : RecordDataValid section14Catalog 11 (⟨471,(6),[11],[2],1227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1227,[3,7,11,15],1231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1275 : RecordDataValid section14Catalog 11 (⟨471,(7),[11],[2],1227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1227,[3,7,11,15],1231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1276 : RecordDataValid section14Catalog 11 (⟨472,(0),[11],[2],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1277 : RecordDataValid section14Catalog 11 (⟨472,(1),[11],[2],1229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1229,[3,5,7,8,9,11,12,15],1233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1278 : RecordDataValid section14Catalog 11 (⟨472,(2),[11],[2],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1279 : RecordDataValid section14Catalog 11 (⟨472,(3),[11],[2],1230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1230,[3,5,7,8,9,11,12,15],1234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1280 : RecordDataValid section14Catalog 11 (⟨472,(4),[11],[2],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1281 : RecordDataValid section14Catalog 11 (⟨472,(5),[11],[2],1232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1232,[3,5,7,8,9,11,12,15],1236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1282 : RecordDataValid section14Catalog 11 (⟨472,(6),[11],[2],1233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1233,[3,7,11,15],1237⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1283 : RecordDataValid section14Catalog 11 (⟨472,(7),[11],[2],1234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1234,[3,7,11,15],1238⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1284 : RecordDataValid section14Catalog 11 (⟨472,(8),[11],[2],1235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1235,[3,5,7,8,9,11,12,15],1239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1285 : RecordDataValid section14Catalog 11 (⟨472,(9),[11],[2],1236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1236,[3,5,7,8,9,11,12,15],1240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1286 : RecordDataValid section14Catalog 11 (⟨472,(10),[11],[2],1237⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1237,[3,7,11,15],1241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1287 : RecordDataValid section14Catalog 11 (⟨472,(11),[11],[2],1238⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1238,[3,7,11,15],1242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1288 : RecordDataValid section14Catalog 11 (⟨472,(12),[11],[2],1239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1239,[3,5,7,8,9,11,12,15],1243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1289 : RecordDataValid section14Catalog 11 (⟨472,(13),[11],[2],1240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1240,[3,5,7,8,9,11,12,15],1244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1290 : RecordDataValid section14Catalog 11 (⟨472,(14),[11],[2],1241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1241,[3,7,11,15],1245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1291 : RecordDataValid section14Catalog 11 (⟨472,(15),[11],[2],1241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1241,[3,7,11,15],1245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1292 : RecordDataValid section14Catalog 11 (⟨472,(16),[11],[2],1242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1242,[3,5,7,8,9,11,12,15],1246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1293 : RecordDataValid section14Catalog 11 (⟨472,(17),[11],[2],1243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1243,[3,5,7,8,9,11,12,15],1247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1294 : RecordDataValid section14Catalog 11 (⟨472,(18),[11],[2],1244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1244,[3,7,11,15],1248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1295 : RecordDataValid section14Catalog 11 (⟨472,(19),[11],[2],1244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1244,[3,7,11,15],1248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1296 : RecordDataValid section14Catalog 11 (⟨474,(0),[11],[2],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1297 : RecordDataValid section14Catalog 11 (⟨474,(1),[11],[2],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1298 : RecordDataValid section14Catalog 11 (⟨474,(2),[11],[2],1246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1246,[3,7,11],1250⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1299 : RecordDataValid section14Catalog 11 (⟨474,(3),[11],[2],1246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1246,[3,7,11],1250⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1300 : RecordDataValid section14Catalog 11 (⟨474,(4),[11],[2],1247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1247,[3,7,11],1251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1301 : RecordDataValid section14Catalog 11 (⟨474,(5),[11],[2],1247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1247,[3,7,11],1251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1302 : RecordDataValid section14Catalog 11 (⟨474,(6),[11],[2],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1303 : RecordDataValid section14Catalog 11 (⟨474,(7),[11],[2],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1304 : RecordDataValid section14Catalog 11 (⟨474,(8),[11],[2],1248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1248,[3,7,11],1252⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1305 : RecordDataValid section14Catalog 11 (⟨474,(9),[11],[2],1248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1248,[3,7,11],1252⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1306 : RecordDataValid section14Catalog 11 (⟨537,(0),[11],[2],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1307 : RecordDataValid section14Catalog 11 (⟨537,(1),[11],[2],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1308 : RecordDataValid section14Catalog 11 (⟨537,(2),[11],[2],1686⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1686,[11],1691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1309 : RecordDataValid section14Catalog 11 (⟨537,(3),[11],[2],1687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1687,[11],1692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1310 : RecordDataValid section14Catalog 11 (⟨537,(4),[11],[2],14⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨14,[1,2,3,4,6,7,11,13,14,15,16],14⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1311 : RecordDataValid section14Catalog 11 (⟨537,(5),[11],[2],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1248).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1248).take 64 = [⟨468,(12),[11],[2],1210⟩,⟨468,(13),[11],[2],1205⟩,⟨468,(14),[11],[2],1206⟩,⟨468,(15),[11],[2],1207⟩,⟨470,(0),[11],[2],1211⟩,⟨470,(1),[11],[2],1212⟩,⟨470,(2),[11],[2],1213⟩,⟨470,(3),[11],[2],1214⟩,⟨470,(4),[11],[2],1215⟩,⟨470,(5),[11],[2],1216⟩,⟨470,(6),[11],[2],1217⟩,⟨470,(7),[11],[2],1218⟩,⟨470,(8),[11],[2],1219⟩,⟨470,(9),[11],[2],1220⟩,⟨470,(10),[11],[2],1221⟩,⟨470,(11),[11],[2],1222⟩,⟨470,(12),[11],[2],1223⟩,⟨470,(13),[11],[2],1220⟩,⟨470,(14),[11],[2],1221⟩,⟨470,(15),[11],[2],1222⟩,⟨471,(0),[11],[2],1224⟩,⟨471,(1),[11],[2],1224⟩,⟨471,(2),[11],[2],1225⟩,⟨471,(3),[11],[2],1225⟩,⟨471,(4),[11],[2],1226⟩,⟨471,(5),[11],[2],1226⟩,⟨471,(6),[11],[2],1227⟩,⟨471,(7),[11],[2],1227⟩,⟨472,(0),[11],[2],1228⟩,⟨472,(1),[11],[2],1229⟩,⟨472,(2),[11],[2],1228⟩,⟨472,(3),[11],[2],1230⟩,⟨472,(4),[11],[2],1231⟩,⟨472,(5),[11],[2],1232⟩,⟨472,(6),[11],[2],1233⟩,⟨472,(7),[11],[2],1234⟩,⟨472,(8),[11],[2],1235⟩,⟨472,(9),[11],[2],1236⟩,⟨472,(10),[11],[2],1237⟩,⟨472,(11),[11],[2],1238⟩,⟨472,(12),[11],[2],1239⟩,⟨472,(13),[11],[2],1240⟩,⟨472,(14),[11],[2],1241⟩,⟨472,(15),[11],[2],1241⟩,⟨472,(16),[11],[2],1242⟩,⟨472,(17),[11],[2],1243⟩,⟨472,(18),[11],[2],1244⟩,⟨472,(19),[11],[2],1244⟩,⟨474,(0),[11],[2],1245⟩,⟨474,(1),[11],[2],1245⟩,⟨474,(2),[11],[2],1246⟩,⟨474,(3),[11],[2],1246⟩,⟨474,(4),[11],[2],1247⟩,⟨474,(5),[11],[2],1247⟩,⟨474,(6),[11],[2],939⟩,⟨474,(7),[11],[2],939⟩,⟨474,(8),[11],[2],1248⟩,⟨474,(9),[11],[2],1248⟩,⟨537,(0),[11],[2],1649⟩,⟨537,(1),[11],[2],1650⟩,⟨537,(2),[11],[2],1686⟩,⟨537,(3),[11],[2],1687⟩,⟨537,(4),[11],[2],14⟩,⟨537,(5),[11],[2],1649⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1248
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1249
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1250
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1251
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1252
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1253
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1254
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1255
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1256
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1257
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1258
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1259
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1260
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1261
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1262
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1263
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1264
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1265
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1266
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1267
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1268
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1269
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1270
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1271
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1272
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1273
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1274
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1275
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1276
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1277
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1278
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1279
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1280
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1281
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1282
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1283
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1284
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1285
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1286
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1287
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1288
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1289
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1290
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1291
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1292
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1293
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1294
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1295
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1296
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1297
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1298
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1299
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1300
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1301
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1302
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1303
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1304
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1305
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1306
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1307
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1308
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1309
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1310
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1311
end Section14Records_11_1248_1312

#print axioms solution
