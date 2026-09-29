-- Prove2me | solution 1 for Freiman.section14_s0011_records_1312_1376
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:55:11.975723+00:00
-- url     : https://prove2.me/submissions/407e11a4-fe53-4f01-a566-14306f3b1336

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
namespace Section14Records_11_1312_1376
private theorem valid1312 : RecordDataValid section14Catalog 11 (⟨537,(6),[11],[2],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1313 : RecordDataValid section14Catalog 11 (⟨537,(7),[11],[2],1651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1651,[9,10,11,12],1656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1314 : RecordDataValid section14Catalog 11 (⟨537,(8),[11],[2],1652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1652,[9,10,11,12],1657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1315 : RecordDataValid section14Catalog 11 (⟨537,(9),[11],[2],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1316 : RecordDataValid section14Catalog 11 (⟨542,(0),[11],[2],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1317 : RecordDataValid section14Catalog 11 (⟨542,(1),[11],[2],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1318 : RecordDataValid section14Catalog 11 (⟨542,(2),[11],[2],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1319 : RecordDataValid section14Catalog 11 (⟨542,(3),[11],[2],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1320 : RecordDataValid section14Catalog 11 (⟨542,(4),[11],[2],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1321 : RecordDataValid section14Catalog 11 (⟨542,(5),[11],[2],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1322 : RecordDataValid section14Catalog 11 (⟨542,(6),[11],[2],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1323 : RecordDataValid section14Catalog 11 (⟨542,(7),[11],[2],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1324 : RecordDataValid section14Catalog 11 (⟨542,(8),[11],[2],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1325 : RecordDataValid section14Catalog 11 (⟨542,(9),[11],[2],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1326 : RecordDataValid section14Catalog 11 (⟨547,(0),[11],[2],1688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1688,[11],1693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1327 : RecordDataValid section14Catalog 11 (⟨547,(1),[11],[2],1689⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1689,[11],1694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1328 : RecordDataValid section14Catalog 11 (⟨547,(2),[11],[2],1688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1688,[11],1693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1329 : RecordDataValid section14Catalog 11 (⟨547,(3),[11],[2],1690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1690,[11],1695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1330 : RecordDataValid section14Catalog 11 (⟨547,(4),[11],[2],212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨212,[1,2,3,4,11,13,14,15,16],212⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1331 : RecordDataValid section14Catalog 11 (⟨547,(5),[11],[2],1688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1688,[11],1693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1332 : RecordDataValid section14Catalog 11 (⟨547,(6),[11],[2],1689⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1689,[11],1694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1333 : RecordDataValid section14Catalog 11 (⟨547,(7),[11],[2],1688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1688,[11],1693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1334 : RecordDataValid section14Catalog 11 (⟨547,(8),[11],[2],1690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1690,[11],1695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1335 : RecordDataValid section14Catalog 11 (⟨547,(9),[11],[2],212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨212,[1,2,3,4,11,13,14,15,16],212⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1336 : RecordDataValid section14Catalog 11 (⟨552,(0),[11],[2],1657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1657,[9,10,11,12],1662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1337 : RecordDataValid section14Catalog 11 (⟨552,(1),[11],[2],1658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1658,[9,10,11,12],1663⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1338 : RecordDataValid section14Catalog 11 (⟨552,(2),[11],[2],1657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1657,[9,10,11,12],1662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1339 : RecordDataValid section14Catalog 11 (⟨552,(3),[11],[2],1659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1659,[9,10,11,12],1664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1340 : RecordDataValid section14Catalog 11 (⟨552,(4),[11],[2],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1341 : RecordDataValid section14Catalog 11 (⟨552,(5),[11],[2],1657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1657,[9,10,11,12],1662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1342 : RecordDataValid section14Catalog 11 (⟨552,(6),[11],[2],1658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1658,[9,10,11,12],1663⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1343 : RecordDataValid section14Catalog 11 (⟨552,(7),[11],[2],1657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1657,[9,10,11,12],1662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1344 : RecordDataValid section14Catalog 11 (⟨552,(8),[11],[2],1659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1659,[9,10,11,12],1664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1345 : RecordDataValid section14Catalog 11 (⟨552,(9),[11],[2],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1346 : RecordDataValid section14Catalog 11 (⟨557,(0),[11],[2],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1347 : RecordDataValid section14Catalog 11 (⟨557,(1),[11],[2],1664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1664,[9,10,11,12],1669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1348 : RecordDataValid section14Catalog 11 (⟨557,(2),[11],[2],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1349 : RecordDataValid section14Catalog 11 (⟨557,(3),[11],[2],1665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1665,[9,10,11,12],1670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1350 : RecordDataValid section14Catalog 11 (⟨557,(4),[11],[2],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1351 : RecordDataValid section14Catalog 11 (⟨557,(5),[11],[2],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1352 : RecordDataValid section14Catalog 11 (⟨557,(6),[11],[2],1664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1664,[9,10,11,12],1669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1353 : RecordDataValid section14Catalog 11 (⟨557,(7),[11],[2],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1354 : RecordDataValid section14Catalog 11 (⟨557,(8),[11],[2],1665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1665,[9,10,11,12],1670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1355 : RecordDataValid section14Catalog 11 (⟨557,(9),[11],[2],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1356 : RecordDataValid section14Catalog 11 (⟨567,(0),[11],[2],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1357 : RecordDataValid section14Catalog 11 (⟨567,(1),[11],[2],1666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1666,[9,10,11,12],1671⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1358 : RecordDataValid section14Catalog 11 (⟨567,(2),[11],[2],1667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1667,[9,10,11,12],1672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1359 : RecordDataValid section14Catalog 11 (⟨567,(3),[11],[2],1668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1668,[9,10,11,12],1673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1360 : RecordDataValid section14Catalog 11 (⟨567,(4),[11],[2],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1361 : RecordDataValid section14Catalog 11 (⟨567,(5),[11],[2],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1362 : RecordDataValid section14Catalog 11 (⟨567,(6),[11],[2],1666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1666,[9,10,11,12],1671⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1363 : RecordDataValid section14Catalog 11 (⟨567,(7),[11],[2],1667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1667,[9,10,11,12],1672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1364 : RecordDataValid section14Catalog 11 (⟨567,(8),[11],[2],1668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1668,[9,10,11,12],1673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1365 : RecordDataValid section14Catalog 11 (⟨567,(9),[11],[2],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1366 : RecordDataValid section14Catalog 11 (⟨606,(0),[11],[2],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1367 : RecordDataValid section14Catalog 11 (⟨606,(1),[11],[2],1672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1672,[9,10,11],1677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1368 : RecordDataValid section14Catalog 11 (⟨606,(2),[11],[2],1673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1673,[9,10,11,12],1678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1369 : RecordDataValid section14Catalog 11 (⟨606,(3),[11],[2],1674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1674,[9,10,11,12],1679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1370 : RecordDataValid section14Catalog 11 (⟨606,(4),[11],[2],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1371 : RecordDataValid section14Catalog 11 (⟨606,(5),[11],[2],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1372 : RecordDataValid section14Catalog 11 (⟨606,(6),[11],[2],1672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1672,[9,10,11],1677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1373 : RecordDataValid section14Catalog 11 (⟨606,(7),[11],[2],1673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1673,[9,10,11,12],1678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1374 : RecordDataValid section14Catalog 11 (⟨606,(8),[11],[2],1674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1674,[9,10,11,12],1679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1375 : RecordDataValid section14Catalog 11 (⟨606,(9),[11],[2],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1312).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1312).take 64 = [⟨537,(6),[11],[2],1650⟩,⟨537,(7),[11],[2],1651⟩,⟨537,(8),[11],[2],1652⟩,⟨537,(9),[11],[2],17⟩,⟨542,(0),[11],[2],46⟩,⟨542,(1),[11],[2],46⟩,⟨542,(2),[11],[2],42⟩,⟨542,(3),[11],[2],43⟩,⟨542,(4),[11],[2],44⟩,⟨542,(5),[11],[2],47⟩,⟨542,(6),[11],[2],47⟩,⟨542,(7),[11],[2],47⟩,⟨542,(8),[11],[2],43⟩,⟨542,(9),[11],[2],44⟩,⟨547,(0),[11],[2],1688⟩,⟨547,(1),[11],[2],1689⟩,⟨547,(2),[11],[2],1688⟩,⟨547,(3),[11],[2],1690⟩,⟨547,(4),[11],[2],212⟩,⟨547,(5),[11],[2],1688⟩,⟨547,(6),[11],[2],1689⟩,⟨547,(7),[11],[2],1688⟩,⟨547,(8),[11],[2],1690⟩,⟨547,(9),[11],[2],212⟩,⟨552,(0),[11],[2],1657⟩,⟨552,(1),[11],[2],1658⟩,⟨552,(2),[11],[2],1657⟩,⟨552,(3),[11],[2],1659⟩,⟨552,(4),[11],[2],256⟩,⟨552,(5),[11],[2],1657⟩,⟨552,(6),[11],[2],1658⟩,⟨552,(7),[11],[2],1657⟩,⟨552,(8),[11],[2],1659⟩,⟨552,(9),[11],[2],256⟩,⟨557,(0),[11],[2],1663⟩,⟨557,(1),[11],[2],1664⟩,⟨557,(2),[11],[2],1663⟩,⟨557,(3),[11],[2],1665⟩,⟨557,(4),[11],[2],371⟩,⟨557,(5),[11],[2],1663⟩,⟨557,(6),[11],[2],1664⟩,⟨557,(7),[11],[2],1663⟩,⟨557,(8),[11],[2],1665⟩,⟨557,(9),[11],[2],371⟩,⟨567,(0),[11],[2],1649⟩,⟨567,(1),[11],[2],1666⟩,⟨567,(2),[11],[2],1667⟩,⟨567,(3),[11],[2],1668⟩,⟨567,(4),[11],[2],396⟩,⟨567,(5),[11],[2],1649⟩,⟨567,(6),[11],[2],1666⟩,⟨567,(7),[11],[2],1667⟩,⟨567,(8),[11],[2],1668⟩,⟨567,(9),[11],[2],396⟩,⟨606,(0),[11],[2],1649⟩,⟨606,(1),[11],[2],1672⟩,⟨606,(2),[11],[2],1673⟩,⟨606,(3),[11],[2],1674⟩,⟨606,(4),[11],[2],890⟩,⟨606,(5),[11],[2],1649⟩,⟨606,(6),[11],[2],1672⟩,⟨606,(7),[11],[2],1673⟩,⟨606,(8),[11],[2],1674⟩,⟨606,(9),[11],[2],890⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1312
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1313
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1314
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1315
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1316
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1317
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1318
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1319
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1320
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1321
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1322
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1323
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1324
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1325
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1326
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1327
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1328
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1329
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1330
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1331
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1332
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1333
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1334
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1335
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1336
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1337
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1338
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1339
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1340
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1341
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1342
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1343
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1344
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1345
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1346
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1347
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1348
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1349
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1350
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1351
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1352
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1353
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1354
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1355
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1356
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1357
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1358
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1359
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1360
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1361
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1362
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1363
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1364
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1365
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1366
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1367
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1368
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1369
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1370
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1371
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1372
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1373
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1374
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1375
end Section14Records_11_1312_1376

#print axioms solution
