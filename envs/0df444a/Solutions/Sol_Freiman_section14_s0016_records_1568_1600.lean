-- Prove2me | solution 1 for Freiman.section14_s0016_records_1568_1600
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:37:58.201136+00:00
-- url     : https://prove2.me/submissions/2606a482-162a-4bfd-a1f9-170f761f08f6

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
namespace Section14Records_16_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 16 (⟨234,(14),[4,8,12,16],[10],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 16 (⟨234,(15),[4,8,12,16],[10],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 16 (⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 16 (⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 16 (⟨235,(2),[4,8,12,16],[10],1387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1387,[4,8,9,12,16],1391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 16 (⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 16 (⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 16 (⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 16 (⟨235,(6),[4,8,12,16],[10],1388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1388,[4,8,9,12,16],1392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 16 (⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 16 (⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 16 (⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 16 (⟨235,(10),[4,8,12,16],[10],1387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1387,[4,8,9,12,16],1391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 16 (⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 16 (⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 16 (⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 16 (⟨235,(14),[4,8,12,16],[10],1389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1389,[4,8,9,12,16],1393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 16 (⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 16 (⟨236,(0),[3,4,8,12,15,16],[10],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 16 (⟨236,(1),[3,4,8,12,15,16],[10],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 16 (⟨236,(2),[4,8,12,16],[10],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 16 (⟨236,(3),[3,4,8,12,15,16],[10],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 16 (⟨237,(0),[3,4,8,12,15,16],[10],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 16 (⟨237,(1),[3,4,7,8,15,16],[10],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 16 (⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 16 (⟨237,(3),[4,8,12,16],[10],1271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1271,[4,8,9,12,16],1275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 16 (⟨237,(4),[3,4,8,12,15,16],[10],866⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 16 (⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 16 (⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 16 (⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 16 (⟨237,(8),[4,8,12,16],[10],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 16 (⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1568).take 32 = [⟨234,(14),[4,8,12,16],[10],1386⟩,⟨234,(15),[4,8,12,16],[10],1386⟩,⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩,⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩,⟨235,(2),[4,8,12,16],[10],1387⟩,⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩,⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩,⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩,⟨235,(6),[4,8,12,16],[10],1388⟩,⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩,⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩,⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩,⟨235,(10),[4,8,12,16],[10],1387⟩,⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩,⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩,⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩,⟨235,(14),[4,8,12,16],[10],1389⟩,⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩,⟨236,(0),[3,4,8,12,15,16],[10],861⟩,⟨236,(1),[3,4,8,12,15,16],[10],862⟩,⟨236,(2),[4,8,12,16],[10],861⟩,⟨236,(3),[3,4,8,12,15,16],[10],864⟩,⟨237,(0),[3,4,8,12,15,16],[10],865⟩,⟨237,(1),[3,4,7,8,15,16],[10],594⟩,⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩,⟨237,(3),[4,8,12,16],[10],1271⟩,⟨237,(4),[3,4,8,12,15,16],[10],866⟩,⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩,⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩,⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩,⟨237,(8),[4,8,12,16],[10],865⟩,⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1599
end Section14Records_16_1568_1600

#print axioms solution
