-- Prove2me | solution 1 for Freiman.section14_s0012_records_1824_1856
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:11:24.570225+00:00
-- url     : https://prove2.me/submissions/2760bab7-c3ba-4a63-b5ee-e2ff98569d09

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
namespace Section14Records_12_1824_1856
private theorem valid1824 : RecordDataValid section14Catalog 12 (⟨270,(7),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1825 : RecordDataValid section14Catalog 12 (⟨270,(8),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1826 : RecordDataValid section14Catalog 12 (⟨270,(9),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1827 : RecordDataValid section14Catalog 12 (⟨270,(10),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1828 : RecordDataValid section14Catalog 12 (⟨270,(11),[8,12],[10],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1829 : RecordDataValid section14Catalog 12 (⟨270,(12),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1830 : RecordDataValid section14Catalog 12 (⟨270,(13),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1831 : RecordDataValid section14Catalog 12 (⟨270,(14),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1832 : RecordDataValid section14Catalog 12 (⟨270,(15),[8,12],[10],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1833 : RecordDataValid section14Catalog 12 (⟨273,(0),[8,12],[10],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1834 : RecordDataValid section14Catalog 12 (⟨273,(1),[8,12],[10],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1835 : RecordDataValid section14Catalog 12 (⟨273,(2),[8,12],[10],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1836 : RecordDataValid section14Catalog 12 (⟨273,(3),[8,12],[10],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1837 : RecordDataValid section14Catalog 12 (⟨273,(4),[8,12],[10],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1838 : RecordDataValid section14Catalog 12 (⟨273,(5),[8,12],[10],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1839 : RecordDataValid section14Catalog 12 (⟨273,(6),[8,12],[10],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1840 : RecordDataValid section14Catalog 12 (⟨273,(7),[8,12],[10],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1841 : RecordDataValid section14Catalog 12 (⟨273,(8),[8,12],[10],1102⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1102,[3,5,7,8,9,11,12,15],1106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1842 : RecordDataValid section14Catalog 12 (⟨273,(9),[8,12],[10],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1843 : RecordDataValid section14Catalog 12 (⟨275,(0),[8,12],[10],1420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1420,[5,8,9,12],1425⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1844 : RecordDataValid section14Catalog 12 (⟨275,(1),[8,12],[10],1420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1420,[5,8,9,12],1425⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1845 : RecordDataValid section14Catalog 12 (⟨275,(2),[8,12],[10],1421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1421,[5,8,9,12],1426⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1846 : RecordDataValid section14Catalog 12 (⟨275,(3),[8,12],[10],1422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1422,[5,8,9,12],1427⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1847 : RecordDataValid section14Catalog 12 (⟨275,(4),[8,12],[10],1423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1423,[5,8,9,12],1428⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1848 : RecordDataValid section14Catalog 12 (⟨275,(5),[8,12],[10],1424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1424,[5,8,9,12],1429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1849 : RecordDataValid section14Catalog 12 (⟨275,(6),[8,12],[10],1424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1424,[5,8,9,12],1429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1850 : RecordDataValid section14Catalog 12 (⟨275,(7),[8,12],[10],1424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1424,[5,8,9,12],1429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1851 : RecordDataValid section14Catalog 12 (⟨275,(8),[8,12],[10],1422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1422,[5,8,9,12],1427⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1852 : RecordDataValid section14Catalog 12 (⟨275,(9),[8,12],[10],1423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1423,[5,8,9,12],1428⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1853 : RecordDataValid section14Catalog 12 (⟨278,(0),[8,12],[10],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1854 : RecordDataValid section14Catalog 12 (⟨278,(1),[8,12],[10],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1855 : RecordDataValid section14Catalog 12 (⟨278,(2),[8,12],[10],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1824).take 32 = [⟨270,(7),[8,12],[10],1417⟩,⟨270,(8),[8,12],[10],1418⟩,⟨270,(9),[8,12],[10],1418⟩,⟨270,(10),[8,12],[10],1418⟩,⟨270,(11),[8,12],[10],1418⟩,⟨270,(12),[8,12],[10],1419⟩,⟨270,(13),[8,12],[10],1419⟩,⟨270,(14),[8,12],[10],1419⟩,⟨270,(15),[8,12],[10],1419⟩,⟨273,(0),[8,12],[10],1098⟩,⟨273,(1),[8,12],[10],1099⟩,⟨273,(2),[8,12],[10],1100⟩,⟨273,(3),[8,12],[10],1100⟩,⟨273,(4),[8,12],[10],1100⟩,⟨273,(5),[8,12],[10],1098⟩,⟨273,(6),[8,12],[10],1099⟩,⟨273,(7),[8,12],[10],1101⟩,⟨273,(8),[8,12],[10],1102⟩,⟨273,(9),[8,12],[10],1101⟩,⟨275,(0),[8,12],[10],1420⟩,⟨275,(1),[8,12],[10],1420⟩,⟨275,(2),[8,12],[10],1421⟩,⟨275,(3),[8,12],[10],1422⟩,⟨275,(4),[8,12],[10],1423⟩,⟨275,(5),[8,12],[10],1424⟩,⟨275,(6),[8,12],[10],1424⟩,⟨275,(7),[8,12],[10],1424⟩,⟨275,(8),[8,12],[10],1422⟩,⟨275,(9),[8,12],[10],1423⟩,⟨278,(0),[8,12],[10],1108⟩,⟨278,(1),[8,12],[10],1109⟩,⟨278,(2),[8,12],[10],1110⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1824
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1825
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1826
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1827
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1828
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1829
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1830
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1831
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1832
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1833
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1834
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1835
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1836
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1837
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1838
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1839
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1840
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1841
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1842
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1843
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1844
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1845
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1846
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1847
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1848
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1849
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1850
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1851
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1852
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1853
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1854
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1855
end Section14Records_12_1824_1856

#print axioms solution
