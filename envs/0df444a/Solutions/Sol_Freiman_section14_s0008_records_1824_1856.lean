-- Prove2me | solution 1 for Freiman.section14_s0008_records_1824_1856
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:41:07.884134+00:00
-- url     : https://prove2.me/submissions/b652c474-f061-4b35-ab9e-f3784bf1daf2

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
namespace Section14Records_8_1824_1856
private theorem valid1824 : RecordDataValid section14Catalog 8 (⟨237,(0),[3,4,8,12,15,16],[10],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1825 : RecordDataValid section14Catalog 8 (⟨237,(1),[3,4,7,8,15,16],[10],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1826 : RecordDataValid section14Catalog 8 (⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1827 : RecordDataValid section14Catalog 8 (⟨237,(3),[4,8,12,16],[10],1271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1271,[4,8,9,12,16],1275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1828 : RecordDataValid section14Catalog 8 (⟨237,(4),[3,4,8,12,15,16],[10],866⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1829 : RecordDataValid section14Catalog 8 (⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1830 : RecordDataValid section14Catalog 8 (⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1831 : RecordDataValid section14Catalog 8 (⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1832 : RecordDataValid section14Catalog 8 (⟨237,(8),[4,8,12,16],[10],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1833 : RecordDataValid section14Catalog 8 (⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1834 : RecordDataValid section14Catalog 8 (⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1835 : RecordDataValid section14Catalog 8 (⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1836 : RecordDataValid section14Catalog 8 (⟨237,(12),[3,4,8,12,15,16],[10],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1837 : RecordDataValid section14Catalog 8 (⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1838 : RecordDataValid section14Catalog 8 (⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1839 : RecordDataValid section14Catalog 8 (⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1840 : RecordDataValid section14Catalog 8 (⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1841 : RecordDataValid section14Catalog 8 (⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1842 : RecordDataValid section14Catalog 8 (⟨238,(2),[4,8,12,16],[10],1390⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1390,[4,8,12,16],1394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1843 : RecordDataValid section14Catalog 8 (⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1844 : RecordDataValid section14Catalog 8 (⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1845 : RecordDataValid section14Catalog 8 (⟨238,(5),[3,4,7,8,12,15,16],[10],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1846 : RecordDataValid section14Catalog 8 (⟨238,(6),[4,8,12,16],[10],1391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1391,[4,8,9,12,16],1396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1847 : RecordDataValid section14Catalog 8 (⟨238,(7),[3,4,7,8,12,15,16],[10],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1848 : RecordDataValid section14Catalog 8 (⟨238,(8),[3,4,7,8,12,15,16],[10],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1849 : RecordDataValid section14Catalog 8 (⟨238,(9),[3,4,7,8,12,15,16],[10],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1850 : RecordDataValid section14Catalog 8 (⟨238,(10),[4,8,12,16],[10],1392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1392,[4,8,9,12,16],1397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1851 : RecordDataValid section14Catalog 8 (⟨238,(11),[3,4,7,8,12,15,16],[10],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1852 : RecordDataValid section14Catalog 8 (⟨238,(12),[3,4,7,8,12,15,16],[10],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1853 : RecordDataValid section14Catalog 8 (⟨238,(13),[3,4,7,8,12,15,16],[10],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1854 : RecordDataValid section14Catalog 8 (⟨238,(14),[4,8,12,16],[10],1393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1393,[4,8,9,12,16],1398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1855 : RecordDataValid section14Catalog 8 (⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1824).take 32 = [⟨237,(0),[3,4,8,12,15,16],[10],865⟩,⟨237,(1),[3,4,7,8,15,16],[10],594⟩,⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩,⟨237,(3),[4,8,12,16],[10],1271⟩,⟨237,(4),[3,4,8,12,15,16],[10],866⟩,⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩,⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩,⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩,⟨237,(8),[4,8,12,16],[10],865⟩,⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩,⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩,⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩,⟨237,(12),[3,4,8,12,15,16],[10],868⟩,⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩,⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩,⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩,⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩,⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩,⟨238,(2),[4,8,12,16],[10],1390⟩,⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩,⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩,⟨238,(5),[3,4,7,8,12,15,16],[10],610⟩,⟨238,(6),[4,8,12,16],[10],1391⟩,⟨238,(7),[3,4,7,8,12,15,16],[10],612⟩,⟨238,(8),[3,4,7,8,12,15,16],[10],613⟩,⟨238,(9),[3,4,7,8,12,15,16],[10],614⟩,⟨238,(10),[4,8,12,16],[10],1392⟩,⟨238,(11),[3,4,7,8,12,15,16],[10],616⟩,⟨238,(12),[3,4,7,8,12,15,16],[10],617⟩,⟨238,(13),[3,4,7,8,12,15,16],[10],618⟩,⟨238,(14),[4,8,12,16],[10],1393⟩,⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1824
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1825
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1826
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1827
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1828
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1829
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1830
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1831
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1832
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1833
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1834
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1835
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1836
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1837
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1838
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1839
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1840
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1841
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1842
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1843
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1844
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1845
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1846
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1847
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1848
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1849
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1850
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1851
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1852
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1853
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1854
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1855
end Section14Records_8_1824_1856

#print axioms solution
