-- Prove2me | solution 1 for Freiman.section14_s0007_records_1888_1920
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:24:38.864793+00:00
-- url     : https://prove2.me/submissions/d24d5ec6-6bf5-43fc-8339-3d2b759aa91a

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
namespace Section14Records_7_1888_1920
private theorem valid1888 : RecordDataValid section14Catalog 7 (⟨237,(4),[7],[10],1626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1626,[7],1631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1889 : RecordDataValid section14Catalog 7 (⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1890 : RecordDataValid section14Catalog 7 (⟨237,(5),[3,7],[11],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1891 : RecordDataValid section14Catalog 7 (⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1892 : RecordDataValid section14Catalog 7 (⟨237,(6),[3,7],[11],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1893 : RecordDataValid section14Catalog 7 (⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1894 : RecordDataValid section14Catalog 7 (⟨237,(7),[3,7],[11],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1895 : RecordDataValid section14Catalog 7 (⟨237,(8),[3,7],[11],867⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨867,[1,2,3,6,7,10,11,13,14,15],868⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1896 : RecordDataValid section14Catalog 7 (⟨237,(8),[3,7,15],[10],867⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨867,[1,2,3,6,7,10,11,13,14,15],868⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1897 : RecordDataValid section14Catalog 7 (⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1898 : RecordDataValid section14Catalog 7 (⟨237,(9),[3,7],[11],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1899 : RecordDataValid section14Catalog 7 (⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1900 : RecordDataValid section14Catalog 7 (⟨237,(10),[3,7],[11],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1901 : RecordDataValid section14Catalog 7 (⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1902 : RecordDataValid section14Catalog 7 (⟨237,(11),[3,7],[11],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1903 : RecordDataValid section14Catalog 7 (⟨237,(12),[3,7],[11],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1904 : RecordDataValid section14Catalog 7 (⟨237,(12),[7],[10],1627⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1627,[7],1632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1905 : RecordDataValid section14Catalog 7 (⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1906 : RecordDataValid section14Catalog 7 (⟨237,(13),[3,7],[11],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1907 : RecordDataValid section14Catalog 7 (⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1908 : RecordDataValid section14Catalog 7 (⟨237,(14),[3,7],[11],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1909 : RecordDataValid section14Catalog 7 (⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1910 : RecordDataValid section14Catalog 7 (⟨237,(15),[3,7],[11],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1911 : RecordDataValid section14Catalog 7 (⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1912 : RecordDataValid section14Catalog 7 (⟨238,(0),[3,7],[11],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1913 : RecordDataValid section14Catalog 7 (⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1914 : RecordDataValid section14Catalog 7 (⟨238,(1),[3,7],[11],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1915 : RecordDataValid section14Catalog 7 (⟨238,(2),[3,7],[11],1084⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1084,[3,5,6,7],1088⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1916 : RecordDataValid section14Catalog 7 (⟨238,(2),[3,7,15],[10],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1917 : RecordDataValid section14Catalog 7 (⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1918 : RecordDataValid section14Catalog 7 (⟨238,(3),[7],[11],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1919 : RecordDataValid section14Catalog 7 (⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1888).take 32 = [⟨237,(4),[7],[10],1626⟩,⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩,⟨237,(5),[3,7],[11],598⟩,⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩,⟨237,(6),[3,7],[11],599⟩,⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩,⟨237,(7),[3,7],[11],600⟩,⟨237,(8),[3,7],[11],867⟩,⟨237,(8),[3,7,15],[10],867⟩,⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩,⟨237,(9),[3,7],[11],594⟩,⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩,⟨237,(10),[3,7],[11],595⟩,⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩,⟨237,(11),[3,7],[11],596⟩,⟨237,(12),[3,7],[11],868⟩,⟨237,(12),[7],[10],1627⟩,⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩,⟨237,(13),[3,7],[11],602⟩,⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩,⟨237,(14),[3,7],[11],603⟩,⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩,⟨237,(15),[3,7],[11],604⟩,⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩,⟨238,(0),[3,7],[11],869⟩,⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩,⟨238,(1),[3,7],[11],870⟩,⟨238,(2),[3,7],[11],1084⟩,⟨238,(2),[3,7,15],[10],607⟩,⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩,⟨238,(3),[7],[11],871⟩,⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1888
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1889
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1890
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1891
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1892
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1893
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1894
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1895
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1896
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1897
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1898
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1899
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1900
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1901
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1902
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1903
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1904
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1905
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1906
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1907
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1908
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1909
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1910
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1911
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1912
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1913
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1914
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1915
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1916
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1917
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1918
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1919
end Section14Records_7_1888_1920

#print axioms solution
