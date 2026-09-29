-- Prove2me | solution 1 for Freiman.section14_s0012_records_0928_0960
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:40:26.225986+00:00
-- url     : https://prove2.me/submissions/5ef89916-4432-433b-bee7-aac139e3817b

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
namespace Section14Records_12_928_960
private theorem valid928 : RecordDataValid section14Catalog 12 (⟨144,(0),[4,8,12,16],[10],590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨590,[1,4,5,6,8,9,10,12,13,16],591⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid929 : RecordDataValid section14Catalog 12 (⟨144,(1),[4,8,12,16],[10],591⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨591,[1,4,5,6,8,9,10,12,13,16],592⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid930 : RecordDataValid section14Catalog 12 (⟨144,(2),[4,8,12,16],[10],590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨590,[1,4,5,6,8,9,10,12,13,16],591⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid931 : RecordDataValid section14Catalog 12 (⟨144,(3),[4,8,12,16],[10],592⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨592,[1,4,5,6,8,9,10,12,13,16],593⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid932 : RecordDataValid section14Catalog 12 (⟨145,(0),[4,8,12,16],[10],593⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨593,[1,4,5,6,8,9,10,12,13,16],594⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid933 : RecordDataValid section14Catalog 12 (⟨145,(1),[12],[10],1714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1714,[12],1719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid934 : RecordDataValid section14Catalog 12 (⟨145,(2),[4,8,12,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid935 : RecordDataValid section14Catalog 12 (⟨145,(3),[4,8,12,16],[10],1271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1271,[4,8,9,12,16],1275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid936 : RecordDataValid section14Catalog 12 (⟨145,(4),[4,8,12,16],[10],597⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨597,[1,4,5,6,8,9,10,12,13,16],598⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid937 : RecordDataValid section14Catalog 12 (⟨145,(5),[4,8,12,16],[10],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid938 : RecordDataValid section14Catalog 12 (⟨145,(6),[4,8,12,16],[10],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid939 : RecordDataValid section14Catalog 12 (⟨145,(7),[4,8,12,16],[10],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid940 : RecordDataValid section14Catalog 12 (⟨145,(8),[4,8,12,16],[10],593⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨593,[1,4,5,6,8,9,10,12,13,16],594⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid941 : RecordDataValid section14Catalog 12 (⟨145,(9),[4,8,12,16],[10],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid942 : RecordDataValid section14Catalog 12 (⟨145,(10),[4,8,12,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid943 : RecordDataValid section14Catalog 12 (⟨145,(11),[4,8,12,16],[10],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid944 : RecordDataValid section14Catalog 12 (⟨145,(12),[4,8,12,16],[10],601⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨601,[1,4,5,6,8,9,10,12,13,16],602⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid945 : RecordDataValid section14Catalog 12 (⟨145,(13),[4,8,12,16],[10],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid946 : RecordDataValid section14Catalog 12 (⟨145,(14),[4,8,12,16],[10],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid947 : RecordDataValid section14Catalog 12 (⟨145,(15),[4,8,12,16],[10],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid948 : RecordDataValid section14Catalog 12 (⟨146,(0),[4,8,12,16],[10],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid949 : RecordDataValid section14Catalog 12 (⟨146,(1),[4,8,12,16],[10],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid950 : RecordDataValid section14Catalog 12 (⟨146,(2),[4,8,12,16],[10],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid951 : RecordDataValid section14Catalog 12 (⟨146,(3),[4,8,12,16],[10],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid952 : RecordDataValid section14Catalog 12 (⟨146,(4),[4,8,12,16],[10],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid953 : RecordDataValid section14Catalog 12 (⟨146,(5),[4,8,12,16],[10],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid954 : RecordDataValid section14Catalog 12 (⟨146,(6),[4,8,12,16],[10],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid955 : RecordDataValid section14Catalog 12 (⟨146,(7),[4,8,12,16],[10],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid956 : RecordDataValid section14Catalog 12 (⟨146,(8),[4,8,12,16],[10],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid957 : RecordDataValid section14Catalog 12 (⟨146,(9),[4,8,12,16],[10],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid958 : RecordDataValid section14Catalog 12 (⟨146,(10),[4,8,12,16],[10],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid959 : RecordDataValid section14Catalog 12 (⟨146,(11),[4,8,12,16],[10],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 928).take 32 = [⟨144,(0),[4,8,12,16],[10],590⟩,⟨144,(1),[4,8,12,16],[10],591⟩,⟨144,(2),[4,8,12,16],[10],590⟩,⟨144,(3),[4,8,12,16],[10],592⟩,⟨145,(0),[4,8,12,16],[10],593⟩,⟨145,(1),[12],[10],1714⟩,⟨145,(2),[4,8,12,16],[10],595⟩,⟨145,(3),[4,8,12,16],[10],1271⟩,⟨145,(4),[4,8,12,16],[10],597⟩,⟨145,(5),[4,8,12,16],[10],598⟩,⟨145,(6),[4,8,12,16],[10],599⟩,⟨145,(7),[4,8,12,16],[10],600⟩,⟨145,(8),[4,8,12,16],[10],593⟩,⟨145,(9),[4,8,12,16],[10],594⟩,⟨145,(10),[4,8,12,16],[10],595⟩,⟨145,(11),[4,8,12,16],[10],596⟩,⟨145,(12),[4,8,12,16],[10],601⟩,⟨145,(13),[4,8,12,16],[10],602⟩,⟨145,(14),[4,8,12,16],[10],603⟩,⟨145,(15),[4,8,12,16],[10],604⟩,⟨146,(0),[4,8,12,16],[10],869⟩,⟨146,(1),[4,8,12,16],[10],870⟩,⟨146,(2),[4,8,12,16],[10],607⟩,⟨146,(3),[4,8,12,16],[10],871⟩,⟨146,(4),[4,8,12,16],[10],609⟩,⟨146,(5),[4,8,12,16],[10],610⟩,⟨146,(6),[4,8,12,16],[10],611⟩,⟨146,(7),[4,8,12,16],[10],612⟩,⟨146,(8),[4,8,12,16],[10],613⟩,⟨146,(9),[4,8,12,16],[10],614⟩,⟨146,(10),[4,8,12,16],[10],615⟩,⟨146,(11),[4,8,12,16],[10],616⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid928
  · exact recordValid_of_data section14Catalog 12 _ hnum valid929
  · exact recordValid_of_data section14Catalog 12 _ hnum valid930
  · exact recordValid_of_data section14Catalog 12 _ hnum valid931
  · exact recordValid_of_data section14Catalog 12 _ hnum valid932
  · exact recordValid_of_data section14Catalog 12 _ hnum valid933
  · exact recordValid_of_data section14Catalog 12 _ hnum valid934
  · exact recordValid_of_data section14Catalog 12 _ hnum valid935
  · exact recordValid_of_data section14Catalog 12 _ hnum valid936
  · exact recordValid_of_data section14Catalog 12 _ hnum valid937
  · exact recordValid_of_data section14Catalog 12 _ hnum valid938
  · exact recordValid_of_data section14Catalog 12 _ hnum valid939
  · exact recordValid_of_data section14Catalog 12 _ hnum valid940
  · exact recordValid_of_data section14Catalog 12 _ hnum valid941
  · exact recordValid_of_data section14Catalog 12 _ hnum valid942
  · exact recordValid_of_data section14Catalog 12 _ hnum valid943
  · exact recordValid_of_data section14Catalog 12 _ hnum valid944
  · exact recordValid_of_data section14Catalog 12 _ hnum valid945
  · exact recordValid_of_data section14Catalog 12 _ hnum valid946
  · exact recordValid_of_data section14Catalog 12 _ hnum valid947
  · exact recordValid_of_data section14Catalog 12 _ hnum valid948
  · exact recordValid_of_data section14Catalog 12 _ hnum valid949
  · exact recordValid_of_data section14Catalog 12 _ hnum valid950
  · exact recordValid_of_data section14Catalog 12 _ hnum valid951
  · exact recordValid_of_data section14Catalog 12 _ hnum valid952
  · exact recordValid_of_data section14Catalog 12 _ hnum valid953
  · exact recordValid_of_data section14Catalog 12 _ hnum valid954
  · exact recordValid_of_data section14Catalog 12 _ hnum valid955
  · exact recordValid_of_data section14Catalog 12 _ hnum valid956
  · exact recordValid_of_data section14Catalog 12 _ hnum valid957
  · exact recordValid_of_data section14Catalog 12 _ hnum valid958
  · exact recordValid_of_data section14Catalog 12 _ hnum valid959
end Section14Records_12_928_960

#print axioms solution
