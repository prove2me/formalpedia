-- Prove2me | solution 1 for Freiman.section14_s0015_records_0896_0928
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:07:52.243613+00:00
-- url     : https://prove2.me/submissions/10f35747-2a0c-4413-850a-a1c3365fee19

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
namespace Section14Records_15_896_928
private theorem valid896 : RecordDataValid section14Catalog 15 (⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid897 : RecordDataValid section14Catalog 15 (⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid898 : RecordDataValid section14Catalog 15 (⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid899 : RecordDataValid section14Catalog 15 (⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid900 : RecordDataValid section14Catalog 15 (⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid901 : RecordDataValid section14Catalog 15 (⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid902 : RecordDataValid section14Catalog 15 (⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid903 : RecordDataValid section14Catalog 15 (⟨225,(7),[3,7,15],[10],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid904 : RecordDataValid section14Catalog 15 (⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid905 : RecordDataValid section14Catalog 15 (⟨225,(9),[3,7,15],[10],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid906 : RecordDataValid section14Catalog 15 (⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid907 : RecordDataValid section14Catalog 15 (⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid908 : RecordDataValid section14Catalog 15 (⟨225,(12),[3,7,15],[10],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid909 : RecordDataValid section14Catalog 15 (⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid910 : RecordDataValid section14Catalog 15 (⟨225,(14),[3,7,15],[10],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid911 : RecordDataValid section14Catalog 15 (⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid912 : RecordDataValid section14Catalog 15 (⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid913 : RecordDataValid section14Catalog 15 (⟨225,(17),[3,7,15],[10],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid914 : RecordDataValid section14Catalog 15 (⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid915 : RecordDataValid section14Catalog 15 (⟨225,(19),[3,7,15],[10],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid916 : RecordDataValid section14Catalog 15 (⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid917 : RecordDataValid section14Catalog 15 (⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid918 : RecordDataValid section14Catalog 15 (⟨225,(22),[3,7,15],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid919 : RecordDataValid section14Catalog 15 (⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid920 : RecordDataValid section14Catalog 15 (⟨225,(24),[3,7,15],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid921 : RecordDataValid section14Catalog 15 (⟨226,(0),[3,4,8,12,15,16],[10],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid922 : RecordDataValid section14Catalog 15 (⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid923 : RecordDataValid section14Catalog 15 (⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid924 : RecordDataValid section14Catalog 15 (⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid925 : RecordDataValid section14Catalog 15 (⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid926 : RecordDataValid section14Catalog 15 (⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid927 : RecordDataValid section14Catalog 15 (⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 896).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 896).take 32 = [⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩,⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩,⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩,⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩,⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩,⟨225,(7),[3,7,15],[10],753⟩,⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩,⟨225,(9),[3,7,15],[10],753⟩,⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩,⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩,⟨225,(12),[3,7,15],[10],757⟩,⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩,⟨225,(14),[3,7,15],[10],757⟩,⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩,⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩,⟨225,(17),[3,7,15],[10],761⟩,⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩,⟨225,(19),[3,7,15],[10],761⟩,⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩,⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩,⟨225,(22),[3,7,15],[10],547⟩,⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩,⟨225,(24),[3,7,15],[10],547⟩,⟨226,(0),[3,4,8,12,15,16],[10],766⟩,⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩,⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩,⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩,⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid896
  · exact recordValid_of_data section14Catalog 15 _ hnum valid897
  · exact recordValid_of_data section14Catalog 15 _ hnum valid898
  · exact recordValid_of_data section14Catalog 15 _ hnum valid899
  · exact recordValid_of_data section14Catalog 15 _ hnum valid900
  · exact recordValid_of_data section14Catalog 15 _ hnum valid901
  · exact recordValid_of_data section14Catalog 15 _ hnum valid902
  · exact recordValid_of_data section14Catalog 15 _ hnum valid903
  · exact recordValid_of_data section14Catalog 15 _ hnum valid904
  · exact recordValid_of_data section14Catalog 15 _ hnum valid905
  · exact recordValid_of_data section14Catalog 15 _ hnum valid906
  · exact recordValid_of_data section14Catalog 15 _ hnum valid907
  · exact recordValid_of_data section14Catalog 15 _ hnum valid908
  · exact recordValid_of_data section14Catalog 15 _ hnum valid909
  · exact recordValid_of_data section14Catalog 15 _ hnum valid910
  · exact recordValid_of_data section14Catalog 15 _ hnum valid911
  · exact recordValid_of_data section14Catalog 15 _ hnum valid912
  · exact recordValid_of_data section14Catalog 15 _ hnum valid913
  · exact recordValid_of_data section14Catalog 15 _ hnum valid914
  · exact recordValid_of_data section14Catalog 15 _ hnum valid915
  · exact recordValid_of_data section14Catalog 15 _ hnum valid916
  · exact recordValid_of_data section14Catalog 15 _ hnum valid917
  · exact recordValid_of_data section14Catalog 15 _ hnum valid918
  · exact recordValid_of_data section14Catalog 15 _ hnum valid919
  · exact recordValid_of_data section14Catalog 15 _ hnum valid920
  · exact recordValid_of_data section14Catalog 15 _ hnum valid921
  · exact recordValid_of_data section14Catalog 15 _ hnum valid922
  · exact recordValid_of_data section14Catalog 15 _ hnum valid923
  · exact recordValid_of_data section14Catalog 15 _ hnum valid924
  · exact recordValid_of_data section14Catalog 15 _ hnum valid925
  · exact recordValid_of_data section14Catalog 15 _ hnum valid926
  · exact recordValid_of_data section14Catalog 15 _ hnum valid927
end Section14Records_15_896_928

#print axioms solution
