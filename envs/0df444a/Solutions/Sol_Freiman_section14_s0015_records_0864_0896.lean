-- Prove2me | solution 1 for Freiman.section14_s0015_records_0864_0896
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:08:00.94466+00:00
-- url     : https://prove2.me/submissions/270c8107-2533-4b95-ab3a-07322fa9803a

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
namespace Section14Records_15_864_896
private theorem valid864 : RecordDataValid section14Catalog 15 (⟨222,(18),[3,4,8,12,15,16],[10],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid865 : RecordDataValid section14Catalog 15 (⟨222,(19),[3,4,7,8,12,15,16],[10],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid866 : RecordDataValid section14Catalog 15 (⟨222,(20),[3,4,7,8,12,15,16],[10],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid867 : RecordDataValid section14Catalog 15 (⟨222,(21),[3,4,7,8,12,15,16],[10],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid868 : RecordDataValid section14Catalog 15 (⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid869 : RecordDataValid section14Catalog 15 (⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid870 : RecordDataValid section14Catalog 15 (⟨222,(24),[3,4,7,15,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid871 : RecordDataValid section14Catalog 15 (⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid872 : RecordDataValid section14Catalog 15 (⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid873 : RecordDataValid section14Catalog 15 (⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid874 : RecordDataValid section14Catalog 15 (⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid875 : RecordDataValid section14Catalog 15 (⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid876 : RecordDataValid section14Catalog 15 (⟨224,(5),[3,7,15],[10],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid877 : RecordDataValid section14Catalog 15 (⟨224,(6),[3,7,15],[10],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid878 : RecordDataValid section14Catalog 15 (⟨224,(7),[3,7,15],[10],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid879 : RecordDataValid section14Catalog 15 (⟨224,(8),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid880 : RecordDataValid section14Catalog 15 (⟨224,(9),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid881 : RecordDataValid section14Catalog 15 (⟨224,(10),[3,7,15],[10],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid882 : RecordDataValid section14Catalog 15 (⟨224,(11),[3,7,15],[10],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid883 : RecordDataValid section14Catalog 15 (⟨224,(12),[3,7,15],[10],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid884 : RecordDataValid section14Catalog 15 (⟨224,(13),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid885 : RecordDataValid section14Catalog 15 (⟨224,(14),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid886 : RecordDataValid section14Catalog 15 (⟨224,(15),[3,7,15],[10],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid887 : RecordDataValid section14Catalog 15 (⟨224,(16),[3,7,15],[10],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid888 : RecordDataValid section14Catalog 15 (⟨224,(17),[3,7,15],[10],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid889 : RecordDataValid section14Catalog 15 (⟨224,(18),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid890 : RecordDataValid section14Catalog 15 (⟨224,(19),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid891 : RecordDataValid section14Catalog 15 (⟨224,(20),[3,7,15],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid892 : RecordDataValid section14Catalog 15 (⟨224,(21),[3,7,15],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid893 : RecordDataValid section14Catalog 15 (⟨224,(22),[3,7,15],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid894 : RecordDataValid section14Catalog 15 (⟨224,(23),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid895 : RecordDataValid section14Catalog 15 (⟨224,(24),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 864).take 32 = [⟨222,(18),[3,4,8,12,15,16],[10],746⟩,⟨222,(19),[3,4,7,8,12,15,16],[10],534⟩,⟨222,(20),[3,4,7,8,12,15,16],[10],535⟩,⟨222,(21),[3,4,7,8,12,15,16],[10],536⟩,⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩,⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩,⟨222,(24),[3,4,7,15,16],[10],537⟩,⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩,⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩,⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩,⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩,⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩,⟨224,(5),[3,7,15],[10],543⟩,⟨224,(6),[3,7,15],[10],543⟩,⟨224,(7),[3,7,15],[10],544⟩,⟨224,(8),[3,7,15],[10],517⟩,⟨224,(9),[3,7,15],[10],518⟩,⟨224,(10),[3,7,15],[10],545⟩,⟨224,(11),[3,7,15],[10],545⟩,⟨224,(12),[3,7,15],[10],544⟩,⟨224,(13),[3,7,15],[10],517⟩,⟨224,(14),[3,7,15],[10],518⟩,⟨224,(15),[3,7,15],[10],546⟩,⟨224,(16),[3,7,15],[10],546⟩,⟨224,(17),[3,7,15],[10],544⟩,⟨224,(18),[3,7,15],[10],517⟩,⟨224,(19),[3,7,15],[10],518⟩,⟨224,(20),[3,7,15],[10],547⟩,⟨224,(21),[3,7,15],[10],547⟩,⟨224,(22),[3,7,15],[10],547⟩,⟨224,(23),[3,7,15],[10],517⟩,⟨224,(24),[3,7,15],[10],518⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid864
  · exact recordValid_of_data section14Catalog 15 _ hnum valid865
  · exact recordValid_of_data section14Catalog 15 _ hnum valid866
  · exact recordValid_of_data section14Catalog 15 _ hnum valid867
  · exact recordValid_of_data section14Catalog 15 _ hnum valid868
  · exact recordValid_of_data section14Catalog 15 _ hnum valid869
  · exact recordValid_of_data section14Catalog 15 _ hnum valid870
  · exact recordValid_of_data section14Catalog 15 _ hnum valid871
  · exact recordValid_of_data section14Catalog 15 _ hnum valid872
  · exact recordValid_of_data section14Catalog 15 _ hnum valid873
  · exact recordValid_of_data section14Catalog 15 _ hnum valid874
  · exact recordValid_of_data section14Catalog 15 _ hnum valid875
  · exact recordValid_of_data section14Catalog 15 _ hnum valid876
  · exact recordValid_of_data section14Catalog 15 _ hnum valid877
  · exact recordValid_of_data section14Catalog 15 _ hnum valid878
  · exact recordValid_of_data section14Catalog 15 _ hnum valid879
  · exact recordValid_of_data section14Catalog 15 _ hnum valid880
  · exact recordValid_of_data section14Catalog 15 _ hnum valid881
  · exact recordValid_of_data section14Catalog 15 _ hnum valid882
  · exact recordValid_of_data section14Catalog 15 _ hnum valid883
  · exact recordValid_of_data section14Catalog 15 _ hnum valid884
  · exact recordValid_of_data section14Catalog 15 _ hnum valid885
  · exact recordValid_of_data section14Catalog 15 _ hnum valid886
  · exact recordValid_of_data section14Catalog 15 _ hnum valid887
  · exact recordValid_of_data section14Catalog 15 _ hnum valid888
  · exact recordValid_of_data section14Catalog 15 _ hnum valid889
  · exact recordValid_of_data section14Catalog 15 _ hnum valid890
  · exact recordValid_of_data section14Catalog 15 _ hnum valid891
  · exact recordValid_of_data section14Catalog 15 _ hnum valid892
  · exact recordValid_of_data section14Catalog 15 _ hnum valid893
  · exact recordValid_of_data section14Catalog 15 _ hnum valid894
  · exact recordValid_of_data section14Catalog 15 _ hnum valid895
end Section14Records_15_864_896

#print axioms solution
