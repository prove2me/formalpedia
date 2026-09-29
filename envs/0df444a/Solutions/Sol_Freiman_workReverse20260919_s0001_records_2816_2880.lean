-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_2816_2880
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T02:06:02.379+00:00
-- url     : https://prove2.me/submissions/411e7619-8a65-4331-8dce-857e16e4c1f8

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2816_2848
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2816_2848
private theorem valid2816 : RecordDataValid section14Catalog 1 (⟨138,(11),[1,5,6,13],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2817 : RecordDataValid section14Catalog 1 (⟨138,(12),[1,5,6,13],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2818 : RecordDataValid section14Catalog 1 (⟨138,(13),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2819 : RecordDataValid section14Catalog 1 (⟨138,(14),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2820 : RecordDataValid section14Catalog 1 (⟨138,(15),[1,5,6,13],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2821 : RecordDataValid section14Catalog 1 (⟨138,(16),[1,5,6,13],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2822 : RecordDataValid section14Catalog 1 (⟨138,(17),[1,5,6,13],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2823 : RecordDataValid section14Catalog 1 (⟨138,(18),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2824 : RecordDataValid section14Catalog 1 (⟨138,(19),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2825 : RecordDataValid section14Catalog 1 (⟨138,(20),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2826 : RecordDataValid section14Catalog 1 (⟨138,(21),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2827 : RecordDataValid section14Catalog 1 (⟨138,(22),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2828 : RecordDataValid section14Catalog 1 (⟨138,(23),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2829 : RecordDataValid section14Catalog 1 (⟨138,(24),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2830 : RecordDataValid section14Catalog 1 (⟨139,(0),[1,5,6,13],[170],548⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨548,[1,4,5,6,8,9,10,12,13,16],549⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2831 : RecordDataValid section14Catalog 1 (⟨139,(1),[1,5,6,13],[170],549⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨549,[1,4,5,6,8,9,10,12,13,16],550⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2832 : RecordDataValid section14Catalog 1 (⟨139,(2),[1,5,6,13],[170],548⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨548,[1,4,5,6,8,9,10,12,13,16],549⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2833 : RecordDataValid section14Catalog 1 (⟨139,(3),[1,5,6,13],[170],550⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨550,[1,4,5,6,8,9,10,12,13,16],551⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2834 : RecordDataValid section14Catalog 1 (⟨139,(4),[1,5,6,13],[170],551⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨551,[1,4,5,6,8,9,10,12,13,16],552⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2835 : RecordDataValid section14Catalog 1 (⟨139,(5),[1,5,6,13],[170],552⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨552,[1,4,5,6,9,10,13,16],553⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2836 : RecordDataValid section14Catalog 1 (⟨139,(6),[1,5,6,13],[170],553⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨553,[1,4,5,6,9,10,13,16],554⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2837 : RecordDataValid section14Catalog 1 (⟨139,(7),[1,5,6,13],[170],554⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨554,[1,4,5,6,9,10,13,16],555⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2838 : RecordDataValid section14Catalog 1 (⟨139,(8),[1,5,6,13],[170],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2839 : RecordDataValid section14Catalog 1 (⟨139,(9),[1,5,6,13],[170],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2840 : RecordDataValid section14Catalog 1 (⟨139,(10),[1,5,6,13],[170],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2841 : RecordDataValid section14Catalog 1 (⟨139,(11),[1,5,6,13],[170],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2842 : RecordDataValid section14Catalog 1 (⟨139,(12),[1,5,6,13],[170],559⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨559,[1,4,5,6,8,9,10,12,13,16],560⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2843 : RecordDataValid section14Catalog 1 (⟨139,(13),[1,5,6,13],[170],560⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨560,[1,4,5,6,8,9,10,12,13,16],561⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2844 : RecordDataValid section14Catalog 1 (⟨139,(14),[1,5,6,13],[170],561⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨561,[1,4,5,6,8,9,10,12,13,16],562⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2845 : RecordDataValid section14Catalog 1 (⟨139,(15),[1,5,6,13],[170],562⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨562,[1,4,5,6,8,9,10,12,13,16],563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2846 : RecordDataValid section14Catalog 1 (⟨139,(16),[1,5,6,13],[170],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2847 : RecordDataValid section14Catalog 1 (⟨139,(17),[1,5,6,13],[170],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2816_2848 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2816).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2816).take 32 = [⟨138,(11),[1,5,6,13],[170],545⟩,⟨138,(12),[1,5,6,13],[170],544⟩,⟨138,(13),[1,5,6,13],[170],517⟩,⟨138,(14),[1,5,6,13],[170],518⟩,⟨138,(15),[1,5,6,13],[170],546⟩,⟨138,(16),[1,5,6,13],[170],546⟩,⟨138,(17),[1,5,6,13],[170],544⟩,⟨138,(18),[1,5,6,13],[170],517⟩,⟨138,(19),[1,5,6,13],[170],518⟩,⟨138,(20),[1,5,6,13],[170],547⟩,⟨138,(21),[1,5,6,13],[170],547⟩,⟨138,(22),[1,5,6,13],[170],547⟩,⟨138,(23),[1,5,6,13],[170],517⟩,⟨138,(24),[1,5,6,13],[170],518⟩,⟨139,(0),[1,5,6,13],[170],548⟩,⟨139,(1),[1,5,6,13],[170],549⟩,⟨139,(2),[1,5,6,13],[170],548⟩,⟨139,(3),[1,5,6,13],[170],550⟩,⟨139,(4),[1,5,6,13],[170],551⟩,⟨139,(5),[1,5,6,13],[170],552⟩,⟨139,(6),[1,5,6,13],[170],553⟩,⟨139,(7),[1,5,6,13],[170],554⟩,⟨139,(8),[1,5,6,13],[170],555⟩,⟨139,(9),[1,5,6,13],[170],556⟩,⟨139,(10),[1,5,6,13],[170],557⟩,⟨139,(11),[1,5,6,13],[170],558⟩,⟨139,(12),[1,5,6,13],[170],559⟩,⟨139,(13),[1,5,6,13],[170],560⟩,⟨139,(14),[1,5,6,13],[170],561⟩,⟨139,(15),[1,5,6,13],[170],562⟩,⟨139,(16),[1,5,6,13],[170],555⟩,⟨139,(17),[1,5,6,13],[170],556⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2816
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2817
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2818
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2819
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2820
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2821
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2822
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2823
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2824
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2825
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2826
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2827
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2828
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2829
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2830
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2831
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2832
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2833
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2834
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2835
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2836
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2837
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2838
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2839
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2840
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2841
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2842
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2843
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2844
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2845
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2846
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2847
end Section14Records_1_2816_2848

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2816_2848


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2848_2880
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2848_2880
private theorem valid2848 : RecordDataValid section14Catalog 1 (⟨139,(18),[1,5,6,13],[170],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2849 : RecordDataValid section14Catalog 1 (⟨139,(19),[1,5,6,13],[170],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2850 : RecordDataValid section14Catalog 1 (⟨140,(0),[1,5,6,13],[170],563⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨563,[1,4,5,6,8,9,10,12,13,16],564⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2851 : RecordDataValid section14Catalog 1 (⟨140,(1),[1,5,6,13],[170],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2852 : RecordDataValid section14Catalog 1 (⟨140,(2),[1,5,6,13],[170],565⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨565,[1,4,5,6,8,9,10,12,13,16],566⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2853 : RecordDataValid section14Catalog 1 (⟨140,(3),[1,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2854 : RecordDataValid section14Catalog 1 (⟨140,(4),[1,5,6,13],[170],566⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨566,[1,4,5,6,8,9,10,12,13,16],567⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2855 : RecordDataValid section14Catalog 1 (⟨140,(5),[1,5,6,13],[170],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2856 : RecordDataValid section14Catalog 1 (⟨140,(6),[1,5,6,13],[170],567⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨567,[1,4,5,6,10,13,16],568⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2857 : RecordDataValid section14Catalog 1 (⟨140,(7),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2858 : RecordDataValid section14Catalog 1 (⟨142,(0),[1,5,6,13],[170],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2859 : RecordDataValid section14Catalog 1 (⟨142,(1),[1,5,6,13],[170],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2860 : RecordDataValid section14Catalog 1 (⟨142,(2),[1,5,6,13],[170],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2861 : RecordDataValid section14Catalog 1 (⟨142,(3),[1,5,6,13],[170],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2862 : RecordDataValid section14Catalog 1 (⟨142,(4),[1,5,6,13],[170],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2863 : RecordDataValid section14Catalog 1 (⟨142,(5),[1,5,6,13],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2864 : RecordDataValid section14Catalog 1 (⟨142,(6),[1,5,6,13],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2865 : RecordDataValid section14Catalog 1 (⟨142,(7),[1,5,6,13],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2866 : RecordDataValid section14Catalog 1 (⟨142,(8),[1,5,6,13],[170],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2867 : RecordDataValid section14Catalog 1 (⟨142,(9),[1,5,6,13],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2868 : RecordDataValid section14Catalog 1 (⟨142,(10),[1,5,6,13],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2869 : RecordDataValid section14Catalog 1 (⟨142,(11),[1,5,6,13],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2870 : RecordDataValid section14Catalog 1 (⟨142,(12),[1,5,6,13],[170],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2871 : RecordDataValid section14Catalog 1 (⟨142,(13),[1,5,6,13],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2872 : RecordDataValid section14Catalog 1 (⟨142,(14),[1,5,6,13],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2873 : RecordDataValid section14Catalog 1 (⟨142,(15),[1,5,6,13],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2874 : RecordDataValid section14Catalog 1 (⟨143,(0),[1,5,6,13],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2875 : RecordDataValid section14Catalog 1 (⟨143,(1),[1,5,6,13],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2876 : RecordDataValid section14Catalog 1 (⟨143,(2),[1,5,6,13],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2877 : RecordDataValid section14Catalog 1 (⟨143,(3),[1,5,6,13],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2878 : RecordDataValid section14Catalog 1 (⟨143,(4),[1,5,6,13],[170],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2879 : RecordDataValid section14Catalog 1 (⟨143,(5),[1,5,6,13],[170],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2848_2880 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2848).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2848).take 32 = [⟨139,(18),[1,5,6,13],[170],557⟩,⟨139,(19),[1,5,6,13],[170],558⟩,⟨140,(0),[1,5,6,13],[170],563⟩,⟨140,(1),[1,5,6,13],[170],564⟩,⟨140,(2),[1,5,6,13],[170],565⟩,⟨140,(3),[1,6,13],[170],547⟩,⟨140,(4),[1,5,6,13],[170],566⟩,⟨140,(5),[1,5,6,13],[170],564⟩,⟨140,(6),[1,5,6,13],[170],567⟩,⟨140,(7),[1,5,6,13],[170],547⟩,⟨142,(0),[1,5,6,13],[170],568⟩,⟨142,(1),[1,5,6,13],[170],569⟩,⟨142,(2),[1,5,6,13],[170],570⟩,⟨142,(3),[1,5,6,13],[170],571⟩,⟨142,(4),[1,5,6,13],[170],572⟩,⟨142,(5),[1,5,6,13],[170],573⟩,⟨142,(6),[1,5,6,13],[170],573⟩,⟨142,(7),[1,5,6,13],[170],573⟩,⟨142,(8),[1,5,6,13],[170],574⟩,⟨142,(9),[1,5,6,13],[170],575⟩,⟨142,(10),[1,5,6,13],[170],575⟩,⟨142,(11),[1,5,6,13],[170],575⟩,⟨142,(12),[1,5,6,13],[170],576⟩,⟨142,(13),[1,5,6,13],[170],577⟩,⟨142,(14),[1,5,6,13],[170],577⟩,⟨142,(15),[1,5,6,13],[170],577⟩,⟨143,(0),[1,5,6,13],[170],578⟩,⟨143,(1),[1,5,6,13],[170],579⟩,⟨143,(2),[1,5,6,13],[170],580⟩,⟨143,(3),[1,5,6,13],[170],581⟩,⟨143,(4),[1,5,6,13],[170],582⟩,⟨143,(5),[1,5,6,13],[170],583⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2848
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2849
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2850
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2851
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2852
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2853
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2854
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2855
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2856
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2857
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2858
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2859
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2860
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2861
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2862
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2863
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2864
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2865
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2866
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2867
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2868
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2869
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2870
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2871
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2872
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2873
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2874
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2875
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2876
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2877
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2878
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2879
end Section14Records_1_2848_2880

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2848_2880

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2816).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 2816 2848 2880 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2816_2848 hnum) (Freiman.workReverse20260919_s0001_records_2848_2880 hnum))

#print axioms solution
