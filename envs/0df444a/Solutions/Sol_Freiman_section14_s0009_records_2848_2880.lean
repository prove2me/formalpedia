-- Prove2me | solution 1 for Freiman.section14_s0009_records_2848_2880
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:53:41.939482+00:00
-- url     : https://prove2.me/submissions/01fc9861-920a-4f16-9c4a-ccef21b5db66

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
namespace Section14Records_9_2848_2880
private theorem valid2848 : RecordDataValid section14Catalog 9 (⟨321,(16),[9],[42],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2849 : RecordDataValid section14Catalog 9 (⟨321,(17),[9],[42],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2850 : RecordDataValid section14Catalog 9 (⟨321,(18),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2851 : RecordDataValid section14Catalog 9 (⟨321,(19),[9],[42],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2852 : RecordDataValid section14Catalog 9 (⟨321,(20),[9],[42],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2853 : RecordDataValid section14Catalog 9 (⟨321,(21),[9],[42],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2854 : RecordDataValid section14Catalog 9 (⟨321,(22),[9],[42],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2855 : RecordDataValid section14Catalog 9 (⟨321,(23),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2856 : RecordDataValid section14Catalog 9 (⟨321,(24),[9],[42],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2857 : RecordDataValid section14Catalog 9 (⟨537,(0),[9,10],[42],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2858 : RecordDataValid section14Catalog 9 (⟨537,(1),[9,10],[42],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2859 : RecordDataValid section14Catalog 9 (⟨537,(2),[9,10],[42],1651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1651,[9,10,11,12],1656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2860 : RecordDataValid section14Catalog 9 (⟨537,(3),[9,10],[42],1652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1652,[9,10,11,12],1657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2861 : RecordDataValid section14Catalog 9 (⟨537,(4),[9,10],[42],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2862 : RecordDataValid section14Catalog 9 (⟨537,(5),[9,10],[42],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2863 : RecordDataValid section14Catalog 9 (⟨537,(6),[9,10],[42],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2864 : RecordDataValid section14Catalog 9 (⟨537,(7),[9,10],[42],1651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1651,[9,10,11,12],1656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2865 : RecordDataValid section14Catalog 9 (⟨537,(8),[9,10],[42],1652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1652,[9,10,11,12],1657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2866 : RecordDataValid section14Catalog 9 (⟨537,(9),[9,10],[42],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2867 : RecordDataValid section14Catalog 9 (⟨542,(0),[9,10],[42],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2868 : RecordDataValid section14Catalog 9 (⟨542,(1),[9,10],[42],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2869 : RecordDataValid section14Catalog 9 (⟨542,(2),[9,10],[42],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2870 : RecordDataValid section14Catalog 9 (⟨542,(3),[9,10],[42],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2871 : RecordDataValid section14Catalog 9 (⟨542,(4),[9,10],[42],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2872 : RecordDataValid section14Catalog 9 (⟨542,(5),[9,10],[42],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2873 : RecordDataValid section14Catalog 9 (⟨542,(6),[9,10],[42],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2874 : RecordDataValid section14Catalog 9 (⟨542,(7),[9,10],[42],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2875 : RecordDataValid section14Catalog 9 (⟨542,(8),[9,10],[42],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2876 : RecordDataValid section14Catalog 9 (⟨542,(9),[9,10],[42],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2877 : RecordDataValid section14Catalog 9 (⟨547,(0),[9,10],[34,35,38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2878 : RecordDataValid section14Catalog 9 (⟨547,(1),[9,10],[34,35,38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2879 : RecordDataValid section14Catalog 9 (⟨547,(2),[9,10],[34,35,38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2848).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2848).take 32 = [⟨321,(16),[9],[42],626⟩,⟨321,(17),[9],[42],286⟩,⟨321,(18),[9],[42],101⟩,⟨321,(19),[9],[42],286⟩,⟨321,(20),[9],[42],882⟩,⟨321,(21),[9],[42],1497⟩,⟨321,(22),[9],[42],1512⟩,⟨321,(23),[9],[42],101⟩,⟨321,(24),[9],[42],1512⟩,⟨537,(0),[9,10],[42],1649⟩,⟨537,(1),[9,10],[42],1650⟩,⟨537,(2),[9,10],[42],1651⟩,⟨537,(3),[9,10],[42],1652⟩,⟨537,(4),[9,10],[42],17⟩,⟨537,(5),[9,10],[42],1649⟩,⟨537,(6),[9,10],[42],1650⟩,⟨537,(7),[9,10],[42],1651⟩,⟨537,(8),[9,10],[42],1652⟩,⟨537,(9),[9,10],[42],17⟩,⟨542,(0),[9,10],[42],46⟩,⟨542,(1),[9,10],[42],46⟩,⟨542,(2),[9,10],[42],42⟩,⟨542,(3),[9,10],[42],43⟩,⟨542,(4),[9,10],[42],44⟩,⟨542,(5),[9,10],[42],47⟩,⟨542,(6),[9,10],[42],47⟩,⟨542,(7),[9,10],[42],47⟩,⟨542,(8),[9,10],[42],43⟩,⟨542,(9),[9,10],[42],44⟩,⟨547,(0),[9,10],[34,35,38],3⟩,⟨547,(1),[9,10],[34,35,38],3⟩,⟨547,(2),[9,10],[34,35,38],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2848
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2849
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2850
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2851
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2852
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2853
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2854
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2855
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2856
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2857
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2858
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2859
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2860
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2861
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2862
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2863
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2864
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2865
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2866
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2867
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2868
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2869
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2870
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2871
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2872
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2873
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2874
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2875
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2876
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2877
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2878
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2879
end Section14Records_9_2848_2880

#print axioms solution
