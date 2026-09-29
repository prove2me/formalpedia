-- Prove2me | solution 1 for Freiman.section14_s0009_records_2816_2848
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:53:39.052979+00:00
-- url     : https://prove2.me/submissions/de339ecd-d59c-4ada-90e2-386936923b2c

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
namespace Section14Records_9_2816_2848
private theorem valid2816 : RecordDataValid section14Catalog 9 (⟨319,(4),[9],[42],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2817 : RecordDataValid section14Catalog 9 (⟨319,(5),[9],[42],1232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1232,[3,5,7,8,9,11,12,15],1236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2818 : RecordDataValid section14Catalog 9 (⟨319,(6),[9],[42],1504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1504,[5,8,9,12],1509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2819 : RecordDataValid section14Catalog 9 (⟨319,(7),[9],[42],1505⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1505,[5,8,9,12],1510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2820 : RecordDataValid section14Catalog 9 (⟨319,(8),[9],[42],1235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1235,[3,5,7,8,9,11,12,15],1239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2821 : RecordDataValid section14Catalog 9 (⟨319,(9),[9],[42],1236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1236,[3,5,7,8,9,11,12,15],1240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2822 : RecordDataValid section14Catalog 9 (⟨319,(10),[9],[42],1506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1506,[5,8,9,12],1511⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2823 : RecordDataValid section14Catalog 9 (⟨319,(11),[9],[42],1507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1507,[5,8,9,12],1512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2824 : RecordDataValid section14Catalog 9 (⟨319,(12),[9],[42],1239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1239,[3,5,7,8,9,11,12,15],1243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2825 : RecordDataValid section14Catalog 9 (⟨319,(13),[9],[42],1240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1240,[3,5,7,8,9,11,12,15],1244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2826 : RecordDataValid section14Catalog 9 (⟨319,(14),[9],[42],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2827 : RecordDataValid section14Catalog 9 (⟨319,(15),[9],[42],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2828 : RecordDataValid section14Catalog 9 (⟨319,(16),[9],[42],1242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1242,[3,5,7,8,9,11,12,15],1246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2829 : RecordDataValid section14Catalog 9 (⟨319,(17),[9],[42],1243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1243,[3,5,7,8,9,11,12,15],1247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2830 : RecordDataValid section14Catalog 9 (⟨319,(18),[9],[42],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2831 : RecordDataValid section14Catalog 9 (⟨319,(19),[9],[42],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2832 : RecordDataValid section14Catalog 9 (⟨321,(0),[9],[42],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2833 : RecordDataValid section14Catalog 9 (⟨321,(1),[9],[42],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2834 : RecordDataValid section14Catalog 9 (⟨321,(2),[9],[42],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2835 : RecordDataValid section14Catalog 9 (⟨321,(3),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2836 : RecordDataValid section14Catalog 9 (⟨321,(4),[9],[42],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2837 : RecordDataValid section14Catalog 9 (⟨321,(5),[9],[42],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2838 : RecordDataValid section14Catalog 9 (⟨321,(6),[9],[42],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2839 : RecordDataValid section14Catalog 9 (⟨321,(7),[9],[42],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2840 : RecordDataValid section14Catalog 9 (⟨321,(8),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2841 : RecordDataValid section14Catalog 9 (⟨321,(9),[9],[42],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2842 : RecordDataValid section14Catalog 9 (⟨321,(10),[9],[42],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2843 : RecordDataValid section14Catalog 9 (⟨321,(11),[9],[42],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2844 : RecordDataValid section14Catalog 9 (⟨321,(12),[9],[42],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2845 : RecordDataValid section14Catalog 9 (⟨321,(13),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2846 : RecordDataValid section14Catalog 9 (⟨321,(14),[9],[42],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2847 : RecordDataValid section14Catalog 9 (⟨321,(15),[9],[42],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2816).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2816).take 32 = [⟨319,(4),[9],[42],1231⟩,⟨319,(5),[9],[42],1232⟩,⟨319,(6),[9],[42],1504⟩,⟨319,(7),[9],[42],1505⟩,⟨319,(8),[9],[42],1235⟩,⟨319,(9),[9],[42],1236⟩,⟨319,(10),[9],[42],1506⟩,⟨319,(11),[9],[42],1507⟩,⟨319,(12),[9],[42],1239⟩,⟨319,(13),[9],[42],1240⟩,⟨319,(14),[9],[42],1508⟩,⟨319,(15),[9],[42],1508⟩,⟨319,(16),[9],[42],1242⟩,⟨319,(17),[9],[42],1243⟩,⟨319,(18),[9],[42],1509⟩,⟨319,(19),[9],[42],1509⟩,⟨321,(0),[9],[42],882⟩,⟨321,(1),[9],[42],1497⟩,⟨321,(2),[9],[42],1245⟩,⟨321,(3),[9],[42],101⟩,⟨321,(4),[9],[42],1245⟩,⟨321,(5),[9],[42],882⟩,⟨321,(6),[9],[42],1497⟩,⟨321,(7),[9],[42],1510⟩,⟨321,(8),[9],[42],101⟩,⟨321,(9),[9],[42],1510⟩,⟨321,(10),[9],[42],882⟩,⟨321,(11),[9],[42],1497⟩,⟨321,(12),[9],[42],1511⟩,⟨321,(13),[9],[42],101⟩,⟨321,(14),[9],[42],1511⟩,⟨321,(15),[9],[42],625⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2816
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2817
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2818
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2819
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2820
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2821
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2822
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2823
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2824
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2825
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2826
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2827
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2828
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2829
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2830
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2831
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2832
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2833
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2834
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2835
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2836
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2837
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2838
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2839
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2840
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2841
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2842
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2843
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2844
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2845
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2846
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2847
end Section14Records_9_2816_2848

#print axioms solution
