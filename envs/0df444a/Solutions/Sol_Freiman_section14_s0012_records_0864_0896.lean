-- Prove2me | solution 1 for Freiman.section14_s0012_records_0864_0896
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:39:11.606495+00:00
-- url     : https://prove2.me/submissions/f9ba6f0f-bf24-497b-9b74-b89f0a24db07

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
namespace Section14Records_12_864_896
private theorem valid864 : RecordDataValid section14Catalog 12 (⟨138,(21),[4,8,12,16],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid865 : RecordDataValid section14Catalog 12 (⟨138,(22),[4,8,12,16],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid866 : RecordDataValid section14Catalog 12 (⟨138,(23),[4,8,12,16],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid867 : RecordDataValid section14Catalog 12 (⟨138,(24),[4,8,12,16],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid868 : RecordDataValid section14Catalog 12 (⟨139,(0),[4,8,12,16],[10],548⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨548,[1,4,5,6,8,9,10,12,13,16],549⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid869 : RecordDataValid section14Catalog 12 (⟨139,(1),[4,8,12,16],[10],549⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨549,[1,4,5,6,8,9,10,12,13,16],550⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid870 : RecordDataValid section14Catalog 12 (⟨139,(2),[4,8,12,16],[10],548⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨548,[1,4,5,6,8,9,10,12,13,16],549⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid871 : RecordDataValid section14Catalog 12 (⟨139,(3),[4,8,12,16],[10],550⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨550,[1,4,5,6,8,9,10,12,13,16],551⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid872 : RecordDataValid section14Catalog 12 (⟨139,(4),[4,8,12,16],[10],551⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨551,[1,4,5,6,8,9,10,12,13,16],552⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid873 : RecordDataValid section14Catalog 12 (⟨139,(5),[8,12],[10],1639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1639,[8,12],1644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid874 : RecordDataValid section14Catalog 12 (⟨139,(6),[8,12],[10],1640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1640,[8,12],1645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid875 : RecordDataValid section14Catalog 12 (⟨139,(7),[8,12],[10],1641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1641,[8,12],1646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid876 : RecordDataValid section14Catalog 12 (⟨139,(8),[4,8,12,16],[10],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid877 : RecordDataValid section14Catalog 12 (⟨139,(9),[4,8,12,16],[10],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid878 : RecordDataValid section14Catalog 12 (⟨139,(10),[4,8,12,16],[10],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid879 : RecordDataValid section14Catalog 12 (⟨139,(11),[4,8,12,16],[10],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid880 : RecordDataValid section14Catalog 12 (⟨139,(12),[4,8,12,16],[10],559⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨559,[1,4,5,6,8,9,10,12,13,16],560⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid881 : RecordDataValid section14Catalog 12 (⟨139,(13),[4,8,12,16],[10],560⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨560,[1,4,5,6,8,9,10,12,13,16],561⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid882 : RecordDataValid section14Catalog 12 (⟨139,(14),[4,8,12,16],[10],561⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨561,[1,4,5,6,8,9,10,12,13,16],562⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid883 : RecordDataValid section14Catalog 12 (⟨139,(15),[4,8,12,16],[10],562⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨562,[1,4,5,6,8,9,10,12,13,16],563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid884 : RecordDataValid section14Catalog 12 (⟨139,(16),[4,8,12,16],[10],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid885 : RecordDataValid section14Catalog 12 (⟨139,(17),[4,8,12,16],[10],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid886 : RecordDataValid section14Catalog 12 (⟨139,(18),[4,8,12,16],[10],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid887 : RecordDataValid section14Catalog 12 (⟨139,(19),[4,8,12,16],[10],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid888 : RecordDataValid section14Catalog 12 (⟨140,(0),[4,8,12,16],[10],563⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨563,[1,4,5,6,8,9,10,12,13,16],564⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid889 : RecordDataValid section14Catalog 12 (⟨140,(1),[4,8,12,16],[10],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid890 : RecordDataValid section14Catalog 12 (⟨140,(2),[4,8,12,16],[10],565⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨565,[1,4,5,6,8,9,10,12,13,16],566⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid891 : RecordDataValid section14Catalog 12 (⟨140,(3),[4,8,12,16],[10],1270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1270,[4,5,8,9,12,16],1274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid892 : RecordDataValid section14Catalog 12 (⟨140,(4),[4,8,12,16],[10],566⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨566,[1,4,5,6,8,9,10,12,13,16],567⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid893 : RecordDataValid section14Catalog 12 (⟨140,(5),[4,8,12,16],[10],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid894 : RecordDataValid section14Catalog 12 (⟨140,(6),[8,12],[10],1642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1642,[8,9,12],1647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid895 : RecordDataValid section14Catalog 12 (⟨140,(7),[8,12],[10],1643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1643,[8,12],1648⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 864).take 32 = [⟨138,(21),[4,8,12,16],[10],547⟩,⟨138,(22),[4,8,12,16],[10],547⟩,⟨138,(23),[4,8,12,16],[10],517⟩,⟨138,(24),[4,8,12,16],[10],518⟩,⟨139,(0),[4,8,12,16],[10],548⟩,⟨139,(1),[4,8,12,16],[10],549⟩,⟨139,(2),[4,8,12,16],[10],548⟩,⟨139,(3),[4,8,12,16],[10],550⟩,⟨139,(4),[4,8,12,16],[10],551⟩,⟨139,(5),[8,12],[10],1639⟩,⟨139,(6),[8,12],[10],1640⟩,⟨139,(7),[8,12],[10],1641⟩,⟨139,(8),[4,8,12,16],[10],555⟩,⟨139,(9),[4,8,12,16],[10],556⟩,⟨139,(10),[4,8,12,16],[10],557⟩,⟨139,(11),[4,8,12,16],[10],558⟩,⟨139,(12),[4,8,12,16],[10],559⟩,⟨139,(13),[4,8,12,16],[10],560⟩,⟨139,(14),[4,8,12,16],[10],561⟩,⟨139,(15),[4,8,12,16],[10],562⟩,⟨139,(16),[4,8,12,16],[10],555⟩,⟨139,(17),[4,8,12,16],[10],556⟩,⟨139,(18),[4,8,12,16],[10],557⟩,⟨139,(19),[4,8,12,16],[10],558⟩,⟨140,(0),[4,8,12,16],[10],563⟩,⟨140,(1),[4,8,12,16],[10],564⟩,⟨140,(2),[4,8,12,16],[10],565⟩,⟨140,(3),[4,8,12,16],[10],1270⟩,⟨140,(4),[4,8,12,16],[10],566⟩,⟨140,(5),[4,8,12,16],[10],564⟩,⟨140,(6),[8,12],[10],1642⟩,⟨140,(7),[8,12],[10],1643⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid864
  · exact recordValid_of_data section14Catalog 12 _ hnum valid865
  · exact recordValid_of_data section14Catalog 12 _ hnum valid866
  · exact recordValid_of_data section14Catalog 12 _ hnum valid867
  · exact recordValid_of_data section14Catalog 12 _ hnum valid868
  · exact recordValid_of_data section14Catalog 12 _ hnum valid869
  · exact recordValid_of_data section14Catalog 12 _ hnum valid870
  · exact recordValid_of_data section14Catalog 12 _ hnum valid871
  · exact recordValid_of_data section14Catalog 12 _ hnum valid872
  · exact recordValid_of_data section14Catalog 12 _ hnum valid873
  · exact recordValid_of_data section14Catalog 12 _ hnum valid874
  · exact recordValid_of_data section14Catalog 12 _ hnum valid875
  · exact recordValid_of_data section14Catalog 12 _ hnum valid876
  · exact recordValid_of_data section14Catalog 12 _ hnum valid877
  · exact recordValid_of_data section14Catalog 12 _ hnum valid878
  · exact recordValid_of_data section14Catalog 12 _ hnum valid879
  · exact recordValid_of_data section14Catalog 12 _ hnum valid880
  · exact recordValid_of_data section14Catalog 12 _ hnum valid881
  · exact recordValid_of_data section14Catalog 12 _ hnum valid882
  · exact recordValid_of_data section14Catalog 12 _ hnum valid883
  · exact recordValid_of_data section14Catalog 12 _ hnum valid884
  · exact recordValid_of_data section14Catalog 12 _ hnum valid885
  · exact recordValid_of_data section14Catalog 12 _ hnum valid886
  · exact recordValid_of_data section14Catalog 12 _ hnum valid887
  · exact recordValid_of_data section14Catalog 12 _ hnum valid888
  · exact recordValid_of_data section14Catalog 12 _ hnum valid889
  · exact recordValid_of_data section14Catalog 12 _ hnum valid890
  · exact recordValid_of_data section14Catalog 12 _ hnum valid891
  · exact recordValid_of_data section14Catalog 12 _ hnum valid892
  · exact recordValid_of_data section14Catalog 12 _ hnum valid893
  · exact recordValid_of_data section14Catalog 12 _ hnum valid894
  · exact recordValid_of_data section14Catalog 12 _ hnum valid895
end Section14Records_12_864_896

#print axioms solution
