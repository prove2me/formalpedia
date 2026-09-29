-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_1856_1888
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:17:36.537143+00:00
-- url     : https://prove2.me/submissions/97359f20-bf4b-4143-8ec3-e598aba69faf

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
namespace Section14Records_13_1856_1888
private theorem valid1856 : RecordDataValid section14Catalog 13 (⟨139,(7),[1,5,6,13],[170],554⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨554,[1,4,5,6,9,10,13,16],555⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1857 : RecordDataValid section14Catalog 13 (⟨139,(8),[1,5,6,13],[170],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1858 : RecordDataValid section14Catalog 13 (⟨139,(9),[1,5,6,13],[170],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1859 : RecordDataValid section14Catalog 13 (⟨139,(10),[1,5,6,13],[170],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1860 : RecordDataValid section14Catalog 13 (⟨139,(11),[1,5,6,13],[170],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1861 : RecordDataValid section14Catalog 13 (⟨139,(12),[1,5,6,13],[170],559⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨559,[1,4,5,6,8,9,10,12,13,16],560⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1862 : RecordDataValid section14Catalog 13 (⟨139,(13),[1,5,6,13],[170],560⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨560,[1,4,5,6,8,9,10,12,13,16],561⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1863 : RecordDataValid section14Catalog 13 (⟨139,(14),[1,5,6,13],[170],561⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨561,[1,4,5,6,8,9,10,12,13,16],562⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1864 : RecordDataValid section14Catalog 13 (⟨139,(15),[1,5,6,13],[170],562⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨562,[1,4,5,6,8,9,10,12,13,16],563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1865 : RecordDataValid section14Catalog 13 (⟨139,(16),[1,5,6,13],[170],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1866 : RecordDataValid section14Catalog 13 (⟨139,(17),[1,5,6,13],[170],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1867 : RecordDataValid section14Catalog 13 (⟨139,(18),[1,5,6,13],[170],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1868 : RecordDataValid section14Catalog 13 (⟨139,(19),[1,5,6,13],[170],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1869 : RecordDataValid section14Catalog 13 (⟨140,(0),[1,5,6,13],[170],563⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨563,[1,4,5,6,8,9,10,12,13,16],564⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1870 : RecordDataValid section14Catalog 13 (⟨140,(1),[1,5,6,13],[170],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1871 : RecordDataValid section14Catalog 13 (⟨140,(2),[1,5,6,13],[170],565⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨565,[1,4,5,6,8,9,10,12,13,16],566⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1872 : RecordDataValid section14Catalog 13 (⟨140,(3),[1,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1873 : RecordDataValid section14Catalog 13 (⟨140,(4),[1,5,6,13],[170],566⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨566,[1,4,5,6,8,9,10,12,13,16],567⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1874 : RecordDataValid section14Catalog 13 (⟨140,(5),[1,5,6,13],[170],564⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨564,[1,4,5,6,8,9,10,12,13,16],565⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1875 : RecordDataValid section14Catalog 13 (⟨140,(6),[1,5,6,13],[170],567⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨567,[1,4,5,6,10,13,16],568⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1876 : RecordDataValid section14Catalog 13 (⟨140,(7),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1877 : RecordDataValid section14Catalog 13 (⟨142,(0),[1,5,6,13],[170],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1878 : RecordDataValid section14Catalog 13 (⟨142,(1),[1,5,6,13],[170],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1879 : RecordDataValid section14Catalog 13 (⟨142,(2),[1,5,6,13],[170],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1880 : RecordDataValid section14Catalog 13 (⟨142,(3),[1,5,6,13],[170],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1881 : RecordDataValid section14Catalog 13 (⟨142,(4),[1,5,6,13],[170],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1882 : RecordDataValid section14Catalog 13 (⟨142,(5),[1,5,6,13],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1883 : RecordDataValid section14Catalog 13 (⟨142,(6),[1,5,6,13],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1884 : RecordDataValid section14Catalog 13 (⟨142,(7),[1,5,6,13],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1885 : RecordDataValid section14Catalog 13 (⟨142,(8),[1,5,6,13],[170],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1886 : RecordDataValid section14Catalog 13 (⟨142,(9),[1,5,6,13],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1887 : RecordDataValid section14Catalog 13 (⟨142,(10),[1,5,6,13],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1856).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1856).take 32 = [⟨139,(7),[1,5,6,13],[170],554⟩,⟨139,(8),[1,5,6,13],[170],555⟩,⟨139,(9),[1,5,6,13],[170],556⟩,⟨139,(10),[1,5,6,13],[170],557⟩,⟨139,(11),[1,5,6,13],[170],558⟩,⟨139,(12),[1,5,6,13],[170],559⟩,⟨139,(13),[1,5,6,13],[170],560⟩,⟨139,(14),[1,5,6,13],[170],561⟩,⟨139,(15),[1,5,6,13],[170],562⟩,⟨139,(16),[1,5,6,13],[170],555⟩,⟨139,(17),[1,5,6,13],[170],556⟩,⟨139,(18),[1,5,6,13],[170],557⟩,⟨139,(19),[1,5,6,13],[170],558⟩,⟨140,(0),[1,5,6,13],[170],563⟩,⟨140,(1),[1,5,6,13],[170],564⟩,⟨140,(2),[1,5,6,13],[170],565⟩,⟨140,(3),[1,6,13],[170],547⟩,⟨140,(4),[1,5,6,13],[170],566⟩,⟨140,(5),[1,5,6,13],[170],564⟩,⟨140,(6),[1,5,6,13],[170],567⟩,⟨140,(7),[1,5,6,13],[170],547⟩,⟨142,(0),[1,5,6,13],[170],568⟩,⟨142,(1),[1,5,6,13],[170],569⟩,⟨142,(2),[1,5,6,13],[170],570⟩,⟨142,(3),[1,5,6,13],[170],571⟩,⟨142,(4),[1,5,6,13],[170],572⟩,⟨142,(5),[1,5,6,13],[170],573⟩,⟨142,(6),[1,5,6,13],[170],573⟩,⟨142,(7),[1,5,6,13],[170],573⟩,⟨142,(8),[1,5,6,13],[170],574⟩,⟨142,(9),[1,5,6,13],[170],575⟩,⟨142,(10),[1,5,6,13],[170],575⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1856
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1857
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1858
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1859
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1860
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1861
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1862
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1863
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1864
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1865
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1866
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1867
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1868
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1869
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1870
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1871
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1872
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1873
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1874
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1875
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1876
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1877
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1878
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1879
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1880
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1881
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1882
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1883
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1884
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1885
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1886
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1887
end Section14Records_13_1856_1888

#print axioms solution
