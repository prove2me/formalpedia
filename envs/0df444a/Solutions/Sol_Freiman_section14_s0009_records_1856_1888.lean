-- Prove2me | solution 1 for Freiman.section14_s0009_records_1856_1888
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:04:33.978883+00:00
-- url     : https://prove2.me/submissions/d981ae39-36c5-494c-acc3-329b9a9734e0

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
namespace Section14Records_9_1856_1888
private theorem valid1856 : RecordDataValid section14Catalog 9 (⟨200,(16),[9,10],[42],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1857 : RecordDataValid section14Catalog 9 (⟨200,(17),[9,10],[42],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1858 : RecordDataValid section14Catalog 9 (⟨200,(18),[9,10],[42],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1859 : RecordDataValid section14Catalog 9 (⟨200,(19),[9,10],[42],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1860 : RecordDataValid section14Catalog 9 (⟨200,(20),[9,10],[42],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1861 : RecordDataValid section14Catalog 9 (⟨200,(21),[9,10],[42],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1862 : RecordDataValid section14Catalog 9 (⟨200,(22),[9,10],[42],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1863 : RecordDataValid section14Catalog 9 (⟨200,(23),[9,10],[42],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1864 : RecordDataValid section14Catalog 9 (⟨200,(24),[9,10],[42],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1865 : RecordDataValid section14Catalog 9 (⟨202,(0),[9],[42],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1866 : RecordDataValid section14Catalog 9 (⟨202,(1),[9],[42],1330⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1330,[4,8,9,12,16],1334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1867 : RecordDataValid section14Catalog 9 (⟨202,(2),[9],[42],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1868 : RecordDataValid section14Catalog 9 (⟨202,(3),[9],[42],1331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1331,[4,8,9,12,16],1335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1869 : RecordDataValid section14Catalog 9 (⟨202,(4),[9],[42],1332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1332,[4,8,9,12,16],1336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1870 : RecordDataValid section14Catalog 9 (⟨202,(5),[9],[42],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1871 : RecordDataValid section14Catalog 9 (⟨202,(6),[9],[42],1330⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1330,[4,8,9,12,16],1334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1872 : RecordDataValid section14Catalog 9 (⟨202,(7),[9],[42],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1873 : RecordDataValid section14Catalog 9 (⟨202,(8),[9],[42],1331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1331,[4,8,9,12,16],1335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1874 : RecordDataValid section14Catalog 9 (⟨202,(9),[9],[42],1332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1332,[4,8,9,12,16],1336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1875 : RecordDataValid section14Catalog 9 (⟨202,(10),[9],[42],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1876 : RecordDataValid section14Catalog 9 (⟨202,(11),[9],[42],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1877 : RecordDataValid section14Catalog 9 (⟨202,(12),[9],[42],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1878 : RecordDataValid section14Catalog 9 (⟨202,(13),[9],[42],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1879 : RecordDataValid section14Catalog 9 (⟨202,(14),[9],[42],1332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1332,[4,8,9,12,16],1336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1880 : RecordDataValid section14Catalog 9 (⟨202,(15),[9],[42],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1881 : RecordDataValid section14Catalog 9 (⟨202,(16),[9],[42],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1882 : RecordDataValid section14Catalog 9 (⟨202,(17),[9],[42],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1883 : RecordDataValid section14Catalog 9 (⟨202,(18),[9],[42],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1884 : RecordDataValid section14Catalog 9 (⟨202,(19),[9],[42],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1885 : RecordDataValid section14Catalog 9 (⟨202,(20),[9],[42],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1886 : RecordDataValid section14Catalog 9 (⟨202,(21),[9],[42],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1887 : RecordDataValid section14Catalog 9 (⟨202,(22),[9],[42],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1856).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1856).take 32 = [⟨200,(16),[9,10],[42],710⟩,⟨200,(17),[9,10],[42],710⟩,⟨200,(18),[9,10],[42],710⟩,⟨200,(19),[9,10],[42],710⟩,⟨200,(20),[9,10],[42],706⟩,⟨200,(21),[9,10],[42],707⟩,⟨200,(22),[9,10],[42],708⟩,⟨200,(23),[9,10],[42],707⟩,⟨200,(24),[9,10],[42],709⟩,⟨202,(0),[9],[42],1329⟩,⟨202,(1),[9],[42],1330⟩,⟨202,(2),[9],[42],1329⟩,⟨202,(3),[9],[42],1331⟩,⟨202,(4),[9],[42],1332⟩,⟨202,(5),[9],[42],1329⟩,⟨202,(6),[9],[42],1330⟩,⟨202,(7),[9],[42],1329⟩,⟨202,(8),[9],[42],1331⟩,⟨202,(9),[9],[42],1332⟩,⟨202,(10),[9],[42],1333⟩,⟨202,(11),[9],[42],1333⟩,⟨202,(12),[9],[42],1333⟩,⟨202,(13),[9],[42],1333⟩,⟨202,(14),[9],[42],1332⟩,⟨202,(15),[9],[42],1334⟩,⟨202,(16),[9],[42],1334⟩,⟨202,(17),[9],[42],1334⟩,⟨202,(18),[9],[42],1334⟩,⟨202,(19),[9],[42],1334⟩,⟨202,(20),[9],[42],1335⟩,⟨202,(21),[9],[42],1335⟩,⟨202,(22),[9],[42],1335⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1856
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1857
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1858
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1859
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1860
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1861
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1862
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1863
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1864
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1865
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1866
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1867
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1868
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1869
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1870
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1871
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1872
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1873
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1874
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1875
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1876
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1877
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1878
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1879
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1880
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1881
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1882
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1883
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1884
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1885
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1886
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1887
end Section14Records_9_1856_1888

#print axioms solution
