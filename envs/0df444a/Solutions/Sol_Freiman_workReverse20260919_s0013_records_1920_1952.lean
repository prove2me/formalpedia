-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_1920_1952
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:18:34.061249+00:00
-- url     : https://prove2.me/submissions/3a2c1cba-489a-46b4-8293-be86b7b1d293

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
namespace Section14Records_13_1920_1952
private theorem valid1920 : RecordDataValid section14Catalog 13 (⟨145,(7),[1,5,6,13],[170],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1921 : RecordDataValid section14Catalog 13 (⟨145,(8),[1,5,6,13],[170],593⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨593,[1,4,5,6,8,9,10,12,13,16],594⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1922 : RecordDataValid section14Catalog 13 (⟨145,(9),[1,5,6,13],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1923 : RecordDataValid section14Catalog 13 (⟨145,(10),[1,5,6,13],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1924 : RecordDataValid section14Catalog 13 (⟨145,(11),[1,5,6,13],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1925 : RecordDataValid section14Catalog 13 (⟨145,(12),[1,5,6,13],[170],601⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨601,[1,4,5,6,8,9,10,12,13,16],602⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1926 : RecordDataValid section14Catalog 13 (⟨145,(13),[1,5,6,13],[170],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1927 : RecordDataValid section14Catalog 13 (⟨145,(14),[1,5,6,13],[170],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1928 : RecordDataValid section14Catalog 13 (⟨145,(15),[1,5,6,13],[170],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1929 : RecordDataValid section14Catalog 13 (⟨146,(0),[1,5,6,13],[170],605⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨605,[1,5,6,10,13],606⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1930 : RecordDataValid section14Catalog 13 (⟨146,(1),[1,5,6,13],[170],606⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨606,[1,5,6,10,13],607⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1931 : RecordDataValid section14Catalog 13 (⟨146,(2),[1,5,6,13],[170],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1932 : RecordDataValid section14Catalog 13 (⟨146,(3),[1,5,6,13],[170],608⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨608,[1,5,6,10,13],609⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1933 : RecordDataValid section14Catalog 13 (⟨146,(4),[1,5,6,13],[170],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1934 : RecordDataValid section14Catalog 13 (⟨146,(5),[1,5,6,13],[170],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1935 : RecordDataValid section14Catalog 13 (⟨146,(6),[1,5,6,13],[170],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1936 : RecordDataValid section14Catalog 13 (⟨146,(7),[1,5,6,13],[170],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1937 : RecordDataValid section14Catalog 13 (⟨146,(8),[1,5,6,13],[170],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1938 : RecordDataValid section14Catalog 13 (⟨146,(9),[1,5,6,13],[170],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1939 : RecordDataValid section14Catalog 13 (⟨146,(10),[1,5,6,13],[170],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1940 : RecordDataValid section14Catalog 13 (⟨146,(11),[1,5,6,13],[170],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1941 : RecordDataValid section14Catalog 13 (⟨146,(12),[1,5,6,13],[170],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1942 : RecordDataValid section14Catalog 13 (⟨146,(13),[1,5,6,13],[170],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1943 : RecordDataValid section14Catalog 13 (⟨146,(14),[1,5,6,13],[170],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1944 : RecordDataValid section14Catalog 13 (⟨146,(15),[1,5,6,13],[170],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1945 : RecordDataValid section14Catalog 13 (⟨151,(5),[13],[170],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1946 : RecordDataValid section14Catalog 13 (⟨151,(7),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1947 : RecordDataValid section14Catalog 13 (⟨151,(8),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1948 : RecordDataValid section14Catalog 13 (⟨151,(9),[5,6,13],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1949 : RecordDataValid section14Catalog 13 (⟨151,(15),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1950 : RecordDataValid section14Catalog 13 (⟨151,(16),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1951 : RecordDataValid section14Catalog 13 (⟨151,(17),[1,5,6,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1920).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1920).take 32 = [⟨145,(7),[1,5,6,13],[170],600⟩,⟨145,(8),[1,5,6,13],[170],593⟩,⟨145,(9),[1,5,6,13],[170],594⟩,⟨145,(10),[1,5,6,13],[170],595⟩,⟨145,(11),[1,5,6,13],[170],596⟩,⟨145,(12),[1,5,6,13],[170],601⟩,⟨145,(13),[1,5,6,13],[170],602⟩,⟨145,(14),[1,5,6,13],[170],603⟩,⟨145,(15),[1,5,6,13],[170],604⟩,⟨146,(0),[1,5,6,13],[170],605⟩,⟨146,(1),[1,5,6,13],[170],606⟩,⟨146,(2),[1,5,6,13],[170],607⟩,⟨146,(3),[1,5,6,13],[170],608⟩,⟨146,(4),[1,5,6,13],[170],609⟩,⟨146,(5),[1,5,6,13],[170],610⟩,⟨146,(6),[1,5,6,13],[170],611⟩,⟨146,(7),[1,5,6,13],[170],612⟩,⟨146,(8),[1,5,6,13],[170],613⟩,⟨146,(9),[1,5,6,13],[170],614⟩,⟨146,(10),[1,5,6,13],[170],615⟩,⟨146,(11),[1,5,6,13],[170],616⟩,⟨146,(12),[1,5,6,13],[170],617⟩,⟨146,(13),[1,5,6,13],[170],618⟩,⟨146,(14),[1,5,6,13],[170],619⟩,⟨146,(15),[1,5,6,13],[170],620⟩,⟨151,(5),[13],[170],105⟩,⟨151,(7),[1,5,6,13],[170],3⟩,⟨151,(8),[1,5,6,13],[170],3⟩,⟨151,(9),[5,6,13],[170],143⟩,⟨151,(15),[5,13],[170],48⟩,⟨151,(16),[1,5,6,13],[170],3⟩,⟨151,(17),[1,5,6,13],[170],48⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1920
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1921
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1922
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1923
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1924
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1925
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1926
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1927
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1928
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1929
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1930
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1931
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1932
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1933
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1934
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1935
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1936
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1937
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1938
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1939
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1940
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1941
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1942
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1943
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1944
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1945
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1946
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1947
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1948
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1949
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1950
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1951
end Section14Records_13_1920_1952

#print axioms solution
