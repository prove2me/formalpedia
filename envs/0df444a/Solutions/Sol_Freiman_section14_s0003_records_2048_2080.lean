-- Prove2me | solution 1 for Freiman.section14_s0003_records_2048_2080
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:30:36.521929+00:00
-- url     : https://prove2.me/submissions/94b2e212-4fff-446a-9e14-6e716cbc513c

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
namespace Section14Records_3_2048_2080
private theorem valid2048 : RecordDataValid section14Catalog 3 (⟨343,(6),[3],[11],225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨225,[1,2,3,4],225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2049 : RecordDataValid section14Catalog 3 (⟨343,(6),[3,7],[8],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2050 : RecordDataValid section14Catalog 3 (⟨343,(6),[3,7],[9],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2051 : RecordDataValid section14Catalog 3 (⟨343,(7),[3],[11],229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨229,[1,2,3],229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2052 : RecordDataValid section14Catalog 3 (⟨343,(7),[3,7],[8],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2053 : RecordDataValid section14Catalog 3 (⟨343,(7),[3,7],[9],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2054 : RecordDataValid section14Catalog 3 (⟨343,(8),[3],[11],225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨225,[1,2,3,4],225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2055 : RecordDataValid section14Catalog 3 (⟨343,(8),[3,7],[8],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2056 : RecordDataValid section14Catalog 3 (⟨343,(8),[3,7],[9],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2057 : RecordDataValid section14Catalog 3 (⟨343,(9),[3],[11],227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨227,[1,2,3],227⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2058 : RecordDataValid section14Catalog 3 (⟨343,(9),[3,7],[8],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2059 : RecordDataValid section14Catalog 3 (⟨343,(9),[3,7],[9],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2060 : RecordDataValid section14Catalog 3 (⟨347,(0),[3,15],[8,9,11],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2061 : RecordDataValid section14Catalog 3 (⟨347,(1),[3,7,15],[8,9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2062 : RecordDataValid section14Catalog 3 (⟨347,(1),[3,15],[11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2063 : RecordDataValid section14Catalog 3 (⟨347,(2),[3,7,15],[8,9],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2064 : RecordDataValid section14Catalog 3 (⟨347,(2),[3,15],[11],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2065 : RecordDataValid section14Catalog 3 (⟨347,(3),[3,7,15],[8,9],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2066 : RecordDataValid section14Catalog 3 (⟨347,(3),[3,15],[11],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2067 : RecordDataValid section14Catalog 3 (⟨349,(0),[3],[11],235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨235,[1,2,3],235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2068 : RecordDataValid section14Catalog 3 (⟨349,(0),[3,7],[8],121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨121,[1,2,3,5,6,7,9,10,11],121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2069 : RecordDataValid section14Catalog 3 (⟨349,(0),[3,7],[9],139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨139,[1,2,3,5,6,7],139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2070 : RecordDataValid section14Catalog 3 (⟨349,(1),[3],[11],236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨236,[1,2,3],236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2071 : RecordDataValid section14Catalog 3 (⟨349,(1),[3,7],[8],122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨122,[1,2,3,5,6,7,9,10,11],122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2072 : RecordDataValid section14Catalog 3 (⟨349,(1),[3,7],[9],140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨140,[1,2,3,5,6,7],140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2073 : RecordDataValid section14Catalog 3 (⟨349,(2),[3],[11],933⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨933,[3],937⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2074 : RecordDataValid section14Catalog 3 (⟨349,(2),[3,7],[8],931⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨931,[3,7,11],935⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2075 : RecordDataValid section14Catalog 3 (⟨349,(2),[3,7],[9],932⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨932,[3,7],936⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2076 : RecordDataValid section14Catalog 3 (⟨349,(3),[3],[11],238⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨238,[1,2,3],238⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2077 : RecordDataValid section14Catalog 3 (⟨349,(3),[3,7],[8],124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨124,[1,2,3,5,6,7,9,10,11],124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2078 : RecordDataValid section14Catalog 3 (⟨349,(3),[3,7],[9],142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨142,[1,2,3,5,6,7],142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2079 : RecordDataValid section14Catalog 3 (⟨352,(0),[3,7,15],[10,11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2048).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2048).take 32 = [⟨343,(6),[3],[11],225⟩,⟨343,(6),[3,7],[8],115⟩,⟨343,(6),[3,7],[9],134⟩,⟨343,(7),[3],[11],229⟩,⟨343,(7),[3,7],[8],119⟩,⟨343,(7),[3,7],[9],138⟩,⟨343,(8),[3],[11],225⟩,⟨343,(8),[3,7],[8],115⟩,⟨343,(8),[3,7],[9],134⟩,⟨343,(9),[3],[11],227⟩,⟨343,(9),[3,7],[8],117⟩,⟨343,(9),[3,7],[9],136⟩,⟨347,(0),[3,15],[8,9,11],159⟩,⟨347,(1),[3,7,15],[8,9],2⟩,⟨347,(1),[3,15],[11],2⟩,⟨347,(2),[3,7,15],[8,9],159⟩,⟨347,(2),[3,15],[11],159⟩,⟨347,(3),[3,7,15],[8,9],99⟩,⟨347,(3),[3,15],[11],99⟩,⟨349,(0),[3],[11],235⟩,⟨349,(0),[3,7],[8],121⟩,⟨349,(0),[3,7],[9],139⟩,⟨349,(1),[3],[11],236⟩,⟨349,(1),[3,7],[8],122⟩,⟨349,(1),[3,7],[9],140⟩,⟨349,(2),[3],[11],933⟩,⟨349,(2),[3,7],[8],931⟩,⟨349,(2),[3,7],[9],932⟩,⟨349,(3),[3],[11],238⟩,⟨349,(3),[3,7],[8],124⟩,⟨349,(3),[3,7],[9],142⟩,⟨352,(0),[3,7,15],[10,11],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2048
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2049
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2050
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2051
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2052
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2053
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2054
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2055
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2056
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2057
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2058
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2059
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2060
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2061
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2062
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2063
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2064
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2065
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2066
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2067
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2068
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2069
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2070
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2071
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2072
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2073
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2074
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2075
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2076
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2077
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2078
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2079
end Section14Records_3_2048_2080

#print axioms solution
