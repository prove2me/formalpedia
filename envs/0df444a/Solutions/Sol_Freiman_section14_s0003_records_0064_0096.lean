-- Prove2me | solution 1 for Freiman.section14_s0003_records_0064_0096
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T12:14:35.001199+00:00
-- url     : https://prove2.me/submissions/75a1119a-3a4a-4dd4-9def-5f2d446cbb93

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
namespace Section14Records_3_64_96
private theorem valid64 : RecordDataValid section14Catalog 3 (⟨14,(16),[3,15],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid65 : RecordDataValid section14Catalog 3 (⟨14,(17),[3,7,15],[10],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid66 : RecordDataValid section14Catalog 3 (⟨14,(19),[3,7],[10],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid67 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,4,7,8,12,15,16],[5],66⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨66,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],66⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid68 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,11,15],[0],914⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨914,[2,3,6,7,11,14,15],917⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid69 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[1],58⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨58,[1,2,3,5,6,7,13,14,15],58⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid70 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[2],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid71 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[3],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid72 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[4],66⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨66,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],66⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid73 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[6],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid74 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[7],72⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨72,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],72⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid75 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[10],208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨208,[1,2,3,5,6,7,13,14,15],208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid76 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[13],241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨241,[1,2,3,5,6,7,13,14,15],241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid77 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[12],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid78 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[14],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid79 : RecordDataValid section14Catalog 3 (⟨16,(-1),[3,7,15],[15],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid80 : RecordDataValid section14Catalog 3 (⟨20,(0),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid81 : RecordDataValid section14Catalog 3 (⟨20,(0),[3,15],[11],209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨209,[1,2,3,4,13,14,15,16],209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid82 : RecordDataValid section14Catalog 3 (⟨20,(1),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid83 : RecordDataValid section14Catalog 3 (⟨20,(1),[3,15],[11],210⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨210,[1,2,3,4,13,14,15,16],210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid84 : RecordDataValid section14Catalog 3 (⟨20,(2),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid85 : RecordDataValid section14Catalog 3 (⟨20,(2),[3,15],[11],209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨209,[1,2,3,4,13,14,15,16],209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid86 : RecordDataValid section14Catalog 3 (⟨20,(3),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid87 : RecordDataValid section14Catalog 3 (⟨20,(3),[3,15],[11],211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨211,[1,2,3,4,13,14,15,16],211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid88 : RecordDataValid section14Catalog 3 (⟨20,(4),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid89 : RecordDataValid section14Catalog 3 (⟨20,(4),[3,15],[11],212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨212,[1,2,3,4,11,13,14,15,16],212⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid90 : RecordDataValid section14Catalog 3 (⟨20,(5),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid91 : RecordDataValid section14Catalog 3 (⟨20,(5),[3,15],[11],209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨209,[1,2,3,4,13,14,15,16],209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid92 : RecordDataValid section14Catalog 3 (⟨20,(6),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid93 : RecordDataValid section14Catalog 3 (⟨20,(6),[3,15],[11],210⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨210,[1,2,3,4,13,14,15,16],210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid94 : RecordDataValid section14Catalog 3 (⟨20,(7),[3,7,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid95 : RecordDataValid section14Catalog 3 (⟨20,(7),[3,15],[11],209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨209,[1,2,3,4,13,14,15,16],209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 64).take 32 = [⟨14,(16),[3,15],[10],3⟩,⟨14,(17),[3,7,15],[10],48⟩,⟨14,(19),[3,7],[10],48⟩,⟨16,(-1),[3,4,7,8,12,15,16],[5],66⟩,⟨16,(-1),[3,7,11,15],[0],914⟩,⟨16,(-1),[3,7,15],[1],58⟩,⟨16,(-1),[3,7,15],[2],60⟩,⟨16,(-1),[3,7,15],[3],62⟩,⟨16,(-1),[3,7,15],[4],66⟩,⟨16,(-1),[3,7,15],[6],68⟩,⟨16,(-1),[3,7,15],[7],72⟩,⟨16,(-1),[3,7,15],[10],208⟩,⟨16,(-1),[3,7,15],[13],241⟩,⟨16,(-1),[3,7,15],[12],242⟩,⟨16,(-1),[3,7,15],[14],243⟩,⟨16,(-1),[3,7,15],[15],245⟩,⟨20,(0),[3,7,15],[8,9],3⟩,⟨20,(0),[3,15],[11],209⟩,⟨20,(1),[3,7,15],[8,9],3⟩,⟨20,(1),[3,15],[11],210⟩,⟨20,(2),[3,7,15],[8,9],3⟩,⟨20,(2),[3,15],[11],209⟩,⟨20,(3),[3,7,15],[8,9],3⟩,⟨20,(3),[3,15],[11],211⟩,⟨20,(4),[3,7,15],[8,9],3⟩,⟨20,(4),[3,15],[11],212⟩,⟨20,(5),[3,7,15],[8,9],3⟩,⟨20,(5),[3,15],[11],209⟩,⟨20,(6),[3,7,15],[8,9],3⟩,⟨20,(6),[3,15],[11],210⟩,⟨20,(7),[3,7,15],[8,9],3⟩,⟨20,(7),[3,15],[11],209⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid64
  · exact recordValid_of_data section14Catalog 3 _ hnum valid65
  · exact recordValid_of_data section14Catalog 3 _ hnum valid66
  · exact recordValid_of_data section14Catalog 3 _ hnum valid67
  · exact recordValid_of_data section14Catalog 3 _ hnum valid68
  · exact recordValid_of_data section14Catalog 3 _ hnum valid69
  · exact recordValid_of_data section14Catalog 3 _ hnum valid70
  · exact recordValid_of_data section14Catalog 3 _ hnum valid71
  · exact recordValid_of_data section14Catalog 3 _ hnum valid72
  · exact recordValid_of_data section14Catalog 3 _ hnum valid73
  · exact recordValid_of_data section14Catalog 3 _ hnum valid74
  · exact recordValid_of_data section14Catalog 3 _ hnum valid75
  · exact recordValid_of_data section14Catalog 3 _ hnum valid76
  · exact recordValid_of_data section14Catalog 3 _ hnum valid77
  · exact recordValid_of_data section14Catalog 3 _ hnum valid78
  · exact recordValid_of_data section14Catalog 3 _ hnum valid79
  · exact recordValid_of_data section14Catalog 3 _ hnum valid80
  · exact recordValid_of_data section14Catalog 3 _ hnum valid81
  · exact recordValid_of_data section14Catalog 3 _ hnum valid82
  · exact recordValid_of_data section14Catalog 3 _ hnum valid83
  · exact recordValid_of_data section14Catalog 3 _ hnum valid84
  · exact recordValid_of_data section14Catalog 3 _ hnum valid85
  · exact recordValid_of_data section14Catalog 3 _ hnum valid86
  · exact recordValid_of_data section14Catalog 3 _ hnum valid87
  · exact recordValid_of_data section14Catalog 3 _ hnum valid88
  · exact recordValid_of_data section14Catalog 3 _ hnum valid89
  · exact recordValid_of_data section14Catalog 3 _ hnum valid90
  · exact recordValid_of_data section14Catalog 3 _ hnum valid91
  · exact recordValid_of_data section14Catalog 3 _ hnum valid92
  · exact recordValid_of_data section14Catalog 3 _ hnum valid93
  · exact recordValid_of_data section14Catalog 3 _ hnum valid94
  · exact recordValid_of_data section14Catalog 3 _ hnum valid95
end Section14Records_3_64_96

#print axioms solution
