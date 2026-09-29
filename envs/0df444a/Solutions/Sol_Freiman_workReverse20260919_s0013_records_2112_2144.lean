-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2112_2144
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:19:19.465155+00:00
-- url     : https://prove2.me/submissions/40130cb3-53f6-4fd7-aadd-69fda0f11141

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
namespace Section14Records_13_2112_2144
private theorem valid2112 : RecordDataValid section14Catalog 13 (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2113 : RecordDataValid section14Catalog 13 (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2114 : RecordDataValid section14Catalog 13 (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2115 : RecordDataValid section14Catalog 13 (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2116 : RecordDataValid section14Catalog 13 (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2117 : RecordDataValid section14Catalog 13 (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2118 : RecordDataValid section14Catalog 13 (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2119 : RecordDataValid section14Catalog 13 (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2120 : RecordDataValid section14Catalog 13 (⟨175,(9),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2121 : RecordDataValid section14Catalog 13 (⟨175,(10),[1,2,5,6,13,14],[170],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2122 : RecordDataValid section14Catalog 13 (⟨175,(11),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2123 : RecordDataValid section14Catalog 13 (⟨175,(12),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2124 : RecordDataValid section14Catalog 13 (⟨175,(13),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2125 : RecordDataValid section14Catalog 13 (⟨175,(14),[1,2,5,6,13,14],[170],659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨659,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],660⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2126 : RecordDataValid section14Catalog 13 (⟨175,(15),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2127 : RecordDataValid section14Catalog 13 (⟨178,(0),[1,2,5,6,13,14],[170],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2128 : RecordDataValid section14Catalog 13 (⟨178,(1),[1,2,5,6,13,14],[170],661⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨661,[1,2,3,5,6,7,10,11,13,14,15],662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2129 : RecordDataValid section14Catalog 13 (⟨178,(2),[1,2,5,6,13,14],[170],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2130 : RecordDataValid section14Catalog 13 (⟨178,(3),[1,2,5,6,13,14],[170],662⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨662,[1,2,3,5,6,7,10,11,13,14,15],663⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2131 : RecordDataValid section14Catalog 13 (⟨178,(4),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2132 : RecordDataValid section14Catalog 13 (⟨178,(5),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2133 : RecordDataValid section14Catalog 13 (⟨178,(6),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2134 : RecordDataValid section14Catalog 13 (⟨178,(7),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2135 : RecordDataValid section14Catalog 13 (⟨178,(8),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2136 : RecordDataValid section14Catalog 13 (⟨178,(9),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2137 : RecordDataValid section14Catalog 13 (⟨178,(10),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2138 : RecordDataValid section14Catalog 13 (⟨178,(11),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2139 : RecordDataValid section14Catalog 13 (⟨178,(12),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2140 : RecordDataValid section14Catalog 13 (⟨178,(13),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2141 : RecordDataValid section14Catalog 13 (⟨178,(14),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2142 : RecordDataValid section14Catalog 13 (⟨178,(15),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2143 : RecordDataValid section14Catalog 13 (⟨180,(0),[1,2,5,6,13,14],[170],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2112).take 32 = [⟨175,(1),[1,2,5,6,13,14],[170],655⟩,⟨175,(2),[1,2,5,6,13,14],[170],656⟩,⟨175,(3),[1,2,5,6,13,14],[170],657⟩,⟨175,(4),[1,2,5,6,13,14],[170],654⟩,⟨175,(5),[1,2,5,6,13,14],[170],655⟩,⟨175,(6),[1,2,5,6,13,14],[170],658⟩,⟨175,(7),[1,2,5,6,13,14],[170],657⟩,⟨175,(8),[1,2,5,6,13,14],[170],654⟩,⟨175,(9),[1,2,5,6,13,14],[170],655⟩,⟨175,(10),[1,2,5,6,13,14],[170],656⟩,⟨175,(11),[1,2,5,6,13,14],[170],657⟩,⟨175,(12),[1,2,5,6,13,14],[170],654⟩,⟨175,(13),[1,2,5,6,13,14],[170],655⟩,⟨175,(14),[1,2,5,6,13,14],[170],659⟩,⟨175,(15),[1,2,5,6,13,14],[170],657⟩,⟨178,(0),[1,2,5,6,13,14],[170],660⟩,⟨178,(1),[1,2,5,6,13,14],[170],661⟩,⟨178,(2),[1,2,5,6,13,14],[170],660⟩,⟨178,(3),[1,2,5,6,13,14],[170],662⟩,⟨178,(4),[1,2,5,6,13,14],[170],663⟩,⟨178,(5),[1,2,5,6,13,14],[170],663⟩,⟨178,(6),[1,2,5,6,13,14],[170],663⟩,⟨178,(7),[1,2,5,6,13,14],[170],663⟩,⟨178,(8),[1,2,5,6,13,14],[170],664⟩,⟨178,(9),[1,2,5,6,13,14],[170],664⟩,⟨178,(10),[1,2,5,6,13,14],[170],664⟩,⟨178,(11),[1,2,5,6,13,14],[170],664⟩,⟨178,(12),[1,2,5,6,13,14],[170],665⟩,⟨178,(13),[1,2,5,6,13,14],[170],665⟩,⟨178,(14),[1,2,5,6,13,14],[170],665⟩,⟨178,(15),[1,2,5,6,13,14],[170],665⟩,⟨180,(0),[1,2,5,6,13,14],[170],666⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2112
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2113
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2114
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2115
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2116
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2117
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2118
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2119
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2120
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2121
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2122
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2123
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2124
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2125
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2126
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2127
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2128
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2129
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2130
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2131
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2132
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2133
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2134
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2135
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2136
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2137
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2138
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2139
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2140
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2141
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2142
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2143
end Section14Records_13_2112_2144

#print axioms solution
