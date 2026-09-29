-- Prove2me | solution 1 for Freiman.section14_s0007_records_0160_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:18:54.890399+00:00
-- url     : https://prove2.me/submissions/3c6c3d9b-a301-4bae-b893-2cfdb87feff7

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
namespace Section14Records_7_160_192
private theorem valid160 : RecordDataValid section14Catalog 7 (⟨30,(3),[3,7],[8],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid161 : RecordDataValid section14Catalog 7 (⟨30,(3),[7],[9],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid162 : RecordDataValid section14Catalog 7 (⟨30,(4),[3,7],[8],156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨156,[1,2,3,5,6,7],156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid163 : RecordDataValid section14Catalog 7 (⟨30,(4),[7],[9],231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨231,[1,2,3,4,5,6,7,8,9,10,11,12],231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid164 : RecordDataValid section14Catalog 7 (⟨30,(5),[3,7],[8],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid165 : RecordDataValid section14Catalog 7 (⟨30,(5),[7],[9],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid166 : RecordDataValid section14Catalog 7 (⟨30,(6),[3,7],[8],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid167 : RecordDataValid section14Catalog 7 (⟨30,(6),[7],[9],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid168 : RecordDataValid section14Catalog 7 (⟨30,(7),[3,7],[8],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid169 : RecordDataValid section14Catalog 7 (⟨30,(7),[7],[9],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid170 : RecordDataValid section14Catalog 7 (⟨30,(8),[3,7],[8],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid171 : RecordDataValid section14Catalog 7 (⟨30,(8),[7],[9],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid172 : RecordDataValid section14Catalog 7 (⟨30,(9),[3,7],[8],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid173 : RecordDataValid section14Catalog 7 (⟨30,(9),[7],[9],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid174 : RecordDataValid section14Catalog 7 (⟨36,(5),[3,7,15],[8,9],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid175 : RecordDataValid section14Catalog 7 (⟨36,(7),[3,7,15],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid176 : RecordDataValid section14Catalog 7 (⟨36,(7),[7],[8],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid177 : RecordDataValid section14Catalog 7 (⟨36,(8),[3,7,15],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid178 : RecordDataValid section14Catalog 7 (⟨36,(8),[7],[8],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid179 : RecordDataValid section14Catalog 7 (⟨36,(9),[3,7],[8],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid180 : RecordDataValid section14Catalog 7 (⟨36,(9),[3,7,15],[9],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid181 : RecordDataValid section14Catalog 7 (⟨36,(15),[3,7,15],[8],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid182 : RecordDataValid section14Catalog 7 (⟨36,(15),[7],[9],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid183 : RecordDataValid section14Catalog 7 (⟨36,(16),[3,7,15],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid184 : RecordDataValid section14Catalog 7 (⟨36,(16),[7],[8],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid185 : RecordDataValid section14Catalog 7 (⟨36,(17),[7],[8,9],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid186 : RecordDataValid section14Catalog 7 (⟨36,(19),[7,15],[8,9],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid187 : RecordDataValid section14Catalog 7 (⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid188 : RecordDataValid section14Catalog 7 (⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid189 : RecordDataValid section14Catalog 7 (⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨248,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid190 : RecordDataValid section14Catalog 7 (⟨38,(-1),[3,7,15],[2],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid191 : RecordDataValid section14Catalog 7 (⟨38,(-1),[3,7,15],[6],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 160).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 160).take 32 = [⟨30,(3),[3,7],[8],155⟩,⟨30,(3),[7],[9],230⟩,⟨30,(4),[3,7],[8],156⟩,⟨30,(4),[7],[9],231⟩,⟨30,(5),[3,7],[8],155⟩,⟨30,(5),[7],[9],230⟩,⟨30,(6),[3,7],[8],157⟩,⟨30,(6),[7],[9],232⟩,⟨30,(7),[3,7],[8],157⟩,⟨30,(7),[7],[9],232⟩,⟨30,(8),[3,7],[8],158⟩,⟨30,(8),[7],[9],233⟩,⟨30,(9),[3,7],[8],158⟩,⟨30,(9),[7],[9],233⟩,⟨36,(5),[3,7,15],[8,9],105⟩,⟨36,(7),[3,7,15],[9],3⟩,⟨36,(7),[7],[8],105⟩,⟨36,(8),[3,7,15],[9],3⟩,⟨36,(8),[7],[8],105⟩,⟨36,(9),[3,7],[8],105⟩,⟨36,(9),[3,7,15],[9],143⟩,⟨36,(15),[3,7,15],[8],3⟩,⟨36,(15),[7],[9],105⟩,⟨36,(16),[3,7,15],[9],3⟩,⟨36,(16),[7],[8],105⟩,⟨36,(17),[7],[8,9],48⟩,⟨36,(19),[7,15],[8,9],143⟩,⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩,⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩,⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩,⟨38,(-1),[3,7,15],[2],60⟩,⟨38,(-1),[3,7,15],[6],68⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid160
  · exact recordValid_of_data section14Catalog 7 _ hnum valid161
  · exact recordValid_of_data section14Catalog 7 _ hnum valid162
  · exact recordValid_of_data section14Catalog 7 _ hnum valid163
  · exact recordValid_of_data section14Catalog 7 _ hnum valid164
  · exact recordValid_of_data section14Catalog 7 _ hnum valid165
  · exact recordValid_of_data section14Catalog 7 _ hnum valid166
  · exact recordValid_of_data section14Catalog 7 _ hnum valid167
  · exact recordValid_of_data section14Catalog 7 _ hnum valid168
  · exact recordValid_of_data section14Catalog 7 _ hnum valid169
  · exact recordValid_of_data section14Catalog 7 _ hnum valid170
  · exact recordValid_of_data section14Catalog 7 _ hnum valid171
  · exact recordValid_of_data section14Catalog 7 _ hnum valid172
  · exact recordValid_of_data section14Catalog 7 _ hnum valid173
  · exact recordValid_of_data section14Catalog 7 _ hnum valid174
  · exact recordValid_of_data section14Catalog 7 _ hnum valid175
  · exact recordValid_of_data section14Catalog 7 _ hnum valid176
  · exact recordValid_of_data section14Catalog 7 _ hnum valid177
  · exact recordValid_of_data section14Catalog 7 _ hnum valid178
  · exact recordValid_of_data section14Catalog 7 _ hnum valid179
  · exact recordValid_of_data section14Catalog 7 _ hnum valid180
  · exact recordValid_of_data section14Catalog 7 _ hnum valid181
  · exact recordValid_of_data section14Catalog 7 _ hnum valid182
  · exact recordValid_of_data section14Catalog 7 _ hnum valid183
  · exact recordValid_of_data section14Catalog 7 _ hnum valid184
  · exact recordValid_of_data section14Catalog 7 _ hnum valid185
  · exact recordValid_of_data section14Catalog 7 _ hnum valid186
  · exact recordValid_of_data section14Catalog 7 _ hnum valid187
  · exact recordValid_of_data section14Catalog 7 _ hnum valid188
  · exact recordValid_of_data section14Catalog 7 _ hnum valid189
  · exact recordValid_of_data section14Catalog 7 _ hnum valid190
  · exact recordValid_of_data section14Catalog 7 _ hnum valid191
end Section14Records_7_160_192

#print axioms solution
