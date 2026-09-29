-- Prove2me | solution 1 for Freiman.section14_s0003_records_0224_0256
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T12:20:13.528362+00:00
-- url     : https://prove2.me/submissions/affba3e8-f188-4979-95c2-f2aaa06417cb

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
namespace Section14Records_3_224_256
private theorem valid224 : RecordDataValid section14Catalog 3 (⟨30,(7),[3],[9],203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨203,[1,2,3,4],203⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid225 : RecordDataValid section14Catalog 3 (⟨30,(7),[3],[11],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid226 : RecordDataValid section14Catalog 3 (⟨30,(7),[3,7],[8],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid227 : RecordDataValid section14Catalog 3 (⟨30,(8),[3],[9],204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨204,[1,2,3,4,7],204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid228 : RecordDataValid section14Catalog 3 (⟨30,(8),[3],[11],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid229 : RecordDataValid section14Catalog 3 (⟨30,(8),[3,7],[8],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid230 : RecordDataValid section14Catalog 3 (⟨30,(9),[3],[9],204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨204,[1,2,3,4,7],204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid231 : RecordDataValid section14Catalog 3 (⟨30,(9),[3],[11],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid232 : RecordDataValid section14Catalog 3 (⟨30,(9),[3,7],[8],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid233 : RecordDataValid section14Catalog 3 (⟨36,(5),[3,7,15],[8,9],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid234 : RecordDataValid section14Catalog 3 (⟨36,(5),[3,15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid235 : RecordDataValid section14Catalog 3 (⟨36,(7),[3,7,15],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid236 : RecordDataValid section14Catalog 3 (⟨36,(7),[3,15],[8,11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid237 : RecordDataValid section14Catalog 3 (⟨36,(8),[3,7,15],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid238 : RecordDataValid section14Catalog 3 (⟨36,(8),[3,15],[8,11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid239 : RecordDataValid section14Catalog 3 (⟨36,(9),[3],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid240 : RecordDataValid section14Catalog 3 (⟨36,(9),[3,7],[8],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid241 : RecordDataValid section14Catalog 3 (⟨36,(9),[3,7,15],[9],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid242 : RecordDataValid section14Catalog 3 (⟨36,(15),[3,7,15],[8],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid243 : RecordDataValid section14Catalog 3 (⟨36,(15),[3,15],[9,11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid244 : RecordDataValid section14Catalog 3 (⟨36,(16),[3,7,15],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid245 : RecordDataValid section14Catalog 3 (⟨36,(16),[3,15],[8,11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid246 : RecordDataValid section14Catalog 3 (⟨36,(17),[3,15],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid247 : RecordDataValid section14Catalog 3 (⟨36,(17),[3,15],[11],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid248 : RecordDataValid section14Catalog 3 (⟨36,(19),[3],[8,9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid249 : RecordDataValid section14Catalog 3 (⟨36,(19),[3,15],[11],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid250 : RecordDataValid section14Catalog 3 (⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid251 : RecordDataValid section14Catalog 3 (⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid252 : RecordDataValid section14Catalog 3 (⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨248,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid253 : RecordDataValid section14Catalog 3 (⟨38,(-1),[3,7,15],[2],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid254 : RecordDataValid section14Catalog 3 (⟨38,(-1),[3,7,15],[6],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid255 : RecordDataValid section14Catalog 3 (⟨38,(-1),[3,7,15],[14],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 224).take 32 = [⟨30,(7),[3],[9],203⟩,⟨30,(7),[3],[11],232⟩,⟨30,(7),[3,7],[8],157⟩,⟨30,(8),[3],[9],204⟩,⟨30,(8),[3],[11],233⟩,⟨30,(8),[3,7],[8],158⟩,⟨30,(9),[3],[9],204⟩,⟨30,(9),[3],[11],233⟩,⟨30,(9),[3,7],[8],158⟩,⟨36,(5),[3,7,15],[8,9],105⟩,⟨36,(5),[3,15],[11],3⟩,⟨36,(7),[3,7,15],[9],3⟩,⟨36,(7),[3,15],[8,11],3⟩,⟨36,(8),[3,7,15],[9],3⟩,⟨36,(8),[3,15],[8,11],3⟩,⟨36,(9),[3],[11],3⟩,⟨36,(9),[3,7],[8],105⟩,⟨36,(9),[3,7,15],[9],143⟩,⟨36,(15),[3,7,15],[8],3⟩,⟨36,(15),[3,15],[9,11],3⟩,⟨36,(16),[3,7,15],[9],3⟩,⟨36,(16),[3,15],[8,11],3⟩,⟨36,(17),[3,15],[8,9],3⟩,⟨36,(17),[3,15],[11],48⟩,⟨36,(19),[3],[8,9],3⟩,⟨36,(19),[3,15],[11],143⟩,⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩,⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩,⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩,⟨38,(-1),[3,7,15],[2],60⟩,⟨38,(-1),[3,7,15],[6],68⟩,⟨38,(-1),[3,7,15],[14],243⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid224
  · exact recordValid_of_data section14Catalog 3 _ hnum valid225
  · exact recordValid_of_data section14Catalog 3 _ hnum valid226
  · exact recordValid_of_data section14Catalog 3 _ hnum valid227
  · exact recordValid_of_data section14Catalog 3 _ hnum valid228
  · exact recordValid_of_data section14Catalog 3 _ hnum valid229
  · exact recordValid_of_data section14Catalog 3 _ hnum valid230
  · exact recordValid_of_data section14Catalog 3 _ hnum valid231
  · exact recordValid_of_data section14Catalog 3 _ hnum valid232
  · exact recordValid_of_data section14Catalog 3 _ hnum valid233
  · exact recordValid_of_data section14Catalog 3 _ hnum valid234
  · exact recordValid_of_data section14Catalog 3 _ hnum valid235
  · exact recordValid_of_data section14Catalog 3 _ hnum valid236
  · exact recordValid_of_data section14Catalog 3 _ hnum valid237
  · exact recordValid_of_data section14Catalog 3 _ hnum valid238
  · exact recordValid_of_data section14Catalog 3 _ hnum valid239
  · exact recordValid_of_data section14Catalog 3 _ hnum valid240
  · exact recordValid_of_data section14Catalog 3 _ hnum valid241
  · exact recordValid_of_data section14Catalog 3 _ hnum valid242
  · exact recordValid_of_data section14Catalog 3 _ hnum valid243
  · exact recordValid_of_data section14Catalog 3 _ hnum valid244
  · exact recordValid_of_data section14Catalog 3 _ hnum valid245
  · exact recordValid_of_data section14Catalog 3 _ hnum valid246
  · exact recordValid_of_data section14Catalog 3 _ hnum valid247
  · exact recordValid_of_data section14Catalog 3 _ hnum valid248
  · exact recordValid_of_data section14Catalog 3 _ hnum valid249
  · exact recordValid_of_data section14Catalog 3 _ hnum valid250
  · exact recordValid_of_data section14Catalog 3 _ hnum valid251
  · exact recordValid_of_data section14Catalog 3 _ hnum valid252
  · exact recordValid_of_data section14Catalog 3 _ hnum valid253
  · exact recordValid_of_data section14Catalog 3 _ hnum valid254
  · exact recordValid_of_data section14Catalog 3 _ hnum valid255
end Section14Records_3_224_256

#print axioms solution
