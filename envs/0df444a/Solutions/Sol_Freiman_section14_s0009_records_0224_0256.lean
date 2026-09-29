-- Prove2me | solution 1 for Freiman.section14_s0009_records_0224_0256
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T19:58:23.394287+00:00
-- url     : https://prove2.me/submissions/d999205a-84dd-4ea4-9d75-73748af8e5f0

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
namespace Section14Records_9_224_256
private theorem valid224 : RecordDataValid section14Catalog 9 (⟨25,(5),[9,10],[35],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid225 : RecordDataValid section14Catalog 9 (⟨25,(5),[9,10],[38],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid226 : RecordDataValid section14Catalog 9 (⟨25,(6),[9,10],[34],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid227 : RecordDataValid section14Catalog 9 (⟨25,(6),[9,10],[35],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid228 : RecordDataValid section14Catalog 9 (⟨25,(6),[9,10],[38],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid229 : RecordDataValid section14Catalog 9 (⟨25,(7),[9,10],[34],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid230 : RecordDataValid section14Catalog 9 (⟨25,(7),[9,10],[35],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid231 : RecordDataValid section14Catalog 9 (⟨25,(7),[9,10],[38],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid232 : RecordDataValid section14Catalog 9 (⟨25,(8),[9,10],[34],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid233 : RecordDataValid section14Catalog 9 (⟨25,(8),[9,10],[35],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid234 : RecordDataValid section14Catalog 9 (⟨25,(8),[9,10],[38],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid235 : RecordDataValid section14Catalog 9 (⟨25,(9),[9,10],[34],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid236 : RecordDataValid section14Catalog 9 (⟨25,(9),[9,10],[35],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid237 : RecordDataValid section14Catalog 9 (⟨25,(9),[9,10],[38],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid238 : RecordDataValid section14Catalog 9 (⟨25,(10),[9,10],[34],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid239 : RecordDataValid section14Catalog 9 (⟨25,(10),[9,10],[35],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid240 : RecordDataValid section14Catalog 9 (⟨25,(10),[9,10],[38],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid241 : RecordDataValid section14Catalog 9 (⟨25,(11),[9,10],[34],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid242 : RecordDataValid section14Catalog 9 (⟨25,(11),[9,10],[35],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid243 : RecordDataValid section14Catalog 9 (⟨25,(11),[9,10],[38],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid244 : RecordDataValid section14Catalog 9 (⟨25,(12),[9,10],[34],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid245 : RecordDataValid section14Catalog 9 (⟨25,(12),[9,10],[35],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid246 : RecordDataValid section14Catalog 9 (⟨25,(12),[9,10],[38],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid247 : RecordDataValid section14Catalog 9 (⟨25,(13),[9,10],[34],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid248 : RecordDataValid section14Catalog 9 (⟨25,(13),[9,10],[35],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid249 : RecordDataValid section14Catalog 9 (⟨25,(13),[9,10],[38],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid250 : RecordDataValid section14Catalog 9 (⟨25,(14),[9,10],[34],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid251 : RecordDataValid section14Catalog 9 (⟨25,(14),[9,10],[35],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid252 : RecordDataValid section14Catalog 9 (⟨25,(14),[9,10],[38],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid253 : RecordDataValid section14Catalog 9 (⟨25,(15),[9,10],[34],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid254 : RecordDataValid section14Catalog 9 (⟨25,(15),[9,10],[35],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid255 : RecordDataValid section14Catalog 9 (⟨25,(15),[9,10],[38],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 224).take 32 = [⟨25,(5),[9,10],[35],167⟩,⟨25,(5),[9,10],[38],189⟩,⟨25,(6),[9,10],[34],81⟩,⟨25,(6),[9,10],[35],168⟩,⟨25,(6),[9,10],[38],216⟩,⟨25,(7),[9,10],[34],80⟩,⟨25,(7),[9,10],[35],167⟩,⟨25,(7),[9,10],[38],217⟩,⟨25,(8),[9,10],[34],82⟩,⟨25,(8),[9,10],[35],169⟩,⟨25,(8),[9,10],[38],218⟩,⟨25,(9),[9,10],[34],83⟩,⟨25,(9),[9,10],[35],170⟩,⟨25,(9),[9,10],[38],219⟩,⟨25,(10),[9,10],[34],84⟩,⟨25,(10),[9,10],[35],171⟩,⟨25,(10),[9,10],[38],194⟩,⟨25,(11),[9,10],[34],84⟩,⟨25,(11),[9,10],[35],171⟩,⟨25,(11),[9,10],[38],220⟩,⟨25,(12),[9,10],[34],84⟩,⟨25,(12),[9,10],[35],171⟩,⟨25,(12),[9,10],[38],220⟩,⟨25,(13),[9,10],[34],84⟩,⟨25,(13),[9,10],[35],171⟩,⟨25,(13),[9,10],[38],220⟩,⟨25,(14),[9,10],[34],83⟩,⟨25,(14),[9,10],[35],170⟩,⟨25,(14),[9,10],[38],219⟩,⟨25,(15),[9,10],[34],35⟩,⟨25,(15),[9,10],[35],172⟩,⟨25,(15),[9,10],[38],196⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid224
  · exact recordValid_of_data section14Catalog 9 _ hnum valid225
  · exact recordValid_of_data section14Catalog 9 _ hnum valid226
  · exact recordValid_of_data section14Catalog 9 _ hnum valid227
  · exact recordValid_of_data section14Catalog 9 _ hnum valid228
  · exact recordValid_of_data section14Catalog 9 _ hnum valid229
  · exact recordValid_of_data section14Catalog 9 _ hnum valid230
  · exact recordValid_of_data section14Catalog 9 _ hnum valid231
  · exact recordValid_of_data section14Catalog 9 _ hnum valid232
  · exact recordValid_of_data section14Catalog 9 _ hnum valid233
  · exact recordValid_of_data section14Catalog 9 _ hnum valid234
  · exact recordValid_of_data section14Catalog 9 _ hnum valid235
  · exact recordValid_of_data section14Catalog 9 _ hnum valid236
  · exact recordValid_of_data section14Catalog 9 _ hnum valid237
  · exact recordValid_of_data section14Catalog 9 _ hnum valid238
  · exact recordValid_of_data section14Catalog 9 _ hnum valid239
  · exact recordValid_of_data section14Catalog 9 _ hnum valid240
  · exact recordValid_of_data section14Catalog 9 _ hnum valid241
  · exact recordValid_of_data section14Catalog 9 _ hnum valid242
  · exact recordValid_of_data section14Catalog 9 _ hnum valid243
  · exact recordValid_of_data section14Catalog 9 _ hnum valid244
  · exact recordValid_of_data section14Catalog 9 _ hnum valid245
  · exact recordValid_of_data section14Catalog 9 _ hnum valid246
  · exact recordValid_of_data section14Catalog 9 _ hnum valid247
  · exact recordValid_of_data section14Catalog 9 _ hnum valid248
  · exact recordValid_of_data section14Catalog 9 _ hnum valid249
  · exact recordValid_of_data section14Catalog 9 _ hnum valid250
  · exact recordValid_of_data section14Catalog 9 _ hnum valid251
  · exact recordValid_of_data section14Catalog 9 _ hnum valid252
  · exact recordValid_of_data section14Catalog 9 _ hnum valid253
  · exact recordValid_of_data section14Catalog 9 _ hnum valid254
  · exact recordValid_of_data section14Catalog 9 _ hnum valid255
end Section14Records_9_224_256

#print axioms solution
