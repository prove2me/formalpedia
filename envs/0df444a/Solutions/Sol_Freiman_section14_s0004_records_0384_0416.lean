-- Prove2me | solution 1 for Freiman.section14_s0004_records_0384_0416
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:09:56.852778+00:00
-- url     : https://prove2.me/submissions/b29dd8fd-d038-4a47-bd96-61eda0a37144

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
namespace Section14Records_4_384_416
private theorem valid384 : RecordDataValid section14Catalog 4 (⟨57,(4),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid385 : RecordDataValid section14Catalog 4 (⟨57,(5),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid386 : RecordDataValid section14Catalog 4 (⟨57,(6),[4,8,12],[10],284⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨284,[1,2,4,5,6,8,9,10,12],285⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid387 : RecordDataValid section14Catalog 4 (⟨57,(6),[4,8,12],[14],338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨338,[1,2,4,5,6,8,9,10,12],339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid388 : RecordDataValid section14Catalog 4 (⟨57,(7),[4,8,12],[10,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid389 : RecordDataValid section14Catalog 4 (⟨57,(8),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid390 : RecordDataValid section14Catalog 4 (⟨57,(9),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid391 : RecordDataValid section14Catalog 4 (⟨57,(10),[4,8,12],[10],285⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨285,[1,2,4,5,6,8,9,10,12],286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid392 : RecordDataValid section14Catalog 4 (⟨57,(10),[4,8,12],[14],339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨339,[1,2,4,5,6,8,9,10,12],340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid393 : RecordDataValid section14Catalog 4 (⟨57,(11),[4,8,12],[10,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid394 : RecordDataValid section14Catalog 4 (⟨57,(12),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid395 : RecordDataValid section14Catalog 4 (⟨57,(13),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid396 : RecordDataValid section14Catalog 4 (⟨57,(14),[4,8,12],[10,14],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid397 : RecordDataValid section14Catalog 4 (⟨57,(15),[4,8,12],[10,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid398 : RecordDataValid section14Catalog 4 (⟨57,(16),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid399 : RecordDataValid section14Catalog 4 (⟨57,(17),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid400 : RecordDataValid section14Catalog 4 (⟨57,(18),[4,8,12],[10,14],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid401 : RecordDataValid section14Catalog 4 (⟨57,(19),[4,8,12],[10,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid402 : RecordDataValid section14Catalog 4 (⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨342,[1,2,4,5,6,8,9,10,12,13,14,16],343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid403 : RecordDataValid section14Catalog 4 (⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid404 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,10,12,16],[8],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid405 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,11,12,16],[1],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid406 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,12],[3],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid407 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,12,16],[9],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid408 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,12,16],[11],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid409 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,12,16],[2],344⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨344,[1,2,4,5,6,8,9,10,12,13,14,16],345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid410 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,12,16],[7],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid411 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,8,12,16],[10],366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨366,[1,2,4,5,6,8,9,10,12,13,14,16],367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid412 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,16],[12],342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨342,[1,2,4,5,6,8,9,10,12,13,14,16],343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid413 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,16],[13],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid414 : RecordDataValid section14Catalog 4 (⟨60,(-1),[4,16],[15],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid415 : RecordDataValid section14Catalog 4 (⟨64,(0),[4,8],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 384).take 32 = [⟨57,(4),[4,8,12],[10,14],2⟩,⟨57,(5),[4,8,12],[10,14],2⟩,⟨57,(6),[4,8,12],[10],284⟩,⟨57,(6),[4,8,12],[14],338⟩,⟨57,(7),[4,8,12],[10,14],101⟩,⟨57,(8),[4,8,12],[10,14],2⟩,⟨57,(9),[4,8,12],[10,14],2⟩,⟨57,(10),[4,8,12],[10],285⟩,⟨57,(10),[4,8,12],[14],339⟩,⟨57,(11),[4,8,12],[10,14],101⟩,⟨57,(12),[4,8,12],[10,14],2⟩,⟨57,(13),[4,8,12],[10,14],2⟩,⟨57,(14),[4,8,12],[10,14],286⟩,⟨57,(15),[4,8,12],[10,14],101⟩,⟨57,(16),[4,8,12],[10,14],2⟩,⟨57,(17),[4,8,12],[10,14],2⟩,⟨57,(18),[4,8,12],[10,14],287⟩,⟨57,(19),[4,8,12],[10,14],101⟩,⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩,⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩,⟨60,(-1),[4,8,10,12,16],[8],69⟩,⟨60,(-1),[4,8,11,12,16],[1],343⟩,⟨60,(-1),[4,8,12],[3],345⟩,⟨60,(-1),[4,8,12,16],[9],70⟩,⟨60,(-1),[4,8,12,16],[11],207⟩,⟨60,(-1),[4,8,12,16],[2],344⟩,⟨60,(-1),[4,8,12,16],[7],345⟩,⟨60,(-1),[4,8,12,16],[10],366⟩,⟨60,(-1),[4,16],[12],342⟩,⟨60,(-1),[4,16],[13],343⟩,⟨60,(-1),[4,16],[15],345⟩,⟨64,(0),[4,8],[6],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid384
  · exact recordValid_of_data section14Catalog 4 _ hnum valid385
  · exact recordValid_of_data section14Catalog 4 _ hnum valid386
  · exact recordValid_of_data section14Catalog 4 _ hnum valid387
  · exact recordValid_of_data section14Catalog 4 _ hnum valid388
  · exact recordValid_of_data section14Catalog 4 _ hnum valid389
  · exact recordValid_of_data section14Catalog 4 _ hnum valid390
  · exact recordValid_of_data section14Catalog 4 _ hnum valid391
  · exact recordValid_of_data section14Catalog 4 _ hnum valid392
  · exact recordValid_of_data section14Catalog 4 _ hnum valid393
  · exact recordValid_of_data section14Catalog 4 _ hnum valid394
  · exact recordValid_of_data section14Catalog 4 _ hnum valid395
  · exact recordValid_of_data section14Catalog 4 _ hnum valid396
  · exact recordValid_of_data section14Catalog 4 _ hnum valid397
  · exact recordValid_of_data section14Catalog 4 _ hnum valid398
  · exact recordValid_of_data section14Catalog 4 _ hnum valid399
  · exact recordValid_of_data section14Catalog 4 _ hnum valid400
  · exact recordValid_of_data section14Catalog 4 _ hnum valid401
  · exact recordValid_of_data section14Catalog 4 _ hnum valid402
  · exact recordValid_of_data section14Catalog 4 _ hnum valid403
  · exact recordValid_of_data section14Catalog 4 _ hnum valid404
  · exact recordValid_of_data section14Catalog 4 _ hnum valid405
  · exact recordValid_of_data section14Catalog 4 _ hnum valid406
  · exact recordValid_of_data section14Catalog 4 _ hnum valid407
  · exact recordValid_of_data section14Catalog 4 _ hnum valid408
  · exact recordValid_of_data section14Catalog 4 _ hnum valid409
  · exact recordValid_of_data section14Catalog 4 _ hnum valid410
  · exact recordValid_of_data section14Catalog 4 _ hnum valid411
  · exact recordValid_of_data section14Catalog 4 _ hnum valid412
  · exact recordValid_of_data section14Catalog 4 _ hnum valid413
  · exact recordValid_of_data section14Catalog 4 _ hnum valid414
  · exact recordValid_of_data section14Catalog 4 _ hnum valid415
end Section14Records_4_384_416

#print axioms solution
