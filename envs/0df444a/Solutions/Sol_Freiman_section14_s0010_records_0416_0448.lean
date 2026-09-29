-- Prove2me | solution 1 for Freiman.section14_s0010_records_0416_0448
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:39:17.908981+00:00
-- url     : https://prove2.me/submissions/7fbbbdad-8093-44cf-a600-35850866e51d

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
namespace Section14Records_10_416_448
private theorem valid416 : RecordDataValid section14Catalog 10 (⟨35,(8),[9,10],[34,35,38],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid417 : RecordDataValid section14Catalog 10 (⟨35,(9),[9,10],[34,35,38],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid418 : RecordDataValid section14Catalog 10 (⟨35,(10),[9,10],[35],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid419 : RecordDataValid section14Catalog 10 (⟨35,(10),[9,10],[38],1396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1396,[5,9,10],1401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid420 : RecordDataValid section14Catalog 10 (⟨35,(10),[10],[34],915⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨915,[2,6,10],918⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid421 : RecordDataValid section14Catalog 10 (⟨35,(11),[9,10],[34,38],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid422 : RecordDataValid section14Catalog 10 (⟨35,(11),[9,10],[35],123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨123,[1,2,5,6,9,10],123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid423 : RecordDataValid section14Catalog 10 (⟨35,(12),[9,10],[34,35,38],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid424 : RecordDataValid section14Catalog 10 (⟨35,(13),[9,10],[34,35,38],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid425 : RecordDataValid section14Catalog 10 (⟨35,(14),[9,10],[35],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid426 : RecordDataValid section14Catalog 10 (⟨35,(14),[9,10],[38],188⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨188,[1,5,9,10],188⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid427 : RecordDataValid section14Catalog 10 (⟨35,(14),[10],[34],124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨124,[1,2,3,5,6,7,9,10,11],124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid428 : RecordDataValid section14Catalog 10 (⟨35,(15),[9,10],[34,38],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid429 : RecordDataValid section14Catalog 10 (⟨35,(15),[9,10],[35],124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨124,[1,2,3,5,6,7,9,10,11],124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid430 : RecordDataValid section14Catalog 10 (⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid431 : RecordDataValid section14Catalog 10 (⟨38,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid432 : RecordDataValid section14Catalog 10 (⟨38,(-1),[1,2,5,6,9,10,13,14],[5],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid433 : RecordDataValid section14Catalog 10 (⟨38,(-1),[2,4,6,8,10,12,14,16],[0,4],247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨247,[1,2,4,5,6,8,9,10,12,13,14,16],247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid434 : RecordDataValid section14Catalog 10 (⟨38,(-1),[2,6,9,10,14],[16,20],247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨247,[1,2,4,5,6,8,9,10,12,13,14,16],247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid435 : RecordDataValid section14Catalog 10 (⟨38,(-1),[4,8,10,12,16],[8],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid436 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid437 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[9],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid438 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[24],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid439 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[25],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid440 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[43],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid441 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[58],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid442 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[17,21],248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨248,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid443 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[34],249⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨249,[1,2,4,5,6,8,9,10,12,13,14,16],249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid444 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[35,39],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid445 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10],[50,54],340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨340,[1,2,3,5,6,7,9,10,11,13,14,15],341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid446 : RecordDataValid section14Catalog 10 (⟨38,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid447 : RecordDataValid section14Catalog 10 (⟨38,(-1),[10],[13],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 416).take 32 = [⟨35,(8),[9,10],[34,35,38],2⟩,⟨35,(9),[9,10],[34,35,38],2⟩,⟨35,(10),[9,10],[35],101⟩,⟨35,(10),[9,10],[38],1396⟩,⟨35,(10),[10],[34],915⟩,⟨35,(11),[9,10],[34,38],101⟩,⟨35,(11),[9,10],[35],123⟩,⟨35,(12),[9,10],[34,35,38],2⟩,⟨35,(13),[9,10],[34,35,38],2⟩,⟨35,(14),[9,10],[35],101⟩,⟨35,(14),[9,10],[38],188⟩,⟨35,(14),[10],[34],124⟩,⟨35,(15),[9,10],[34,38],101⟩,⟨35,(15),[9,10],[35],124⟩,⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩,⟨38,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨38,(-1),[1,2,5,6,9,10,13,14],[5],246⟩,⟨38,(-1),[2,4,6,8,10,12,14,16],[0,4],247⟩,⟨38,(-1),[2,6,9,10,14],[16,20],247⟩,⟨38,(-1),[4,8,10,12,16],[8],69⟩,⟨38,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩,⟨38,(-1),[9,10],[9],61⟩,⟨38,(-1),[9,10],[24],69⟩,⟨38,(-1),[9,10],[25],70⟩,⟨38,(-1),[9,10],[43],207⟩,⟨38,(-1),[9,10],[58],244⟩,⟨38,(-1),[9,10],[17,21],248⟩,⟨38,(-1),[9,10],[34],249⟩,⟨38,(-1),[9,10],[35,39],251⟩,⟨38,(-1),[9,10],[50,54],340⟩,⟨38,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨38,(-1),[10],[13],62⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid416
  · exact recordValid_of_data section14Catalog 10 _ hnum valid417
  · exact recordValid_of_data section14Catalog 10 _ hnum valid418
  · exact recordValid_of_data section14Catalog 10 _ hnum valid419
  · exact recordValid_of_data section14Catalog 10 _ hnum valid420
  · exact recordValid_of_data section14Catalog 10 _ hnum valid421
  · exact recordValid_of_data section14Catalog 10 _ hnum valid422
  · exact recordValid_of_data section14Catalog 10 _ hnum valid423
  · exact recordValid_of_data section14Catalog 10 _ hnum valid424
  · exact recordValid_of_data section14Catalog 10 _ hnum valid425
  · exact recordValid_of_data section14Catalog 10 _ hnum valid426
  · exact recordValid_of_data section14Catalog 10 _ hnum valid427
  · exact recordValid_of_data section14Catalog 10 _ hnum valid428
  · exact recordValid_of_data section14Catalog 10 _ hnum valid429
  · exact recordValid_of_data section14Catalog 10 _ hnum valid430
  · exact recordValid_of_data section14Catalog 10 _ hnum valid431
  · exact recordValid_of_data section14Catalog 10 _ hnum valid432
  · exact recordValid_of_data section14Catalog 10 _ hnum valid433
  · exact recordValid_of_data section14Catalog 10 _ hnum valid434
  · exact recordValid_of_data section14Catalog 10 _ hnum valid435
  · exact recordValid_of_data section14Catalog 10 _ hnum valid436
  · exact recordValid_of_data section14Catalog 10 _ hnum valid437
  · exact recordValid_of_data section14Catalog 10 _ hnum valid438
  · exact recordValid_of_data section14Catalog 10 _ hnum valid439
  · exact recordValid_of_data section14Catalog 10 _ hnum valid440
  · exact recordValid_of_data section14Catalog 10 _ hnum valid441
  · exact recordValid_of_data section14Catalog 10 _ hnum valid442
  · exact recordValid_of_data section14Catalog 10 _ hnum valid443
  · exact recordValid_of_data section14Catalog 10 _ hnum valid444
  · exact recordValid_of_data section14Catalog 10 _ hnum valid445
  · exact recordValid_of_data section14Catalog 10 _ hnum valid446
  · exact recordValid_of_data section14Catalog 10 _ hnum valid447
end Section14Records_10_416_448

#print axioms solution
