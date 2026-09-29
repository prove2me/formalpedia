-- Prove2me | solution 1 for Freiman.section14_s0002_records_2400_2432
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:04:57.633849+00:00
-- url     : https://prove2.me/submissions/70f4c5c8-0d1a-4feb-b18b-0a1bb0db42f1

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
namespace Section14Records_2_2400_2432
private theorem valid2400 : RecordDataValid section14Catalog 2 (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨855,[1,2,3,5,6,7,10,11,13,14,15],856⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2401 : RecordDataValid section14Catalog 2 (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2402 : RecordDataValid section14Catalog 2 (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2403 : RecordDataValid section14Catalog 2 (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2404 : RecordDataValid section14Catalog 2 (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2405 : RecordDataValid section14Catalog 2 (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨860,[1,2,3,5,6,7,10,11,13,14,15],861⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2406 : RecordDataValid section14Catalog 2 (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2407 : RecordDataValid section14Catalog 2 (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2408 : RecordDataValid section14Catalog 2 (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2409 : RecordDataValid section14Catalog 2 (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2410 : RecordDataValid section14Catalog 2 (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2411 : RecordDataValid section14Catalog 2 (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2412 : RecordDataValid section14Catalog 2 (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2413 : RecordDataValid section14Catalog 2 (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2414 : RecordDataValid section14Catalog 2 (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2415 : RecordDataValid section14Catalog 2 (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2416 : RecordDataValid section14Catalog 2 (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2417 : RecordDataValid section14Catalog 2 (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2418 : RecordDataValid section14Catalog 2 (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2419 : RecordDataValid section14Catalog 2 (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2420 : RecordDataValid section14Catalog 2 (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2421 : RecordDataValid section14Catalog 2 (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2422 : RecordDataValid section14Catalog 2 (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2423 : RecordDataValid section14Catalog 2 (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2424 : RecordDataValid section14Catalog 2 (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2425 : RecordDataValid section14Catalog 2 (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2426 : RecordDataValid section14Catalog 2 (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2427 : RecordDataValid section14Catalog 2 (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2428 : RecordDataValid section14Catalog 2 (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2429 : RecordDataValid section14Catalog 2 (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2430 : RecordDataValid section14Catalog 2 (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2431 : RecordDataValid section14Catalog 2 (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2400).take 32 = [⟨232,(14),[1,2,5,6,13,14],[170],855⟩,⟨232,(15),[1,2,5,6,13,14],[170],856⟩,⟨232,(16),[1,2,5,6,13,14],[170],857⟩,⟨232,(17),[1,2,5,6,13,14],[170],858⟩,⟨232,(18),[1,2,5,6,13,14],[170],859⟩,⟨232,(19),[1,2,5,6,13,14],[170],860⟩,⟨234,(0),[1,2,5,6,13,14],[170],568⟩,⟨234,(1),[1,2,5,6,13,14],[170],569⟩,⟨234,(2),[1,2,5,6,13,14],[170],570⟩,⟨234,(3),[1,2,5,6,13,14],[170],571⟩,⟨234,(4),[1,2,5,6,13,14],[170],572⟩,⟨234,(5),[1,2,5,6,13,14],[170],573⟩,⟨234,(6),[1,2,5,6,13,14],[170],573⟩,⟨234,(7),[1,2,5,6,13,14],[170],573⟩,⟨234,(8),[1,2,5,6,13,14],[170],574⟩,⟨234,(9),[1,2,5,6,13,14],[170],575⟩,⟨234,(10),[1,2,5,6,13,14],[170],575⟩,⟨234,(11),[1,2,5,6,13,14],[170],575⟩,⟨234,(12),[1,2,5,6,13,14],[170],576⟩,⟨234,(13),[1,2,5,6,13,14],[170],577⟩,⟨234,(14),[1,2,5,6,13,14],[170],577⟩,⟨234,(15),[1,2,5,6,13,14],[170],577⟩,⟨235,(0),[1,2,5,6,13,14],[170],578⟩,⟨235,(1),[1,2,5,6,13,14],[170],579⟩,⟨235,(2),[1,2,5,6,13,14],[170],580⟩,⟨235,(3),[1,2,5,6,13,14],[170],581⟩,⟨235,(4),[1,2,5,6,13,14],[170],582⟩,⟨235,(5),[1,2,5,6,13,14],[170],583⟩,⟨235,(6),[1,2,5,6,13,14],[170],584⟩,⟨235,(7),[1,2,5,6,13,14],[170],585⟩,⟨235,(8),[1,2,5,6,13,14],[170],578⟩,⟨235,(9),[1,2,5,6,13,14],[170],579⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2400
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2401
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2402
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2403
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2404
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2405
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2406
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2407
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2408
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2409
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2410
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2411
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2412
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2413
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2414
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2415
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2416
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2417
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2418
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2419
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2420
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2421
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2422
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2423
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2424
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2425
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2426
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2427
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2428
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2429
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2430
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2431
end Section14Records_2_2400_2432

#print axioms solution
