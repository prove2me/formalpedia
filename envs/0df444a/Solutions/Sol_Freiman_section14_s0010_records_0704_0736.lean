-- Prove2me | solution 1 for Freiman.section14_s0010_records_0704_0736
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:46:54.424141+00:00
-- url     : https://prove2.me/submissions/e29c34a9-ca83-4e36-991e-e044ea58e06e

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
namespace Section14Records_10_704_736
private theorem valid704 : RecordDataValid section14Catalog 10 (⟨57,(17),[9,10],[38,42,46],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid705 : RecordDataValid section14Catalog 10 (⟨57,(18),[9,10],[38,42,46],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid706 : RecordDataValid section14Catalog 10 (⟨57,(19),[9,10],[38,42,46],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid707 : RecordDataValid section14Catalog 10 (⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid708 : RecordDataValid section14Catalog 10 (⟨60,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid709 : RecordDataValid section14Catalog 10 (⟨60,(-1),[1,2,5,6,9,10,13,14],[5],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid710 : RecordDataValid section14Catalog 10 (⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨342,[1,2,4,5,6,8,9,10,12,13,14,16],343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid711 : RecordDataValid section14Catalog 10 (⟨60,(-1),[2,6,9,10,14],[16,20],342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨342,[1,2,4,5,6,8,9,10,12,13,14,16],343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid712 : RecordDataValid section14Catalog 10 (⟨60,(-1),[4,8,10,12,16],[8],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid713 : RecordDataValid section14Catalog 10 (⟨60,(-1),[8,10,12],[12],71⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨71,[1,2,4,5,6,8,9,10,12,13,14,16],71⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid714 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid715 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[9],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid716 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[13],62⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid717 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[24],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid718 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[25],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid719 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[28],71⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨71,[1,2,4,5,6,8,9,10,12,13,14,16],71⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid720 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[29],72⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨72,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],72⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid721 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[43],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid722 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[47],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid723 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[58],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid724 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[62],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid725 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[17,21],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid726 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[34],344⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨344,[1,2,4,5,6,8,9,10,12,13,14,16],345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid727 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[35,39],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid728 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[42],366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨366,[1,2,4,5,6,8,9,10,12,13,14,16],367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid729 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10],[50,54],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid730 : RecordDataValid section14Catalog 10 (⟨60,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid731 : RecordDataValid section14Catalog 10 (⟨60,(-1),[10],[59],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid732 : RecordDataValid section14Catalog 10 (⟨60,(-1),[10],[63],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid733 : RecordDataValid section14Catalog 10 (⟨60,(-1),[10],[51,55],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid734 : RecordDataValid section14Catalog 10 (⟨62,(0),[9,10],[46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid735 : RecordDataValid section14Catalog 10 (⟨62,(0),[9,10],[38],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 704).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 704).take 32 = [⟨57,(17),[9,10],[38,42,46],2⟩,⟨57,(18),[9,10],[38,42,46],287⟩,⟨57,(19),[9,10],[38,42,46],101⟩,⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩,⟨60,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨60,(-1),[1,2,5,6,9,10,13,14],[5],341⟩,⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩,⟨60,(-1),[2,6,9,10,14],[16,20],342⟩,⟨60,(-1),[4,8,10,12,16],[8],69⟩,⟨60,(-1),[8,10,12],[12],71⟩,⟨60,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩,⟨60,(-1),[9,10],[9],61⟩,⟨60,(-1),[9,10],[13],62⟩,⟨60,(-1),[9,10],[24],69⟩,⟨60,(-1),[9,10],[25],70⟩,⟨60,(-1),[9,10],[28],71⟩,⟨60,(-1),[9,10],[29],72⟩,⟨60,(-1),[9,10],[43],207⟩,⟨60,(-1),[9,10],[47],239⟩,⟨60,(-1),[9,10],[58],244⟩,⟨60,(-1),[9,10],[62],245⟩,⟨60,(-1),[9,10],[17,21],343⟩,⟨60,(-1),[9,10],[34],344⟩,⟨60,(-1),[9,10],[35,39],345⟩,⟨60,(-1),[9,10],[42],366⟩,⟨60,(-1),[9,10],[50,54],385⟩,⟨60,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨60,(-1),[10],[59],207⟩,⟨60,(-1),[10],[63],239⟩,⟨60,(-1),[10],[51,55],345⟩,⟨62,(0),[9,10],[46],3⟩,⟨62,(0),[9,10],[38],347⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid704
  · exact recordValid_of_data section14Catalog 10 _ hnum valid705
  · exact recordValid_of_data section14Catalog 10 _ hnum valid706
  · exact recordValid_of_data section14Catalog 10 _ hnum valid707
  · exact recordValid_of_data section14Catalog 10 _ hnum valid708
  · exact recordValid_of_data section14Catalog 10 _ hnum valid709
  · exact recordValid_of_data section14Catalog 10 _ hnum valid710
  · exact recordValid_of_data section14Catalog 10 _ hnum valid711
  · exact recordValid_of_data section14Catalog 10 _ hnum valid712
  · exact recordValid_of_data section14Catalog 10 _ hnum valid713
  · exact recordValid_of_data section14Catalog 10 _ hnum valid714
  · exact recordValid_of_data section14Catalog 10 _ hnum valid715
  · exact recordValid_of_data section14Catalog 10 _ hnum valid716
  · exact recordValid_of_data section14Catalog 10 _ hnum valid717
  · exact recordValid_of_data section14Catalog 10 _ hnum valid718
  · exact recordValid_of_data section14Catalog 10 _ hnum valid719
  · exact recordValid_of_data section14Catalog 10 _ hnum valid720
  · exact recordValid_of_data section14Catalog 10 _ hnum valid721
  · exact recordValid_of_data section14Catalog 10 _ hnum valid722
  · exact recordValid_of_data section14Catalog 10 _ hnum valid723
  · exact recordValid_of_data section14Catalog 10 _ hnum valid724
  · exact recordValid_of_data section14Catalog 10 _ hnum valid725
  · exact recordValid_of_data section14Catalog 10 _ hnum valid726
  · exact recordValid_of_data section14Catalog 10 _ hnum valid727
  · exact recordValid_of_data section14Catalog 10 _ hnum valid728
  · exact recordValid_of_data section14Catalog 10 _ hnum valid729
  · exact recordValid_of_data section14Catalog 10 _ hnum valid730
  · exact recordValid_of_data section14Catalog 10 _ hnum valid731
  · exact recordValid_of_data section14Catalog 10 _ hnum valid732
  · exact recordValid_of_data section14Catalog 10 _ hnum valid733
  · exact recordValid_of_data section14Catalog 10 _ hnum valid734
  · exact recordValid_of_data section14Catalog 10 _ hnum valid735
end Section14Records_10_704_736

#print axioms solution
