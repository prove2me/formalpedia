-- Prove2me | solution 1 for Freiman.section14_s0002_records_0160_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T05:52:52.666543+00:00
-- url     : https://prove2.me/submissions/5c9f08ed-c87c-4a83-9a0e-f59e426af8f8

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
namespace Section14Records_2_160_192
private theorem valid160 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,13,14],[191],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid161 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨240,[1,2,5,6,9,10,13,14],240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid162 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨241,[1,2,3,5,6,7,13,14,15],241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid163 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,13,14],[210],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid164 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid165 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,13,14],[238],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid166 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,13,14],[254],245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨245,[1,2,3,5,6,7,9,10,13,14,15],245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid167 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid168 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,13,14],[4,20],58⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨58,[1,2,3,5,6,7,13,14,15],58⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid169 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,13,14],[211],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid170 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,5,13,14],[235,251],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid171 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,13,14],[68],63⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨63,[1,2,4,5,6,8,9,10,12,13,14,16],63⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid172 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,13,14],[69],64⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨64,[1,2,4,5,6,8,9,10,12,13,14,16],64⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid173 : RecordDataValid section14Catalog 2 (⟨16,(-1),[1,2,13,14],[214,215],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid174 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,5,6,14],[170],208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨208,[1,2,3,5,6,7,13,14,15],208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid175 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,10,14],[0],912⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨912,[2,6,10,14],915⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid176 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[40,56],67⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨67,[1,2,5,6,13,14],67⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid177 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[44],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid178 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[60],71⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨71,[1,2,4,5,6,8,9,10,12,13,14,16],71⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid179 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[239],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid180 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[255],239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨239,[1,2,4,5,6,8,9,10,12,13,14,16],239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid181 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[16],913⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨913,[2,6,14],916⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid182 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[17],914⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨914,[2,3,6,7,11,14,15],917⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid183 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[134],916⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨916,[2,6,14],919⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid184 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,6,14],[151],917⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨917,[2,6,14],920⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid185 : RecordDataValid section14Catalog 2 (⟨16,(-1),[2,14],[135],916⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨916,[2,6,14],919⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid186 : RecordDataValid section14Catalog 2 (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid187 : RecordDataValid section14Catalog 2 (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨125,[1,2,3,5,6,7,13,14,15],125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid188 : RecordDataValid section14Catalog 2 (⟨18,(0),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid189 : RecordDataValid section14Catalog 2 (⟨18,(0),[2,6],[130],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid190 : RecordDataValid section14Catalog 2 (⟨18,(0),[2,14],[146,147],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid191 : RecordDataValid section14Catalog 2 (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 160).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 160).take 32 = [⟨16,(-1),[1,2,5,6,13,14],[191],239⟩,⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩,⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩,⟨16,(-1),[1,2,5,6,13,14],[210],242⟩,⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩,⟨16,(-1),[1,2,5,6,13,14],[238],244⟩,⟨16,(-1),[1,2,5,6,13,14],[254],245⟩,⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨16,(-1),[1,2,5,13,14],[4,20],58⟩,⟨16,(-1),[1,2,5,13,14],[211],242⟩,⟨16,(-1),[1,2,5,13,14],[235,251],243⟩,⟨16,(-1),[1,2,13,14],[68],63⟩,⟨16,(-1),[1,2,13,14],[69],64⟩,⟨16,(-1),[1,2,13,14],[214,215],242⟩,⟨16,(-1),[2,5,6,14],[170],208⟩,⟨16,(-1),[2,6,10,14],[0],912⟩,⟨16,(-1),[2,6,14],[40,56],67⟩,⟨16,(-1),[2,6,14],[44],69⟩,⟨16,(-1),[2,6,14],[60],71⟩,⟨16,(-1),[2,6,14],[239],207⟩,⟨16,(-1),[2,6,14],[255],239⟩,⟨16,(-1),[2,6,14],[16],913⟩,⟨16,(-1),[2,6,14],[17],914⟩,⟨16,(-1),[2,6,14],[134],916⟩,⟨16,(-1),[2,6,14],[151],917⟩,⟨16,(-1),[2,14],[135],916⟩,⟨18,(0),[1,2,5,6,13,14],[131],106⟩,⟨18,(0),[1,2,5,6,13,14],[150],125⟩,⟨18,(0),[1,2,13,14],[190],3⟩,⟨18,(0),[2,6],[130],106⟩,⟨18,(0),[2,14],[146,147],106⟩,⟨18,(1),[1,2,5,6,13,14],[131],106⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid160
  · exact recordValid_of_data section14Catalog 2 _ hnum valid161
  · exact recordValid_of_data section14Catalog 2 _ hnum valid162
  · exact recordValid_of_data section14Catalog 2 _ hnum valid163
  · exact recordValid_of_data section14Catalog 2 _ hnum valid164
  · exact recordValid_of_data section14Catalog 2 _ hnum valid165
  · exact recordValid_of_data section14Catalog 2 _ hnum valid166
  · exact recordValid_of_data section14Catalog 2 _ hnum valid167
  · exact recordValid_of_data section14Catalog 2 _ hnum valid168
  · exact recordValid_of_data section14Catalog 2 _ hnum valid169
  · exact recordValid_of_data section14Catalog 2 _ hnum valid170
  · exact recordValid_of_data section14Catalog 2 _ hnum valid171
  · exact recordValid_of_data section14Catalog 2 _ hnum valid172
  · exact recordValid_of_data section14Catalog 2 _ hnum valid173
  · exact recordValid_of_data section14Catalog 2 _ hnum valid174
  · exact recordValid_of_data section14Catalog 2 _ hnum valid175
  · exact recordValid_of_data section14Catalog 2 _ hnum valid176
  · exact recordValid_of_data section14Catalog 2 _ hnum valid177
  · exact recordValid_of_data section14Catalog 2 _ hnum valid178
  · exact recordValid_of_data section14Catalog 2 _ hnum valid179
  · exact recordValid_of_data section14Catalog 2 _ hnum valid180
  · exact recordValid_of_data section14Catalog 2 _ hnum valid181
  · exact recordValid_of_data section14Catalog 2 _ hnum valid182
  · exact recordValid_of_data section14Catalog 2 _ hnum valid183
  · exact recordValid_of_data section14Catalog 2 _ hnum valid184
  · exact recordValid_of_data section14Catalog 2 _ hnum valid185
  · exact recordValid_of_data section14Catalog 2 _ hnum valid186
  · exact recordValid_of_data section14Catalog 2 _ hnum valid187
  · exact recordValid_of_data section14Catalog 2 _ hnum valid188
  · exact recordValid_of_data section14Catalog 2 _ hnum valid189
  · exact recordValid_of_data section14Catalog 2 _ hnum valid190
  · exact recordValid_of_data section14Catalog 2 _ hnum valid191
end Section14Records_2_160_192

#print axioms solution
