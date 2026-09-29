-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_1216_1344
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:54:04.80458+00:00
-- url     : https://prove2.me/submissions/68d52bc4-b627-40fb-87c2-1b025520fe91

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1216_1248
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1216_1248
private theorem valid1216 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[45],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1217 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[104,120],67⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨67,[1,2,5,6,13,14],67⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1218 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[105,121],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1219 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[108],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1220 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[109],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1221 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[171,187],206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨206,[1,2,5,6,13,14],206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1222 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[175],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1223 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[234,250],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1224 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[238],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1225 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[17,21],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1226 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[64,68,80,84],342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨342,[1,2,4,5,6,8,9,10,12,13,14,16],343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1227 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[65,69,81,85],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1228 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[130,134],344⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨344,[1,2,4,5,6,8,9,10,12,13,14,16],345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1229 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[147,151],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1230 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[146],346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨346,[1,2,3,5,6,7,13,14,15],347⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1231 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[174],366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨366,[1,2,4,5,6,8,9,10,12,13,14,16],367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1232 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[186],367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨367,[1,2,3,5,6,7,13,14,15],368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1233 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[210,214],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1234 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,13,14],[235,251],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1235 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,13,14],[61],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1236 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,13,14],[124],342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨342,[1,2,4,5,6,8,9,10,12,13,14,16],343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1237 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,13,14],[125],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1238 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,13,14],[191],345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨345,[1,2,4,5,6,8,9,10,12,13,14,16],346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1239 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,13,14],[254],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1240 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1241 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,5,6,13],[194,198],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1242 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,5,9,13],[4],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1243 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,5,13],[40,56],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1244 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,5,13],[44],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1245 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,5,13],[239],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1246 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,5,13],[16,20],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1247 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,5,13],[195,199,211,215],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1216_1248 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1216).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1216).take 32 = [⟨60,(-1),[1,2,5,6,13,14],[45],61⟩,⟨60,(-1),[1,2,5,6,13,14],[104,120],67⟩,⟨60,(-1),[1,2,5,6,13,14],[105,121],68⟩,⟨60,(-1),[1,2,5,6,13,14],[108],69⟩,⟨60,(-1),[1,2,5,6,13,14],[109],70⟩,⟨60,(-1),[1,2,5,6,13,14],[171,187],206⟩,⟨60,(-1),[1,2,5,6,13,14],[175],207⟩,⟨60,(-1),[1,2,5,6,13,14],[234,250],243⟩,⟨60,(-1),[1,2,5,6,13,14],[238],244⟩,⟨60,(-1),[1,2,5,6,13,14],[17,21],341⟩,⟨60,(-1),[1,2,5,6,13,14],[64,68,80,84],342⟩,⟨60,(-1),[1,2,5,6,13,14],[65,69,81,85],343⟩,⟨60,(-1),[1,2,5,6,13,14],[130,134],344⟩,⟨60,(-1),[1,2,5,6,13,14],[147,151],345⟩,⟨60,(-1),[1,2,5,6,13,14],[146],346⟩,⟨60,(-1),[1,2,5,6,13,14],[174],366⟩,⟨60,(-1),[1,2,5,6,13,14],[186],367⟩,⟨60,(-1),[1,2,5,6,13,14],[210,214],385⟩,⟨60,(-1),[1,2,5,13,14],[235,251],243⟩,⟨60,(-1),[1,2,13,14],[61],341⟩,⟨60,(-1),[1,2,13,14],[124],342⟩,⟨60,(-1),[1,2,13,14],[125],343⟩,⟨60,(-1),[1,2,13,14],[191],345⟩,⟨60,(-1),[1,2,13,14],[254],385⟩,⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩,⟨60,(-1),[1,5,6,13],[194,198],385⟩,⟨60,(-1),[1,5,9,13],[4],341⟩,⟨60,(-1),[1,5,13],[40,56],60⟩,⟨60,(-1),[1,5,13],[44],61⟩,⟨60,(-1),[1,5,13],[239],244⟩,⟨60,(-1),[1,5,13],[16,20],341⟩,⟨60,(-1),[1,5,13],[195,199,211,215],385⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1216
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1217
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1218
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1219
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1220
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1221
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1222
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1223
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1224
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1225
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1226
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1227
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1228
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1229
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1230
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1231
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1232
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1233
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1234
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1235
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1236
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1237
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1238
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1239
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1240
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1241
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1242
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1243
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1244
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1245
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1246
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1247
end Section14Records_13_1216_1248

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1216_1248


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1248_1280
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1248_1280
private theorem valid1248 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,13],[60],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1249 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,13],[170],366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨366,[1,2,4,5,6,8,9,10,12,13,14,16],367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1250 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,13],[255],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1251 : RecordDataValid section14Catalog 13 (⟨60,(-1),[2,13,14],[131,135],344⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨344,[1,2,4,5,6,8,9,10,12,13,14,16],345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1252 : RecordDataValid section14Catalog 13 (⟨60,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1253 : RecordDataValid section14Catalog 13 (⟨60,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1254 : RecordDataValid section14Catalog 13 (⟨60,(-1),[13,14],[150],1728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1728,[13,14,15,16],1733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1255 : RecordDataValid section14Catalog 13 (⟨62,(0),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1256 : RecordDataValid section14Catalog 13 (⟨62,(1),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1257 : RecordDataValid section14Catalog 13 (⟨62,(2),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1258 : RecordDataValid section14Catalog 13 (⟨62,(3),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1259 : RecordDataValid section14Catalog 13 (⟨62,(4),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1260 : RecordDataValid section14Catalog 13 (⟨62,(5),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1261 : RecordDataValid section14Catalog 13 (⟨62,(6),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1262 : RecordDataValid section14Catalog 13 (⟨62,(7),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1263 : RecordDataValid section14Catalog 13 (⟨62,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1264 : RecordDataValid section14Catalog 13 (⟨62,(9),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1265 : RecordDataValid section14Catalog 13 (⟨62,(10),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1266 : RecordDataValid section14Catalog 13 (⟨62,(11),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1267 : RecordDataValid section14Catalog 13 (⟨62,(12),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1268 : RecordDataValid section14Catalog 13 (⟨62,(13),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1269 : RecordDataValid section14Catalog 13 (⟨62,(14),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1270 : RecordDataValid section14Catalog 13 (⟨62,(15),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1271 : RecordDataValid section14Catalog 13 (⟨62,(16),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1272 : RecordDataValid section14Catalog 13 (⟨62,(17),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1273 : RecordDataValid section14Catalog 13 (⟨62,(18),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1274 : RecordDataValid section14Catalog 13 (⟨62,(19),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1275 : RecordDataValid section14Catalog 13 (⟨62,(20),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1276 : RecordDataValid section14Catalog 13 (⟨62,(21),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1277 : RecordDataValid section14Catalog 13 (⟨62,(22),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1278 : RecordDataValid section14Catalog 13 (⟨62,(23),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1279 : RecordDataValid section14Catalog 13 (⟨62,(24),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1248_1280 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1248).take 32 = [⟨60,(-1),[1,13],[60],341⟩,⟨60,(-1),[1,13],[170],366⟩,⟨60,(-1),[1,13],[255],385⟩,⟨60,(-1),[2,13,14],[131,135],344⟩,⟨60,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨60,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩,⟨60,(-1),[13,14],[150],1728⟩,⟨62,(0),[1,2,5,6,13,14],[190],3⟩,⟨62,(1),[1,2,5,6,13,14],[190],3⟩,⟨62,(2),[1,2,5,6,13,14],[190],3⟩,⟨62,(3),[1,2,5,6,13,14],[190],3⟩,⟨62,(4),[1,2,5,6,13,14],[190],3⟩,⟨62,(5),[1,2,5,6,13,14],[190],3⟩,⟨62,(6),[1,2,5,6,13,14],[190],3⟩,⟨62,(7),[1,2,5,6,13,14],[190],3⟩,⟨62,(8),[1,2,5,6,13,14],[190],3⟩,⟨62,(9),[1,2,5,6,13,14],[190],3⟩,⟨62,(10),[1,2,5,6,13,14],[190],3⟩,⟨62,(11),[1,2,5,6,13,14],[190],3⟩,⟨62,(12),[1,2,5,6,13,14],[190],3⟩,⟨62,(13),[1,2,5,6,13,14],[190],3⟩,⟨62,(14),[1,2,5,6,13,14],[190],3⟩,⟨62,(15),[1,2,5,6,13,14],[190],3⟩,⟨62,(16),[1,2,5,6,13,14],[190],3⟩,⟨62,(17),[1,2,5,6,13,14],[190],3⟩,⟨62,(18),[1,2,5,6,13,14],[190],3⟩,⟨62,(19),[1,2,5,6,13,14],[190],3⟩,⟨62,(20),[1,2,5,6,13,14],[190],3⟩,⟨62,(21),[1,2,5,6,13,14],[190],3⟩,⟨62,(22),[1,2,5,6,13,14],[190],3⟩,⟨62,(23),[1,2,5,6,13,14],[190],3⟩,⟨62,(24),[1,2,5,6,13,14],[190],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1248
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1249
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1250
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1251
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1252
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1253
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1254
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1255
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1256
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1257
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1258
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1259
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1260
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1261
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1262
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1263
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1264
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1265
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1266
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1267
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1268
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1269
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1270
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1271
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1272
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1273
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1274
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1275
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1276
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1277
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1278
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1279
end Section14Records_13_1248_1280

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1248_1280


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1280_1312
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1280_1312
private theorem valid1280 : RecordDataValid section14Catalog 13 (⟨64,(0),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1281 : RecordDataValid section14Catalog 13 (⟨64,(1),[1,2,5,6,13,14],[190],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1282 : RecordDataValid section14Catalog 13 (⟨64,(2),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1283 : RecordDataValid section14Catalog 13 (⟨64,(3),[1,2,5,6,13,14],[190],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1284 : RecordDataValid section14Catalog 13 (⟨64,(4),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1285 : RecordDataValid section14Catalog 13 (⟨64,(5),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1286 : RecordDataValid section14Catalog 13 (⟨64,(6),[1,2,5,6,13,14],[190],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1287 : RecordDataValid section14Catalog 13 (⟨64,(7),[1,2,5,6,13,14],[190],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1288 : RecordDataValid section14Catalog 13 (⟨64,(8),[1,2,5,6,13,14],[190],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1289 : RecordDataValid section14Catalog 13 (⟨64,(9),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1290 : RecordDataValid section14Catalog 13 (⟨64,(10),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1291 : RecordDataValid section14Catalog 13 (⟨64,(11),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1292 : RecordDataValid section14Catalog 13 (⟨64,(12),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1293 : RecordDataValid section14Catalog 13 (⟨64,(13),[1,2,5,6,13,14],[190],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1294 : RecordDataValid section14Catalog 13 (⟨64,(14),[1,2,5,6,13,14],[190],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1295 : RecordDataValid section14Catalog 13 (⟨64,(15),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1296 : RecordDataValid section14Catalog 13 (⟨64,(16),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1297 : RecordDataValid section14Catalog 13 (⟨64,(17),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1298 : RecordDataValid section14Catalog 13 (⟨64,(18),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1299 : RecordDataValid section14Catalog 13 (⟨64,(19),[1,2,5,6,13,14],[190],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1300 : RecordDataValid section14Catalog 13 (⟨64,(20),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1301 : RecordDataValid section14Catalog 13 (⟨64,(21),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1302 : RecordDataValid section14Catalog 13 (⟨64,(22),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1303 : RecordDataValid section14Catalog 13 (⟨64,(23),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1304 : RecordDataValid section14Catalog 13 (⟨64,(24),[1,2,5,6,13,14],[190],374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨374,[1,2,3,4,5,6,7,8,13,14,15,16],375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1305 : RecordDataValid section14Catalog 13 (⟨67,(0),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1306 : RecordDataValid section14Catalog 13 (⟨67,(1),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1307 : RecordDataValid section14Catalog 13 (⟨67,(2),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1308 : RecordDataValid section14Catalog 13 (⟨67,(3),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1309 : RecordDataValid section14Catalog 13 (⟨67,(4),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1310 : RecordDataValid section14Catalog 13 (⟨67,(5),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1311 : RecordDataValid section14Catalog 13 (⟨67,(6),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1280_1312 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1280).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1280).take 32 = [⟨64,(0),[1,2,5,6,13,14],[190],368⟩,⟨64,(1),[1,2,5,6,13,14],[190],369⟩,⟨64,(2),[1,2,5,6,13,14],[190],368⟩,⟨64,(3),[1,2,5,6,13,14],[190],370⟩,⟨64,(4),[1,2,5,6,13,14],[190],371⟩,⟨64,(5),[1,2,5,6,13,14],[190],368⟩,⟨64,(6),[1,2,5,6,13,14],[190],369⟩,⟨64,(7),[1,2,5,6,13,14],[190],368⟩,⟨64,(8),[1,2,5,6,13,14],[190],370⟩,⟨64,(9),[1,2,5,6,13,14],[190],371⟩,⟨64,(10),[1,2,5,6,13,14],[190],372⟩,⟨64,(11),[1,2,5,6,13,14],[190],372⟩,⟨64,(12),[1,2,5,6,13,14],[190],372⟩,⟨64,(13),[1,2,5,6,13,14],[190],372⟩,⟨64,(14),[1,2,5,6,13,14],[190],371⟩,⟨64,(15),[1,2,5,6,13,14],[190],373⟩,⟨64,(16),[1,2,5,6,13,14],[190],373⟩,⟨64,(17),[1,2,5,6,13,14],[190],373⟩,⟨64,(18),[1,2,5,6,13,14],[190],373⟩,⟨64,(19),[1,2,5,6,13,14],[190],373⟩,⟨64,(20),[1,2,5,6,13,14],[190],374⟩,⟨64,(21),[1,2,5,6,13,14],[190],374⟩,⟨64,(22),[1,2,5,6,13,14],[190],374⟩,⟨64,(23),[1,2,5,6,13,14],[190],374⟩,⟨64,(24),[1,2,5,6,13,14],[190],374⟩,⟨67,(0),[1,2,5,6,13,14],[190],2⟩,⟨67,(1),[1,2,5,6,13,14],[190],2⟩,⟨67,(2),[1,2,5,6,13,14],[190],2⟩,⟨67,(3),[1,2,5,6,13,14],[190],2⟩,⟨67,(4),[1,2,5,6,13,14],[190],2⟩,⟨67,(5),[1,2,5,6,13,14],[190],2⟩,⟨67,(6),[1,2,5,6,13,14],[190],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1280
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1281
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1282
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1283
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1284
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1285
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1286
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1287
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1288
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1289
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1290
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1291
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1292
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1293
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1294
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1295
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1296
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1297
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1298
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1299
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1300
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1301
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1302
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1303
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1304
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1305
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1306
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1307
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1308
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1309
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1310
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1311
end Section14Records_13_1280_1312

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1280_1312


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1312_1344
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1312_1344
private theorem valid1312 : RecordDataValid section14Catalog 13 (⟨67,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1313 : RecordDataValid section14Catalog 13 (⟨67,(8),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1314 : RecordDataValid section14Catalog 13 (⟨67,(9),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1315 : RecordDataValid section14Catalog 13 (⟨67,(10),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1316 : RecordDataValid section14Catalog 13 (⟨67,(11),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1317 : RecordDataValid section14Catalog 13 (⟨67,(12),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1318 : RecordDataValid section14Catalog 13 (⟨67,(13),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1319 : RecordDataValid section14Catalog 13 (⟨67,(14),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1320 : RecordDataValid section14Catalog 13 (⟨67,(15),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1321 : RecordDataValid section14Catalog 13 (⟨67,(16),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1322 : RecordDataValid section14Catalog 13 (⟨67,(17),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1323 : RecordDataValid section14Catalog 13 (⟨67,(18),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1324 : RecordDataValid section14Catalog 13 (⟨67,(19),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1325 : RecordDataValid section14Catalog 13 (⟨67,(20),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1326 : RecordDataValid section14Catalog 13 (⟨67,(21),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1327 : RecordDataValid section14Catalog 13 (⟨67,(22),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1328 : RecordDataValid section14Catalog 13 (⟨67,(23),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1329 : RecordDataValid section14Catalog 13 (⟨67,(24),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1330 : RecordDataValid section14Catalog 13 (⟨69,(0),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1331 : RecordDataValid section14Catalog 13 (⟨69,(1),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1332 : RecordDataValid section14Catalog 13 (⟨69,(2),[1,5,6,13],[190],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1333 : RecordDataValid section14Catalog 13 (⟨69,(3),[1,5,6,13],[190],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1334 : RecordDataValid section14Catalog 13 (⟨69,(4),[1,5,6,13],[190],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1335 : RecordDataValid section14Catalog 13 (⟨69,(5),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1336 : RecordDataValid section14Catalog 13 (⟨69,(6),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1337 : RecordDataValid section14Catalog 13 (⟨69,(7),[1,2,5,6,13,14],[190],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1338 : RecordDataValid section14Catalog 13 (⟨69,(8),[1,2,5,6,13,14],[190],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1339 : RecordDataValid section14Catalog 13 (⟨69,(9),[1,2,5,6,13,14],[190],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1340 : RecordDataValid section14Catalog 13 (⟨69,(10),[1,2,5,6,13,14],[190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1341 : RecordDataValid section14Catalog 13 (⟨69,(11),[1,2,5,6,13,14],[190],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1342 : RecordDataValid section14Catalog 13 (⟨69,(12),[1,2,5,6,13,14],[190],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1343 : RecordDataValid section14Catalog 13 (⟨69,(13),[1,2,5,6,13,14],[190],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1312_1344 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1312).take 32 = [⟨67,(7),[1,2,5,6,13,14],[190],2⟩,⟨67,(8),[1,2,5,6,13,14],[190],2⟩,⟨67,(9),[1,2,5,6,13,14],[190],2⟩,⟨67,(10),[1,2,5,6,13,14],[190],2⟩,⟨67,(11),[1,2,5,6,13,14],[190],2⟩,⟨67,(12),[1,2,5,6,13,14],[190],2⟩,⟨67,(13),[1,2,5,6,13,14],[190],2⟩,⟨67,(14),[1,2,5,6,13,14],[190],2⟩,⟨67,(15),[1,2,5,6,13,14],[190],2⟩,⟨67,(16),[1,2,5,6,13,14],[190],2⟩,⟨67,(17),[1,2,5,6,13,14],[190],2⟩,⟨67,(18),[1,2,5,6,13,14],[190],2⟩,⟨67,(19),[1,2,5,6,13,14],[190],2⟩,⟨67,(20),[1,2,5,6,13,14],[190],2⟩,⟨67,(21),[1,2,5,6,13,14],[190],2⟩,⟨67,(22),[1,2,5,6,13,14],[190],2⟩,⟨67,(23),[1,2,5,6,13,14],[190],2⟩,⟨67,(24),[1,2,5,6,13,14],[190],2⟩,⟨69,(0),[1,2,5,6,13,14],[190],189⟩,⟨69,(1),[1,2,5,6,13,14],[190],260⟩,⟨69,(2),[1,5,6,13],[190],375⟩,⟨69,(3),[1,5,6,13],[190],376⟩,⟨69,(4),[1,5,6,13],[190],377⟩,⟨69,(5),[1,2,5,6,13,14],[190],189⟩,⟨69,(6),[1,2,5,6,13,14],[190],260⟩,⟨69,(7),[1,2,5,6,13,14],[190],375⟩,⟨69,(8),[1,2,5,6,13,14],[190],376⟩,⟨69,(9),[1,2,5,6,13,14],[190],377⟩,⟨69,(10),[1,2,5,6,13,14],[190],194⟩,⟨69,(11),[1,2,5,6,13,14],[190],267⟩,⟨69,(12),[1,2,5,6,13,14],[190],378⟩,⟨69,(13),[1,2,5,6,13,14],[190],378⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1312
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1313
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1314
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1315
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1316
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1317
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1318
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1319
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1320
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1321
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1322
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1323
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1324
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1325
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1326
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1327
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1328
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1329
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1330
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1331
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1332
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1333
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1334
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1335
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1336
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1337
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1338
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1339
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1340
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1341
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1342
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1343
end Section14Records_13_1312_1344

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1312_1344

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1216).take 128, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 1216 1280 1344 (by decide) (by decide) (all_of_interval_split P xs 1216 1248 1280 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_1216_1248 hnum) (Freiman.workReverse20260919_s0013_records_1248_1280 hnum)) (all_of_interval_split P xs 1280 1312 1344 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_1280_1312 hnum) (Freiman.workReverse20260919_s0013_records_1312_1344 hnum)))

#print axioms solution
