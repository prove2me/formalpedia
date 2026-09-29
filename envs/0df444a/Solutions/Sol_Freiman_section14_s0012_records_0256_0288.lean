-- Prove2me | solution 1 for Freiman.section14_s0012_records_0256_0288
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:19:18.663056+00:00
-- url     : https://prove2.me/submissions/f3ff3db9-3325-4cd8-91e5-82cdb9141676

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
namespace Section14Records_12_256_288
private theorem valid256 : RecordDataValid section14Catalog 12 (⟨50,(14),[4,8,12],[14],336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨336,[1,2,4,5,6,8,9,10,12],337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid257 : RecordDataValid section14Catalog 12 (⟨50,(14),[12],[6],336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨336,[1,2,4,5,6,8,9,10,12],337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid258 : RecordDataValid section14Catalog 12 (⟨50,(15),[4,8,12],[10],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid259 : RecordDataValid section14Catalog 12 (⟨50,(15),[4,8,12],[14],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid260 : RecordDataValid section14Catalog 12 (⟨50,(15),[12],[6],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid261 : RecordDataValid section14Catalog 12 (⟨53,(0),[3,4,7,8,12],[10],279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨279,[1,2,3,4,5,6,7,8,9,10,11,12],280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid262 : RecordDataValid section14Catalog 12 (⟨53,(0),[4,8,12],[14],325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨325,[1,2,4,5,6,8,9,10,12],326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid263 : RecordDataValid section14Catalog 12 (⟨53,(0),[12],[6],360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨360,[1,2,3,4,5,6,7,8,9,10,12],361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid264 : RecordDataValid section14Catalog 12 (⟨53,(1),[3,4,7,8,12],[10],280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨280,[1,2,3,4,5,6,7,8,9,10,11,12],281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid265 : RecordDataValid section14Catalog 12 (⟨53,(1),[4,8,12],[14],326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨326,[1,2,4,5,6,8,9,10,12],327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid266 : RecordDataValid section14Catalog 12 (⟨53,(1),[12],[6],361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨361,[1,2,3,4,5,6,7,8,9,10,12],362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid267 : RecordDataValid section14Catalog 12 (⟨53,(2),[3,4,7,8,12],[10],281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨281,[1,2,3,4,5,6,7,8,9,10,11,12],282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid268 : RecordDataValid section14Catalog 12 (⟨53,(2),[4,8,12],[14],327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨327,[1,2,4,5,6,8,9,10,12],328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid269 : RecordDataValid section14Catalog 12 (⟨53,(2),[12],[6],362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨362,[1,2,3,4,5,6,7,8,9,10,12],363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid270 : RecordDataValid section14Catalog 12 (⟨53,(3),[3,4,7,8,12],[10],282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨282,[1,2,3,4,5,6,7,8,9,10,11,12],283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid271 : RecordDataValid section14Catalog 12 (⟨53,(3),[4,8,12],[14],328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨328,[1,2,4,5,6,8,9,10,12],329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid272 : RecordDataValid section14Catalog 12 (⟨53,(3),[12],[6],363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨363,[1,2,3,4,5,6,7,8,9,10,12],364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid273 : RecordDataValid section14Catalog 12 (⟨57,(0),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid274 : RecordDataValid section14Catalog 12 (⟨57,(0),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid275 : RecordDataValid section14Catalog 12 (⟨57,(1),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid276 : RecordDataValid section14Catalog 12 (⟨57,(1),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid277 : RecordDataValid section14Catalog 12 (⟨57,(2),[4,8,12],[10],311⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨311,[1,2,4,5,6,8,9,10,12],312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid278 : RecordDataValid section14Catalog 12 (⟨57,(2),[4,8,12],[14],337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨337,[1,2,3,4,5,6,7,8,9,10,11,12],338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid279 : RecordDataValid section14Catalog 12 (⟨57,(2),[12],[6],337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨337,[1,2,3,4,5,6,7,8,9,10,11,12],338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid280 : RecordDataValid section14Catalog 12 (⟨57,(3),[4,8,12],[10,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid281 : RecordDataValid section14Catalog 12 (⟨57,(3),[12],[6],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid282 : RecordDataValid section14Catalog 12 (⟨57,(4),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid283 : RecordDataValid section14Catalog 12 (⟨57,(4),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid284 : RecordDataValid section14Catalog 12 (⟨57,(5),[4,8,12],[10,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid285 : RecordDataValid section14Catalog 12 (⟨57,(5),[12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid286 : RecordDataValid section14Catalog 12 (⟨57,(6),[4,8,12],[10],284⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨284,[1,2,4,5,6,8,9,10,12],285⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid287 : RecordDataValid section14Catalog 12 (⟨57,(6),[4,8,12],[14],338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨338,[1,2,4,5,6,8,9,10,12],339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 256).take 32 = [⟨50,(14),[4,8,12],[14],336⟩,⟨50,(14),[12],[6],336⟩,⟨50,(15),[4,8,12],[10],304⟩,⟨50,(15),[4,8,12],[14],334⟩,⟨50,(15),[12],[6],334⟩,⟨53,(0),[3,4,7,8,12],[10],279⟩,⟨53,(0),[4,8,12],[14],325⟩,⟨53,(0),[12],[6],360⟩,⟨53,(1),[3,4,7,8,12],[10],280⟩,⟨53,(1),[4,8,12],[14],326⟩,⟨53,(1),[12],[6],361⟩,⟨53,(2),[3,4,7,8,12],[10],281⟩,⟨53,(2),[4,8,12],[14],327⟩,⟨53,(2),[12],[6],362⟩,⟨53,(3),[3,4,7,8,12],[10],282⟩,⟨53,(3),[4,8,12],[14],328⟩,⟨53,(3),[12],[6],363⟩,⟨57,(0),[4,8,12],[10,14],2⟩,⟨57,(0),[12],[6],2⟩,⟨57,(1),[4,8,12],[10,14],2⟩,⟨57,(1),[12],[6],2⟩,⟨57,(2),[4,8,12],[10],311⟩,⟨57,(2),[4,8,12],[14],337⟩,⟨57,(2),[12],[6],337⟩,⟨57,(3),[4,8,12],[10,14],101⟩,⟨57,(3),[12],[6],101⟩,⟨57,(4),[4,8,12],[10,14],2⟩,⟨57,(4),[12],[6],2⟩,⟨57,(5),[4,8,12],[10,14],2⟩,⟨57,(5),[12],[6],2⟩,⟨57,(6),[4,8,12],[10],284⟩,⟨57,(6),[4,8,12],[14],338⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid256
  · exact recordValid_of_data section14Catalog 12 _ hnum valid257
  · exact recordValid_of_data section14Catalog 12 _ hnum valid258
  · exact recordValid_of_data section14Catalog 12 _ hnum valid259
  · exact recordValid_of_data section14Catalog 12 _ hnum valid260
  · exact recordValid_of_data section14Catalog 12 _ hnum valid261
  · exact recordValid_of_data section14Catalog 12 _ hnum valid262
  · exact recordValid_of_data section14Catalog 12 _ hnum valid263
  · exact recordValid_of_data section14Catalog 12 _ hnum valid264
  · exact recordValid_of_data section14Catalog 12 _ hnum valid265
  · exact recordValid_of_data section14Catalog 12 _ hnum valid266
  · exact recordValid_of_data section14Catalog 12 _ hnum valid267
  · exact recordValid_of_data section14Catalog 12 _ hnum valid268
  · exact recordValid_of_data section14Catalog 12 _ hnum valid269
  · exact recordValid_of_data section14Catalog 12 _ hnum valid270
  · exact recordValid_of_data section14Catalog 12 _ hnum valid271
  · exact recordValid_of_data section14Catalog 12 _ hnum valid272
  · exact recordValid_of_data section14Catalog 12 _ hnum valid273
  · exact recordValid_of_data section14Catalog 12 _ hnum valid274
  · exact recordValid_of_data section14Catalog 12 _ hnum valid275
  · exact recordValid_of_data section14Catalog 12 _ hnum valid276
  · exact recordValid_of_data section14Catalog 12 _ hnum valid277
  · exact recordValid_of_data section14Catalog 12 _ hnum valid278
  · exact recordValid_of_data section14Catalog 12 _ hnum valid279
  · exact recordValid_of_data section14Catalog 12 _ hnum valid280
  · exact recordValid_of_data section14Catalog 12 _ hnum valid281
  · exact recordValid_of_data section14Catalog 12 _ hnum valid282
  · exact recordValid_of_data section14Catalog 12 _ hnum valid283
  · exact recordValid_of_data section14Catalog 12 _ hnum valid284
  · exact recordValid_of_data section14Catalog 12 _ hnum valid285
  · exact recordValid_of_data section14Catalog 12 _ hnum valid286
  · exact recordValid_of_data section14Catalog 12 _ hnum valid287
end Section14Records_12_256_288

#print axioms solution
