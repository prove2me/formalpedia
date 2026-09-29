-- Prove2me | solution 1 for Freiman.section14_s0015_records_0320_0352
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:49:29.272462+00:00
-- url     : https://prove2.me/submissions/15433ac0-4e3e-4f83-91c0-302191b31c78

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
namespace Section14Records_15_320_352
private theorem valid320 : RecordDataValid section14Catalog 15 (⟨58,(19),[15],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid321 : RecordDataValid section14Catalog 15 (⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid322 : RecordDataValid section14Catalog 15 (⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid323 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid324 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,7,15],[2],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid325 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,7,15],[6],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid326 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,7,15],[14],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid327 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,7,15],[4],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid328 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,7,15],[8],346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨346,[1,2,3,5,6,7,13,14,15],347⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid329 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,7,15],[10],367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨367,[1,2,3,5,6,7,13,14,15],368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid330 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,7,15],[12,13],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid331 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,15],[3],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid332 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,15],[7],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid333 : RecordDataValid section14Catalog 15 (⟨60,(-1),[3,15],[15],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid334 : RecordDataValid section14Catalog 15 (⟨60,(-1),[15],[9],1728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1728,[13,14,15,16],1733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid335 : RecordDataValid section14Catalog 15 (⟨64,(0),[3,7,15],[11],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid336 : RecordDataValid section14Catalog 15 (⟨64,(1),[3,7,15],[11],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid337 : RecordDataValid section14Catalog 15 (⟨64,(2),[3,7,15],[11],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid338 : RecordDataValid section14Catalog 15 (⟨64,(3),[3,7,15],[11],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid339 : RecordDataValid section14Catalog 15 (⟨64,(4),[3,7,15],[11],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid340 : RecordDataValid section14Catalog 15 (⟨64,(5),[3,7,15],[11],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid341 : RecordDataValid section14Catalog 15 (⟨64,(6),[3,7,15],[11],369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨369,[1,2,3,4,5,6,7,8,13,14,15,16],370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid342 : RecordDataValid section14Catalog 15 (⟨64,(7),[3,7,15],[11],368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨368,[1,2,3,4,5,6,7,8,13,14,15,16],369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid343 : RecordDataValid section14Catalog 15 (⟨64,(8),[3,7,15],[11],370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨370,[1,2,3,4,5,6,7,8,13,14,15,16],371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid344 : RecordDataValid section14Catalog 15 (⟨64,(9),[3,7,15],[11],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid345 : RecordDataValid section14Catalog 15 (⟨64,(10),[3,7,15],[11],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid346 : RecordDataValid section14Catalog 15 (⟨64,(11),[3,7,15],[11],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid347 : RecordDataValid section14Catalog 15 (⟨64,(12),[3,7,15],[11],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid348 : RecordDataValid section14Catalog 15 (⟨64,(13),[3,7,15],[11],372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨372,[1,2,3,4,5,6,7,8,13,14,15,16],373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid349 : RecordDataValid section14Catalog 15 (⟨64,(14),[3,7,15],[11],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid350 : RecordDataValid section14Catalog 15 (⟨64,(15),[3,7,15],[11],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid351 : RecordDataValid section14Catalog 15 (⟨64,(16),[3,7,15],[11],373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨373,[1,2,3,4,5,6,7,8,13,14,15,16],374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 320).take 32 = [⟨58,(19),[15],[10],143⟩,⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩,⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩,⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩,⟨60,(-1),[3,7,15],[2],60⟩,⟨60,(-1),[3,7,15],[6],68⟩,⟨60,(-1),[3,7,15],[14],243⟩,⟨60,(-1),[3,7,15],[4],343⟩,⟨60,(-1),[3,7,15],[8],346⟩,⟨60,(-1),[3,7,15],[10],367⟩,⟨60,(-1),[3,7,15],[12,13],385⟩,⟨60,(-1),[3,15],[3],341⟩,⟨60,(-1),[3,15],[7],343⟩,⟨60,(-1),[3,15],[15],385⟩,⟨60,(-1),[15],[9],1728⟩,⟨64,(0),[3,7,15],[11],368⟩,⟨64,(1),[3,7,15],[11],369⟩,⟨64,(2),[3,7,15],[11],368⟩,⟨64,(3),[3,7,15],[11],370⟩,⟨64,(4),[3,7,15],[11],371⟩,⟨64,(5),[3,7,15],[11],368⟩,⟨64,(6),[3,7,15],[11],369⟩,⟨64,(7),[3,7,15],[11],368⟩,⟨64,(8),[3,7,15],[11],370⟩,⟨64,(9),[3,7,15],[11],371⟩,⟨64,(10),[3,7,15],[11],372⟩,⟨64,(11),[3,7,15],[11],372⟩,⟨64,(12),[3,7,15],[11],372⟩,⟨64,(13),[3,7,15],[11],372⟩,⟨64,(14),[3,7,15],[11],371⟩,⟨64,(15),[3,7,15],[11],373⟩,⟨64,(16),[3,7,15],[11],373⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid320
  · exact recordValid_of_data section14Catalog 15 _ hnum valid321
  · exact recordValid_of_data section14Catalog 15 _ hnum valid322
  · exact recordValid_of_data section14Catalog 15 _ hnum valid323
  · exact recordValid_of_data section14Catalog 15 _ hnum valid324
  · exact recordValid_of_data section14Catalog 15 _ hnum valid325
  · exact recordValid_of_data section14Catalog 15 _ hnum valid326
  · exact recordValid_of_data section14Catalog 15 _ hnum valid327
  · exact recordValid_of_data section14Catalog 15 _ hnum valid328
  · exact recordValid_of_data section14Catalog 15 _ hnum valid329
  · exact recordValid_of_data section14Catalog 15 _ hnum valid330
  · exact recordValid_of_data section14Catalog 15 _ hnum valid331
  · exact recordValid_of_data section14Catalog 15 _ hnum valid332
  · exact recordValid_of_data section14Catalog 15 _ hnum valid333
  · exact recordValid_of_data section14Catalog 15 _ hnum valid334
  · exact recordValid_of_data section14Catalog 15 _ hnum valid335
  · exact recordValid_of_data section14Catalog 15 _ hnum valid336
  · exact recordValid_of_data section14Catalog 15 _ hnum valid337
  · exact recordValid_of_data section14Catalog 15 _ hnum valid338
  · exact recordValid_of_data section14Catalog 15 _ hnum valid339
  · exact recordValid_of_data section14Catalog 15 _ hnum valid340
  · exact recordValid_of_data section14Catalog 15 _ hnum valid341
  · exact recordValid_of_data section14Catalog 15 _ hnum valid342
  · exact recordValid_of_data section14Catalog 15 _ hnum valid343
  · exact recordValid_of_data section14Catalog 15 _ hnum valid344
  · exact recordValid_of_data section14Catalog 15 _ hnum valid345
  · exact recordValid_of_data section14Catalog 15 _ hnum valid346
  · exact recordValid_of_data section14Catalog 15 _ hnum valid347
  · exact recordValid_of_data section14Catalog 15 _ hnum valid348
  · exact recordValid_of_data section14Catalog 15 _ hnum valid349
  · exact recordValid_of_data section14Catalog 15 _ hnum valid350
  · exact recordValid_of_data section14Catalog 15 _ hnum valid351
end Section14Records_15_320_352

#print axioms solution
