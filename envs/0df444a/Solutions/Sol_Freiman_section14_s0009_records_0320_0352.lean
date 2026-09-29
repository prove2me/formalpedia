-- Prove2me | solution 1 for Freiman.section14_s0009_records_0320_0352
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:01:25.085272+00:00
-- url     : https://prove2.me/submissions/ba662af5-df64-4e0e-8091-6964ab6dc12e

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
namespace Section14Records_9_320_352
private theorem valid320 : RecordDataValid section14Catalog 9 (⟨28,(12),[9,10],[35],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid321 : RecordDataValid section14Catalog 9 (⟨28,(12),[9,10],[38],178⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨178,[1,5,9,10],178⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid322 : RecordDataValid section14Catalog 9 (⟨28,(13),[9],[34],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid323 : RecordDataValid section14Catalog 9 (⟨28,(13),[9,10],[35],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid324 : RecordDataValid section14Catalog 9 (⟨28,(13),[9,10],[38],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid325 : RecordDataValid section14Catalog 9 (⟨28,(14),[9],[34],90⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨90,[1,5,9],90⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid326 : RecordDataValid section14Catalog 9 (⟨28,(14),[9,10],[35],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid327 : RecordDataValid section14Catalog 9 (⟨28,(14),[9,10],[38],179⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨179,[1,5,9,10],179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid328 : RecordDataValid section14Catalog 9 (⟨28,(15),[9],[34],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid329 : RecordDataValid section14Catalog 9 (⟨28,(15),[9,10],[35],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid330 : RecordDataValid section14Catalog 9 (⟨28,(15),[9,10],[38],176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨176,[1,5,9,10],176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid331 : RecordDataValid section14Catalog 9 (⟨28,(16),[9],[34],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid332 : RecordDataValid section14Catalog 9 (⟨28,(16),[9,10],[35],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid333 : RecordDataValid section14Catalog 9 (⟨28,(16),[9,10],[38],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid334 : RecordDataValid section14Catalog 9 (⟨28,(17),[9],[34],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid335 : RecordDataValid section14Catalog 9 (⟨28,(17),[9,10],[35],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid336 : RecordDataValid section14Catalog 9 (⟨28,(17),[9,10],[38],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid337 : RecordDataValid section14Catalog 9 (⟨28,(18),[9],[34],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid338 : RecordDataValid section14Catalog 9 (⟨28,(18),[9,10],[35],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid339 : RecordDataValid section14Catalog 9 (⟨28,(18),[9,10],[38],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid340 : RecordDataValid section14Catalog 9 (⟨28,(19),[9],[34],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid341 : RecordDataValid section14Catalog 9 (⟨28,(19),[9,10],[35],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid342 : RecordDataValid section14Catalog 9 (⟨28,(19),[9,10],[38],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid343 : RecordDataValid section14Catalog 9 (⟨28,(20),[9],[34],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid344 : RecordDataValid section14Catalog 9 (⟨28,(20),[9,10],[35],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid345 : RecordDataValid section14Catalog 9 (⟨28,(20),[9,10],[38],176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨176,[1,5,9,10],176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid346 : RecordDataValid section14Catalog 9 (⟨28,(21),[9],[34],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid347 : RecordDataValid section14Catalog 9 (⟨28,(21),[9,10],[35],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid348 : RecordDataValid section14Catalog 9 (⟨28,(21),[9,10],[38],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid349 : RecordDataValid section14Catalog 9 (⟨28,(22),[9],[34],89⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨89,[1,5,9],89⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid350 : RecordDataValid section14Catalog 9 (⟨28,(22),[9,10],[35],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid351 : RecordDataValid section14Catalog 9 (⟨28,(22),[9,10],[38],178⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨178,[1,5,9,10],178⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 320).take 32 = [⟨28,(12),[9,10],[35],117⟩,⟨28,(12),[9,10],[38],178⟩,⟨28,(13),[9],[34],88⟩,⟨28,(13),[9,10],[35],116⟩,⟨28,(13),[9,10],[38],177⟩,⟨28,(14),[9],[34],90⟩,⟨28,(14),[9,10],[35],118⟩,⟨28,(14),[9,10],[38],179⟩,⟨28,(15),[9],[34],87⟩,⟨28,(15),[9,10],[35],115⟩,⟨28,(15),[9,10],[38],176⟩,⟨28,(16),[9],[34],91⟩,⟨28,(16),[9,10],[35],119⟩,⟨28,(16),[9,10],[38],180⟩,⟨28,(17),[9],[34],91⟩,⟨28,(17),[9,10],[35],119⟩,⟨28,(17),[9,10],[38],180⟩,⟨28,(18),[9],[34],91⟩,⟨28,(18),[9,10],[35],119⟩,⟨28,(18),[9,10],[38],180⟩,⟨28,(19),[9],[34],91⟩,⟨28,(19),[9,10],[35],119⟩,⟨28,(19),[9,10],[38],180⟩,⟨28,(20),[9],[34],87⟩,⟨28,(20),[9,10],[35],115⟩,⟨28,(20),[9,10],[38],176⟩,⟨28,(21),[9],[34],88⟩,⟨28,(21),[9,10],[35],116⟩,⟨28,(21),[9,10],[38],177⟩,⟨28,(22),[9],[34],89⟩,⟨28,(22),[9,10],[35],117⟩,⟨28,(22),[9,10],[38],178⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid320
  · exact recordValid_of_data section14Catalog 9 _ hnum valid321
  · exact recordValid_of_data section14Catalog 9 _ hnum valid322
  · exact recordValid_of_data section14Catalog 9 _ hnum valid323
  · exact recordValid_of_data section14Catalog 9 _ hnum valid324
  · exact recordValid_of_data section14Catalog 9 _ hnum valid325
  · exact recordValid_of_data section14Catalog 9 _ hnum valid326
  · exact recordValid_of_data section14Catalog 9 _ hnum valid327
  · exact recordValid_of_data section14Catalog 9 _ hnum valid328
  · exact recordValid_of_data section14Catalog 9 _ hnum valid329
  · exact recordValid_of_data section14Catalog 9 _ hnum valid330
  · exact recordValid_of_data section14Catalog 9 _ hnum valid331
  · exact recordValid_of_data section14Catalog 9 _ hnum valid332
  · exact recordValid_of_data section14Catalog 9 _ hnum valid333
  · exact recordValid_of_data section14Catalog 9 _ hnum valid334
  · exact recordValid_of_data section14Catalog 9 _ hnum valid335
  · exact recordValid_of_data section14Catalog 9 _ hnum valid336
  · exact recordValid_of_data section14Catalog 9 _ hnum valid337
  · exact recordValid_of_data section14Catalog 9 _ hnum valid338
  · exact recordValid_of_data section14Catalog 9 _ hnum valid339
  · exact recordValid_of_data section14Catalog 9 _ hnum valid340
  · exact recordValid_of_data section14Catalog 9 _ hnum valid341
  · exact recordValid_of_data section14Catalog 9 _ hnum valid342
  · exact recordValid_of_data section14Catalog 9 _ hnum valid343
  · exact recordValid_of_data section14Catalog 9 _ hnum valid344
  · exact recordValid_of_data section14Catalog 9 _ hnum valid345
  · exact recordValid_of_data section14Catalog 9 _ hnum valid346
  · exact recordValid_of_data section14Catalog 9 _ hnum valid347
  · exact recordValid_of_data section14Catalog 9 _ hnum valid348
  · exact recordValid_of_data section14Catalog 9 _ hnum valid349
  · exact recordValid_of_data section14Catalog 9 _ hnum valid350
  · exact recordValid_of_data section14Catalog 9 _ hnum valid351
end Section14Records_9_320_352

#print axioms solution
