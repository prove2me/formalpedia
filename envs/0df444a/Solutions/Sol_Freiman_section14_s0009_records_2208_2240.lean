-- Prove2me | solution 1 for Freiman.section14_s0009_records_2208_2240
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:19:41.419986+00:00
-- url     : https://prove2.me/submissions/3d361762-9432-4086-aceb-9619f8e06428

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
namespace Section14Records_9_2208_2240
private theorem valid2208 : RecordDataValid section14Catalog 9 (⟨231,(11),[9,10],[42],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2209 : RecordDataValid section14Catalog 9 (⟨231,(12),[9,10],[42],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2210 : RecordDataValid section14Catalog 9 (⟨231,(13),[9,10],[42],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2211 : RecordDataValid section14Catalog 9 (⟨231,(14),[9,10],[42],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2212 : RecordDataValid section14Catalog 9 (⟨231,(15),[9,10],[42],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2213 : RecordDataValid section14Catalog 9 (⟨231,(16),[9,10],[42],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2214 : RecordDataValid section14Catalog 9 (⟨231,(17),[9,10],[42],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2215 : RecordDataValid section14Catalog 9 (⟨231,(18),[9,10],[42],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2216 : RecordDataValid section14Catalog 9 (⟨231,(19),[9,10],[42],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2217 : RecordDataValid section14Catalog 9 (⟨232,(0),[9,10],[42],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2218 : RecordDataValid section14Catalog 9 (⟨232,(1),[9,10],[42],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2219 : RecordDataValid section14Catalog 9 (⟨232,(2),[9,10],[42],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2220 : RecordDataValid section14Catalog 9 (⟨232,(3),[9,10],[42],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2221 : RecordDataValid section14Catalog 9 (⟨232,(4),[9,10],[42],848⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2222 : RecordDataValid section14Catalog 9 (⟨232,(5),[9,10],[42],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2223 : RecordDataValid section14Catalog 9 (⟨232,(6),[9,10],[42],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2224 : RecordDataValid section14Catalog 9 (⟨232,(7),[9,10],[42],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2225 : RecordDataValid section14Catalog 9 (⟨232,(8),[9,10],[42],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2226 : RecordDataValid section14Catalog 9 (⟨232,(9),[9],[42],1378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1378,[4,8,9,12,16],1382⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2227 : RecordDataValid section14Catalog 9 (⟨232,(10),[9,10],[42],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2228 : RecordDataValid section14Catalog 9 (⟨232,(11),[9,10],[42],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2229 : RecordDataValid section14Catalog 9 (⟨232,(12),[9,10],[42],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2230 : RecordDataValid section14Catalog 9 (⟨232,(13),[9,10],[42],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2231 : RecordDataValid section14Catalog 9 (⟨232,(14),[9],[42],1379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1379,[4,8,9,12,16],1383⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2232 : RecordDataValid section14Catalog 9 (⟨232,(15),[9,10],[42],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2233 : RecordDataValid section14Catalog 9 (⟨232,(16),[9,10],[42],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2234 : RecordDataValid section14Catalog 9 (⟨232,(17),[9,10],[42],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2235 : RecordDataValid section14Catalog 9 (⟨232,(18),[9,10],[42],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2236 : RecordDataValid section14Catalog 9 (⟨232,(19),[9],[42],1380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1380,[4,8,9,12,16],1384⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2237 : RecordDataValid section14Catalog 9 (⟨234,(0),[9,10],[42],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2238 : RecordDataValid section14Catalog 9 (⟨234,(1),[9],[42],1381⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1381,[4,8,9,12,16],1385⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2239 : RecordDataValid section14Catalog 9 (⟨234,(2),[9],[42],1382⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1382,[4,8,9,12,16],1386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2208).take 32 = [⟨231,(11),[9,10],[42],837⟩,⟨231,(12),[9,10],[42],838⟩,⟨231,(13),[9,10],[42],839⟩,⟨231,(14),[9,10],[42],838⟩,⟨231,(15),[9,10],[42],840⟩,⟨231,(16),[9,10],[42],841⟩,⟨231,(17),[9,10],[42],842⟩,⟨231,(18),[9,10],[42],841⟩,⟨231,(19),[9,10],[42],843⟩,⟨232,(0),[9,10],[42],844⟩,⟨232,(1),[9,10],[42],845⟩,⟨232,(2),[9,10],[42],846⟩,⟨232,(3),[9,10],[42],847⟩,⟨232,(4),[9,10],[42],848⟩,⟨232,(5),[9,10],[42],849⟩,⟨232,(6),[9,10],[42],850⟩,⟨232,(7),[9,10],[42],851⟩,⟨232,(8),[9,10],[42],852⟩,⟨232,(9),[9],[42],1378⟩,⟨232,(10),[9,10],[42],844⟩,⟨232,(11),[9,10],[42],854⟩,⟨232,(12),[9,10],[42],846⟩,⟨232,(13),[9,10],[42],847⟩,⟨232,(14),[9],[42],1379⟩,⟨232,(15),[9,10],[42],856⟩,⟨232,(16),[9,10],[42],857⟩,⟨232,(17),[9,10],[42],858⟩,⟨232,(18),[9,10],[42],859⟩,⟨232,(19),[9],[42],1380⟩,⟨234,(0),[9,10],[42],568⟩,⟨234,(1),[9],[42],1381⟩,⟨234,(2),[9],[42],1382⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2208
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2209
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2210
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2211
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2212
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2213
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2214
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2215
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2216
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2217
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2218
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2219
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2220
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2221
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2222
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2223
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2224
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2225
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2226
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2227
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2228
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2229
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2230
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2231
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2232
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2233
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2234
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2235
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2236
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2237
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2238
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2239
end Section14Records_9_2208_2240

#print axioms solution
