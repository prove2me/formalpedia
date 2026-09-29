-- Prove2me | solution 1 for Freiman.section14_s0010_records_2176_2208
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:57:09.330443+00:00
-- url     : https://prove2.me/submissions/6772e453-bb7b-4346-8e77-de977114bf0a

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
namespace Section14Records_10_2176_2208
private theorem valid2176 : RecordDataValid section14Catalog 10 (⟨230,(14),[10],[42],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2177 : RecordDataValid section14Catalog 10 (⟨230,(15),[9,10],[42],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2178 : RecordDataValid section14Catalog 10 (⟨230,(16),[9,10],[42],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2179 : RecordDataValid section14Catalog 10 (⟨230,(17),[10],[42],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2180 : RecordDataValid section14Catalog 10 (⟨230,(18),[9,10],[42],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2181 : RecordDataValid section14Catalog 10 (⟨230,(19),[10],[42],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2182 : RecordDataValid section14Catalog 10 (⟨230,(20),[9,10],[42],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2183 : RecordDataValid section14Catalog 10 (⟨230,(21),[9,10],[42],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2184 : RecordDataValid section14Catalog 10 (⟨230,(22),[10],[42],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2185 : RecordDataValid section14Catalog 10 (⟨230,(23),[9,10],[42],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2186 : RecordDataValid section14Catalog 10 (⟨230,(24),[10],[42],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2187 : RecordDataValid section14Catalog 10 (⟨231,(0),[9,10],[42],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2188 : RecordDataValid section14Catalog 10 (⟨231,(1),[10],[42],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2189 : RecordDataValid section14Catalog 10 (⟨231,(2),[9,10],[42],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2190 : RecordDataValid section14Catalog 10 (⟨231,(3),[9,10],[42],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2191 : RecordDataValid section14Catalog 10 (⟨231,(4),[9,10],[42],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2192 : RecordDataValid section14Catalog 10 (⟨231,(5),[10],[42],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2193 : RecordDataValid section14Catalog 10 (⟨231,(6),[9,10],[42],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2194 : RecordDataValid section14Catalog 10 (⟨231,(7),[9,10],[42],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2195 : RecordDataValid section14Catalog 10 (⟨231,(8),[9,10],[42],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2196 : RecordDataValid section14Catalog 10 (⟨231,(9),[9,10],[42],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2197 : RecordDataValid section14Catalog 10 (⟨231,(10),[9,10],[42],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2198 : RecordDataValid section14Catalog 10 (⟨231,(11),[9,10],[42],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2199 : RecordDataValid section14Catalog 10 (⟨231,(12),[9,10],[42],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2200 : RecordDataValid section14Catalog 10 (⟨231,(13),[9,10],[42],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2201 : RecordDataValid section14Catalog 10 (⟨231,(14),[9,10],[42],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2202 : RecordDataValid section14Catalog 10 (⟨231,(15),[9,10],[42],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2203 : RecordDataValid section14Catalog 10 (⟨231,(16),[9,10],[42],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2204 : RecordDataValid section14Catalog 10 (⟨231,(17),[9,10],[42],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2205 : RecordDataValid section14Catalog 10 (⟨231,(18),[9,10],[42],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2206 : RecordDataValid section14Catalog 10 (⟨231,(19),[9,10],[42],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2207 : RecordDataValid section14Catalog 10 (⟨232,(0),[9,10],[42],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2176).take 32 = [⟨230,(14),[10],[42],817⟩,⟨230,(15),[9,10],[42],822⟩,⟨230,(16),[9,10],[42],823⟩,⟨230,(17),[10],[42],824⟩,⟨230,(18),[9,10],[42],825⟩,⟨230,(19),[10],[42],824⟩,⟨230,(20),[9,10],[42],826⟩,⟨230,(21),[9,10],[42],827⟩,⟨230,(22),[10],[42],828⟩,⟨230,(23),[9,10],[42],829⟩,⟨230,(24),[10],[42],828⟩,⟨231,(0),[9,10],[42],830⟩,⟨231,(1),[10],[42],831⟩,⟨231,(2),[9,10],[42],832⟩,⟨231,(3),[9,10],[42],833⟩,⟨231,(4),[9,10],[42],830⟩,⟨231,(5),[10],[42],831⟩,⟨231,(6),[9,10],[42],832⟩,⟨231,(7),[9,10],[42],833⟩,⟨231,(8),[9,10],[42],834⟩,⟨231,(9),[9,10],[42],835⟩,⟨231,(10),[9,10],[42],836⟩,⟨231,(11),[9,10],[42],837⟩,⟨231,(12),[9,10],[42],838⟩,⟨231,(13),[9,10],[42],839⟩,⟨231,(14),[9,10],[42],838⟩,⟨231,(15),[9,10],[42],840⟩,⟨231,(16),[9,10],[42],841⟩,⟨231,(17),[9,10],[42],842⟩,⟨231,(18),[9,10],[42],841⟩,⟨231,(19),[9,10],[42],843⟩,⟨232,(0),[9,10],[42],844⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2176
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2177
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2178
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2179
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2180
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2181
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2182
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2183
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2184
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2185
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2186
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2187
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2188
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2189
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2190
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2191
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2192
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2193
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2194
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2195
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2196
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2197
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2198
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2199
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2200
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2201
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2202
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2203
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2204
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2205
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2206
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2207
end Section14Records_10_2176_2208

#print axioms solution
