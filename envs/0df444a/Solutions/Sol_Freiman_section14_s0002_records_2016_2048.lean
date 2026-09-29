-- Prove2me | solution 1 for Freiman.section14_s0002_records_2016_2048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T06:49:13.689782+00:00
-- url     : https://prove2.me/submissions/3a99c5b1-565f-4a4a-ac02-00e0de6ea6f5

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
namespace Section14Records_2_2016_2048
private theorem valid2016 : RecordDataValid section14Catalog 2 (⟨200,(7),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2017 : RecordDataValid section14Catalog 2 (⟨200,(8),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2018 : RecordDataValid section14Catalog 2 (⟨200,(9),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2019 : RecordDataValid section14Catalog 2 (⟨200,(10),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2020 : RecordDataValid section14Catalog 2 (⟨200,(11),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2021 : RecordDataValid section14Catalog 2 (⟨200,(12),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2022 : RecordDataValid section14Catalog 2 (⟨200,(13),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2023 : RecordDataValid section14Catalog 2 (⟨200,(14),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2024 : RecordDataValid section14Catalog 2 (⟨200,(15),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2025 : RecordDataValid section14Catalog 2 (⟨200,(16),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2026 : RecordDataValid section14Catalog 2 (⟨200,(17),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2027 : RecordDataValid section14Catalog 2 (⟨200,(18),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2028 : RecordDataValid section14Catalog 2 (⟨200,(19),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2029 : RecordDataValid section14Catalog 2 (⟨200,(20),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2030 : RecordDataValid section14Catalog 2 (⟨200,(21),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2031 : RecordDataValid section14Catalog 2 (⟨200,(22),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2032 : RecordDataValid section14Catalog 2 (⟨200,(23),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2033 : RecordDataValid section14Catalog 2 (⟨200,(24),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2034 : RecordDataValid section14Catalog 2 (⟨202,(0),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2035 : RecordDataValid section14Catalog 2 (⟨202,(1),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2036 : RecordDataValid section14Catalog 2 (⟨202,(2),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2037 : RecordDataValid section14Catalog 2 (⟨202,(3),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2038 : RecordDataValid section14Catalog 2 (⟨202,(4),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2039 : RecordDataValid section14Catalog 2 (⟨202,(5),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2040 : RecordDataValid section14Catalog 2 (⟨202,(6),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2041 : RecordDataValid section14Catalog 2 (⟨202,(7),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2042 : RecordDataValid section14Catalog 2 (⟨202,(8),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2043 : RecordDataValid section14Catalog 2 (⟨202,(9),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2044 : RecordDataValid section14Catalog 2 (⟨202,(10),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2045 : RecordDataValid section14Catalog 2 (⟨202,(11),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2046 : RecordDataValid section14Catalog 2 (⟨202,(12),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2047 : RecordDataValid section14Catalog 2 (⟨202,(13),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2016).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2016).take 32 = [⟨200,(7),[1,2,5,6,13,14],[170],705⟩,⟨200,(8),[1,2,5,6,13,14],[170],705⟩,⟨200,(9),[1,2,5,6,13,14],[170],705⟩,⟨200,(10),[1,2,5,6,13,14],[170],706⟩,⟨200,(11),[1,2,5,6,13,14],[170],707⟩,⟨200,(12),[1,2,5,6,13,14],[170],708⟩,⟨200,(13),[1,2,5,6,13,14],[170],707⟩,⟨200,(14),[1,2,5,6,13,14],[170],709⟩,⟨200,(15),[1,2,5,6,13,14],[170],706⟩,⟨200,(16),[1,2,5,6,13,14],[170],710⟩,⟨200,(17),[1,2,5,6,13,14],[170],710⟩,⟨200,(18),[1,2,5,6,13,14],[170],710⟩,⟨200,(19),[1,2,5,6,13,14],[170],710⟩,⟨200,(20),[1,2,5,6,13,14],[170],706⟩,⟨200,(21),[1,2,5,6,13,14],[170],707⟩,⟨200,(22),[1,2,5,6,13,14],[170],708⟩,⟨200,(23),[1,2,5,6,13,14],[170],707⟩,⟨200,(24),[1,2,5,6,13,14],[170],709⟩,⟨202,(0),[1,2,5,6,13,14],[170],467⟩,⟨202,(1),[1,2,5,6,13,14],[170],468⟩,⟨202,(2),[1,2,5,6,13,14],[170],467⟩,⟨202,(3),[1,2,5,6,13,14],[170],469⟩,⟨202,(4),[1,2,5,6,13,14],[170],470⟩,⟨202,(5),[1,2,5,6,13,14],[170],467⟩,⟨202,(6),[1,2,5,6,13,14],[170],468⟩,⟨202,(7),[1,2,5,6,13,14],[170],467⟩,⟨202,(8),[1,2,5,6,13,14],[170],469⟩,⟨202,(9),[1,2,5,6,13,14],[170],470⟩,⟨202,(10),[1,2,5,6,13,14],[170],471⟩,⟨202,(11),[1,2,5,6,13,14],[170],471⟩,⟨202,(12),[1,2,5,6,13,14],[170],471⟩,⟨202,(13),[1,2,5,6,13,14],[170],471⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2016
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2017
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2018
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2019
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2020
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2021
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2022
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2023
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2024
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2025
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2026
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2027
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2028
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2029
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2030
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2031
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2032
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2033
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2034
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2035
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2036
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2037
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2038
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2039
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2040
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2041
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2042
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2043
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2044
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2045
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2046
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2047
end Section14Records_2_2016_2048

#print axioms solution
