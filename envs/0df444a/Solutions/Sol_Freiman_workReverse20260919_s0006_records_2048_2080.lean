-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2048_2080
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:31:21.845989+00:00
-- url     : https://prove2.me/submissions/81a15e13-00d8-453b-8714-9548e5efb185

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
namespace Section14Records_6_2048_2080
private theorem valid2048 : RecordDataValid section14Catalog 6 (⟨138,(14),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2049 : RecordDataValid section14Catalog 6 (⟨138,(15),[1,5,6,13],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2050 : RecordDataValid section14Catalog 6 (⟨138,(16),[1,5,6,13],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2051 : RecordDataValid section14Catalog 6 (⟨138,(17),[1,5,6,13],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2052 : RecordDataValid section14Catalog 6 (⟨138,(18),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2053 : RecordDataValid section14Catalog 6 (⟨138,(19),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2054 : RecordDataValid section14Catalog 6 (⟨138,(20),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2055 : RecordDataValid section14Catalog 6 (⟨138,(21),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2056 : RecordDataValid section14Catalog 6 (⟨138,(22),[1,5,6,13],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2057 : RecordDataValid section14Catalog 6 (⟨138,(23),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2058 : RecordDataValid section14Catalog 6 (⟨138,(24),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2059 : RecordDataValid section14Catalog 6 (⟨139,(0),[1,5,6,13],[170],548⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨548,[1,4,5,6,8,9,10,12,13,16],549⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2060 : RecordDataValid section14Catalog 6 (⟨139,(1),[1,5,6,13],[170],549⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨549,[1,4,5,6,8,9,10,12,13,16],550⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2061 : RecordDataValid section14Catalog 6 (⟨139,(2),[1,5,6,13],[170],548⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨548,[1,4,5,6,8,9,10,12,13,16],549⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2062 : RecordDataValid section14Catalog 6 (⟨139,(3),[1,5,6,13],[170],550⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨550,[1,4,5,6,8,9,10,12,13,16],551⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2063 : RecordDataValid section14Catalog 6 (⟨139,(4),[1,5,6,13],[170],551⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨551,[1,4,5,6,8,9,10,12,13,16],552⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2064 : RecordDataValid section14Catalog 6 (⟨139,(5),[1,5,6,13],[170],552⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨552,[1,4,5,6,9,10,13,16],553⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2065 : RecordDataValid section14Catalog 6 (⟨139,(6),[1,5,6,13],[170],553⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨553,[1,4,5,6,9,10,13,16],554⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2066 : RecordDataValid section14Catalog 6 (⟨139,(7),[1,5,6,13],[170],554⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨554,[1,4,5,6,9,10,13,16],555⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2067 : RecordDataValid section14Catalog 6 (⟨139,(8),[1,5,6,13],[170],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2068 : RecordDataValid section14Catalog 6 (⟨139,(9),[1,5,6,13],[170],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2069 : RecordDataValid section14Catalog 6 (⟨139,(10),[1,5,6,13],[170],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2070 : RecordDataValid section14Catalog 6 (⟨139,(11),[1,5,6,13],[170],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2071 : RecordDataValid section14Catalog 6 (⟨139,(12),[1,5,6,13],[170],559⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨559,[1,4,5,6,8,9,10,12,13,16],560⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2072 : RecordDataValid section14Catalog 6 (⟨139,(13),[1,5,6,13],[170],560⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨560,[1,4,5,6,8,9,10,12,13,16],561⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2073 : RecordDataValid section14Catalog 6 (⟨139,(14),[1,5,6,13],[170],561⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨561,[1,4,5,6,8,9,10,12,13,16],562⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2074 : RecordDataValid section14Catalog 6 (⟨139,(15),[1,5,6,13],[170],562⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨562,[1,4,5,6,8,9,10,12,13,16],563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2075 : RecordDataValid section14Catalog 6 (⟨139,(16),[1,5,6,13],[170],555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨555,[1,4,5,6,8,9,10,12,13,16],556⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2076 : RecordDataValid section14Catalog 6 (⟨139,(17),[1,5,6,13],[170],556⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨556,[1,4,5,6,8,9,10,12,13,16],557⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2077 : RecordDataValid section14Catalog 6 (⟨139,(18),[1,5,6,13],[170],557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨557,[1,4,5,6,8,9,10,12,13,16],558⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2078 : RecordDataValid section14Catalog 6 (⟨139,(19),[1,5,6,13],[170],558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨558,[1,4,5,6,8,9,10,12,13,16],559⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2079 : RecordDataValid section14Catalog 6 (⟨140,(0),[1,5,6,13],[170],563⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨563,[1,4,5,6,8,9,10,12,13,16],564⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2048).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2048).take 32 = [⟨138,(14),[1,5,6,13],[170],518⟩,⟨138,(15),[1,5,6,13],[170],546⟩,⟨138,(16),[1,5,6,13],[170],546⟩,⟨138,(17),[1,5,6,13],[170],544⟩,⟨138,(18),[1,5,6,13],[170],517⟩,⟨138,(19),[1,5,6,13],[170],518⟩,⟨138,(20),[1,5,6,13],[170],547⟩,⟨138,(21),[1,5,6,13],[170],547⟩,⟨138,(22),[1,5,6,13],[170],547⟩,⟨138,(23),[1,5,6,13],[170],517⟩,⟨138,(24),[1,5,6,13],[170],518⟩,⟨139,(0),[1,5,6,13],[170],548⟩,⟨139,(1),[1,5,6,13],[170],549⟩,⟨139,(2),[1,5,6,13],[170],548⟩,⟨139,(3),[1,5,6,13],[170],550⟩,⟨139,(4),[1,5,6,13],[170],551⟩,⟨139,(5),[1,5,6,13],[170],552⟩,⟨139,(6),[1,5,6,13],[170],553⟩,⟨139,(7),[1,5,6,13],[170],554⟩,⟨139,(8),[1,5,6,13],[170],555⟩,⟨139,(9),[1,5,6,13],[170],556⟩,⟨139,(10),[1,5,6,13],[170],557⟩,⟨139,(11),[1,5,6,13],[170],558⟩,⟨139,(12),[1,5,6,13],[170],559⟩,⟨139,(13),[1,5,6,13],[170],560⟩,⟨139,(14),[1,5,6,13],[170],561⟩,⟨139,(15),[1,5,6,13],[170],562⟩,⟨139,(16),[1,5,6,13],[170],555⟩,⟨139,(17),[1,5,6,13],[170],556⟩,⟨139,(18),[1,5,6,13],[170],557⟩,⟨139,(19),[1,5,6,13],[170],558⟩,⟨140,(0),[1,5,6,13],[170],563⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2048
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2049
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2050
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2051
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2052
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2053
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2054
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2055
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2056
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2057
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2058
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2059
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2060
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2061
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2062
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2063
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2064
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2065
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2066
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2067
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2068
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2069
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2070
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2071
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2072
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2073
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2074
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2075
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2076
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2077
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2078
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2079
end Section14Records_6_2048_2080

#print axioms solution
