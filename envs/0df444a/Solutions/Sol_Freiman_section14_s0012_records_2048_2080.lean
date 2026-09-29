-- Prove2me | solution 1 for Freiman.section14_s0012_records_2048_2080
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:20:02.464989+00:00
-- url     : https://prove2.me/submissions/e9bdd7fd-1ac2-498a-82a3-cc96acb41e7d

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
namespace Section14Records_12_2048_2080
private theorem valid2048 : RecordDataValid section14Catalog 12 (⟨300,(9),[8,12],[10],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2049 : RecordDataValid section14Catalog 12 (⟨300,(10),[8,12],[10],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2050 : RecordDataValid section14Catalog 12 (⟨300,(11),[8,12],[10],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2051 : RecordDataValid section14Catalog 12 (⟨300,(12),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2052 : RecordDataValid section14Catalog 12 (⟨300,(13),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2053 : RecordDataValid section14Catalog 12 (⟨300,(14),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2054 : RecordDataValid section14Catalog 12 (⟨300,(15),[8,12],[10],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2055 : RecordDataValid section14Catalog 12 (⟨302,(0),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2056 : RecordDataValid section14Catalog 12 (⟨302,(1),[8,12],[10],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2057 : RecordDataValid section14Catalog 12 (⟨302,(2),[8,12],[10],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2058 : RecordDataValid section14Catalog 12 (⟨302,(3),[8,12],[10],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2059 : RecordDataValid section14Catalog 12 (⟨302,(4),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2060 : RecordDataValid section14Catalog 12 (⟨302,(5),[8,12],[10],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2061 : RecordDataValid section14Catalog 12 (⟨302,(6),[8,12],[10],1467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1467,[5,8,9,12],1472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2062 : RecordDataValid section14Catalog 12 (⟨302,(7),[8,12],[10],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2063 : RecordDataValid section14Catalog 12 (⟨302,(8),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2064 : RecordDataValid section14Catalog 12 (⟨302,(9),[8,12],[10],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2065 : RecordDataValid section14Catalog 12 (⟨302,(10),[8,12],[10],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2066 : RecordDataValid section14Catalog 12 (⟨302,(11),[8,12],[10],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2067 : RecordDataValid section14Catalog 12 (⟨302,(12),[8,12],[10],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2068 : RecordDataValid section14Catalog 12 (⟨302,(13),[8,12],[10],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2069 : RecordDataValid section14Catalog 12 (⟨302,(14),[8,12],[10],1468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1468,[5,8,9,12],1473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2070 : RecordDataValid section14Catalog 12 (⟨302,(15),[8,12],[10],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2071 : RecordDataValid section14Catalog 12 (⟨305,(0),[8,12],[10],1469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1469,[5,8,9,12],1474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2072 : RecordDataValid section14Catalog 12 (⟨305,(1),[8,12],[10],1470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1470,[5,8,9,12],1475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2073 : RecordDataValid section14Catalog 12 (⟨305,(2),[8,12],[10],1471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1471,[5,8,9,12],1476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2074 : RecordDataValid section14Catalog 12 (⟨305,(3),[8,12],[10],1472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1472,[5,8,9,12],1477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2075 : RecordDataValid section14Catalog 12 (⟨307,(0),[8,12],[10],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2076 : RecordDataValid section14Catalog 12 (⟨307,(1),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2077 : RecordDataValid section14Catalog 12 (⟨307,(2),[8,12],[10],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2078 : RecordDataValid section14Catalog 12 (⟨307,(3),[8,12],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2079 : RecordDataValid section14Catalog 12 (⟨307,(4),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2048).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2048).take 32 = [⟨300,(9),[8,12],[10],1461⟩,⟨300,(10),[8,12],[10],1461⟩,⟨300,(11),[8,12],[10],1461⟩,⟨300,(12),[8,12],[10],1462⟩,⟨300,(13),[8,12],[10],1462⟩,⟨300,(14),[8,12],[10],1462⟩,⟨300,(15),[8,12],[10],1462⟩,⟨302,(0),[8,12],[10],1463⟩,⟨302,(1),[8,12],[10],1464⟩,⟨302,(2),[8,12],[10],1465⟩,⟨302,(3),[8,12],[10],1466⟩,⟨302,(4),[8,12],[10],1463⟩,⟨302,(5),[8,12],[10],1464⟩,⟨302,(6),[8,12],[10],1467⟩,⟨302,(7),[8,12],[10],1466⟩,⟨302,(8),[8,12],[10],1463⟩,⟨302,(9),[8,12],[10],1464⟩,⟨302,(10),[8,12],[10],1465⟩,⟨302,(11),[8,12],[10],1466⟩,⟨302,(12),[8,12],[10],1463⟩,⟨302,(13),[8,12],[10],1464⟩,⟨302,(14),[8,12],[10],1468⟩,⟨302,(15),[8,12],[10],1466⟩,⟨305,(0),[8,12],[10],1469⟩,⟨305,(1),[8,12],[10],1470⟩,⟨305,(2),[8,12],[10],1471⟩,⟨305,(3),[8,12],[10],1472⟩,⟨307,(0),[8,12],[10],1266⟩,⟨307,(1),[8,12],[10],3⟩,⟨307,(2),[8,12],[10],1266⟩,⟨307,(3),[8,12],[10],29⟩,⟨307,(4),[8,12],[10],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2048
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2049
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2050
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2051
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2052
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2053
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2054
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2055
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2056
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2057
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2058
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2059
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2060
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2061
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2062
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2063
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2064
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2065
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2066
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2067
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2068
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2069
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2070
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2071
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2072
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2073
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2074
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2075
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2076
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2077
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2078
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2079
end Section14Records_12_2048_2080

#print axioms solution
