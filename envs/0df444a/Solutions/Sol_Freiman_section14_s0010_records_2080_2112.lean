-- Prove2me | solution 1 for Freiman.section14_s0010_records_2080_2112
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:52:24.282987+00:00
-- url     : https://prove2.me/submissions/e01dfac9-ea79-4ad5-9fa1-bd1260b584f4

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
namespace Section14Records_10_2080_2112
private theorem valid2080 : RecordDataValid section14Catalog 10 (⟨225,(3),[9,10],[42],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2081 : RecordDataValid section14Catalog 10 (⟨225,(4),[9,10],[42],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2082 : RecordDataValid section14Catalog 10 (⟨225,(5),[9,10],[42],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2083 : RecordDataValid section14Catalog 10 (⟨225,(6),[9,10],[42],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2084 : RecordDataValid section14Catalog 10 (⟨225,(7),[10],[42],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2085 : RecordDataValid section14Catalog 10 (⟨225,(8),[9,10],[42],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2086 : RecordDataValid section14Catalog 10 (⟨225,(9),[10],[42],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2087 : RecordDataValid section14Catalog 10 (⟨225,(10),[9,10],[42],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2088 : RecordDataValid section14Catalog 10 (⟨225,(11),[9,10],[42],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2089 : RecordDataValid section14Catalog 10 (⟨225,(12),[10],[42],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2090 : RecordDataValid section14Catalog 10 (⟨225,(13),[9,10],[42],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2091 : RecordDataValid section14Catalog 10 (⟨225,(14),[10],[42],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2092 : RecordDataValid section14Catalog 10 (⟨225,(15),[9,10],[42],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2093 : RecordDataValid section14Catalog 10 (⟨225,(16),[9,10],[42],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2094 : RecordDataValid section14Catalog 10 (⟨225,(17),[10],[42],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2095 : RecordDataValid section14Catalog 10 (⟨225,(18),[9,10],[42],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2096 : RecordDataValid section14Catalog 10 (⟨225,(19),[10],[42],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2097 : RecordDataValid section14Catalog 10 (⟨225,(20),[9,10],[42],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2098 : RecordDataValid section14Catalog 10 (⟨225,(21),[9,10],[42],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2099 : RecordDataValid section14Catalog 10 (⟨225,(22),[10],[42],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2100 : RecordDataValid section14Catalog 10 (⟨225,(23),[9,10],[42],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2101 : RecordDataValid section14Catalog 10 (⟨225,(24),[10],[42],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2102 : RecordDataValid section14Catalog 10 (⟨226,(0),[9,10],[42],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2103 : RecordDataValid section14Catalog 10 (⟨226,(1),[9,10],[42],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2104 : RecordDataValid section14Catalog 10 (⟨226,(2),[9,10],[42],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2105 : RecordDataValid section14Catalog 10 (⟨226,(3),[9,10],[42],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2106 : RecordDataValid section14Catalog 10 (⟨226,(4),[9,10],[42],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2107 : RecordDataValid section14Catalog 10 (⟨226,(5),[9,10],[42],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2108 : RecordDataValid section14Catalog 10 (⟨226,(6),[9,10],[42],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2109 : RecordDataValid section14Catalog 10 (⟨226,(7),[9,10],[42],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2110 : RecordDataValid section14Catalog 10 (⟨226,(8),[9,10],[42],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2111 : RecordDataValid section14Catalog 10 (⟨226,(9),[9,10],[42],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2080).take 32 = [⟨225,(3),[9,10],[42],750⟩,⟨225,(4),[9,10],[42],749⟩,⟨225,(5),[9,10],[42],751⟩,⟨225,(6),[9,10],[42],752⟩,⟨225,(7),[10],[42],753⟩,⟨225,(8),[9,10],[42],754⟩,⟨225,(9),[10],[42],753⟩,⟨225,(10),[9,10],[42],755⟩,⟨225,(11),[9,10],[42],756⟩,⟨225,(12),[10],[42],757⟩,⟨225,(13),[9,10],[42],758⟩,⟨225,(14),[10],[42],757⟩,⟨225,(15),[9,10],[42],759⟩,⟨225,(16),[9,10],[42],760⟩,⟨225,(17),[10],[42],761⟩,⟨225,(18),[9,10],[42],762⟩,⟨225,(19),[10],[42],761⟩,⟨225,(20),[9,10],[42],763⟩,⟨225,(21),[9,10],[42],764⟩,⟨225,(22),[10],[42],547⟩,⟨225,(23),[9,10],[42],765⟩,⟨225,(24),[10],[42],547⟩,⟨226,(0),[9,10],[42],766⟩,⟨226,(1),[9,10],[42],767⟩,⟨226,(2),[9,10],[42],768⟩,⟨226,(3),[9,10],[42],767⟩,⟨226,(4),[9,10],[42],769⟩,⟨226,(5),[9,10],[42],770⟩,⟨226,(6),[9,10],[42],771⟩,⟨226,(7),[9,10],[42],771⟩,⟨226,(8),[9,10],[42],772⟩,⟨226,(9),[9,10],[42],772⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2080
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2081
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2082
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2083
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2084
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2085
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2086
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2087
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2088
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2089
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2090
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2091
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2092
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2093
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2094
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2095
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2096
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2097
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2098
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2099
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2100
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2101
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2102
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2103
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2104
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2105
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2106
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2107
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2108
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2109
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2110
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2111
end Section14Records_10_2080_2112

#print axioms solution
