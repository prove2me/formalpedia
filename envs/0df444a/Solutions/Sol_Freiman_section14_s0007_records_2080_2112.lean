-- Prove2me | solution 1 for Freiman.section14_s0007_records_2080_2112
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:31:29.08387+00:00
-- url     : https://prove2.me/submissions/00eddc4f-30b2-4328-8565-5210c8d1b48d

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
namespace Section14Records_7_2080_2112
private theorem valid2080 : RecordDataValid section14Catalog 7 (⟨356,(9),[7],[9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2081 : RecordDataValid section14Catalog 7 (⟨360,(0),[7],[9,11],1539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1539,[7,11],1544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2082 : RecordDataValid section14Catalog 7 (⟨360,(0),[7],[10],1540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1540,[7],1545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2083 : RecordDataValid section14Catalog 7 (⟨360,(1),[3,7],[10],935⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨935,[3,7],939⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2084 : RecordDataValid section14Catalog 7 (⟨360,(1),[3,7],[11],942⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨942,[3,7,11],946⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2085 : RecordDataValid section14Catalog 7 (⟨360,(1),[7],[9],942⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨942,[3,7,11],946⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2086 : RecordDataValid section14Catalog 7 (⟨360,(2),[3,7],[10],934⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨934,[3,7],938⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2087 : RecordDataValid section14Catalog 7 (⟨360,(2),[3,7],[11],941⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨941,[3,7,11],945⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2088 : RecordDataValid section14Catalog 7 (⟨360,(2),[7],[9],941⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨941,[3,7,11],945⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2089 : RecordDataValid section14Catalog 7 (⟨360,(3),[3,7],[10],936⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨936,[3,7],940⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2090 : RecordDataValid section14Catalog 7 (⟨360,(3),[3,7],[11],943⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨943,[3,7,11],947⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2091 : RecordDataValid section14Catalog 7 (⟨360,(3),[7],[9],943⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨943,[3,7,11],947⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2092 : RecordDataValid section14Catalog 7 (⟨363,(0),[7],[9,10,11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2093 : RecordDataValid section14Catalog 7 (⟨363,(1),[3,7,15],[10,11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2094 : RecordDataValid section14Catalog 7 (⟨363,(1),[7],[9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2095 : RecordDataValid section14Catalog 7 (⟨363,(2),[3,7,15],[10,11],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2096 : RecordDataValid section14Catalog 7 (⟨363,(2),[7],[9],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2097 : RecordDataValid section14Catalog 7 (⟨363,(3),[3,7,15],[10,11],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2098 : RecordDataValid section14Catalog 7 (⟨363,(3),[7],[9],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2099 : RecordDataValid section14Catalog 7 (⟨365,(0),[3,7],[10],283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨283,[1,2,3,5,6,7],284⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2100 : RecordDataValid section14Catalog 7 (⟨365,(0),[3,7],[11],337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨337,[1,2,3,4,5,6,7,8,9,10,11,12],338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2101 : RecordDataValid section14Catalog 7 (⟨365,(0),[7],[9],337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨337,[1,2,3,4,5,6,7,8,9,10,11,12],338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2102 : RecordDataValid section14Catalog 7 (⟨365,(1),[3,7],[10],937⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨937,[3,7],941⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2103 : RecordDataValid section14Catalog 7 (⟨365,(1),[3,7],[11],944⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨944,[3,7,11],948⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2104 : RecordDataValid section14Catalog 7 (⟨365,(1),[7],[9],944⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨944,[3,7,11],948⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2105 : RecordDataValid section14Catalog 7 (⟨365,(2),[3,7],[10],938⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨938,[3,7],942⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2106 : RecordDataValid section14Catalog 7 (⟨365,(2),[3,7],[11],945⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨945,[3,7,11],949⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2107 : RecordDataValid section14Catalog 7 (⟨365,(2),[7],[9],945⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨945,[3,7,11],949⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2108 : RecordDataValid section14Catalog 7 (⟨365,(3),[3,7],[10,11],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2109 : RecordDataValid section14Catalog 7 (⟨365,(3),[7],[9],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2110 : RecordDataValid section14Catalog 7 (⟨365,(4),[3,7],[10,11],940⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨940,[3,7,11],944⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2111 : RecordDataValid section14Catalog 7 (⟨365,(4),[7],[9],204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨204,[1,2,3,4,7],204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2080).take 32 = [⟨356,(9),[7],[9],2⟩,⟨360,(0),[7],[9,11],1539⟩,⟨360,(0),[7],[10],1540⟩,⟨360,(1),[3,7],[10],935⟩,⟨360,(1),[3,7],[11],942⟩,⟨360,(1),[7],[9],942⟩,⟨360,(2),[3,7],[10],934⟩,⟨360,(2),[3,7],[11],941⟩,⟨360,(2),[7],[9],941⟩,⟨360,(3),[3,7],[10],936⟩,⟨360,(3),[3,7],[11],943⟩,⟨360,(3),[7],[9],943⟩,⟨363,(0),[7],[9,10,11],2⟩,⟨363,(1),[3,7,15],[10,11],2⟩,⟨363,(1),[7],[9],2⟩,⟨363,(2),[3,7,15],[10,11],159⟩,⟨363,(2),[7],[9],159⟩,⟨363,(3),[3,7,15],[10,11],99⟩,⟨363,(3),[7],[9],99⟩,⟨365,(0),[3,7],[10],283⟩,⟨365,(0),[3,7],[11],337⟩,⟨365,(0),[7],[9],337⟩,⟨365,(1),[3,7],[10],937⟩,⟨365,(1),[3,7],[11],944⟩,⟨365,(1),[7],[9],944⟩,⟨365,(2),[3,7],[10],938⟩,⟨365,(2),[3,7],[11],945⟩,⟨365,(2),[7],[9],945⟩,⟨365,(3),[3,7],[10,11],939⟩,⟨365,(3),[7],[9],939⟩,⟨365,(4),[3,7],[10,11],940⟩,⟨365,(4),[7],[9],204⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2080
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2081
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2082
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2083
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2084
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2085
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2086
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2087
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2088
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2089
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2090
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2091
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2092
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2093
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2094
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2095
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2096
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2097
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2098
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2099
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2100
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2101
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2102
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2103
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2104
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2105
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2106
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2107
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2108
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2109
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2110
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2111
end Section14Records_7_2080_2112

#print axioms solution
