-- Prove2me | solution 1 for Freiman.section14_s0012_records_2208_2240
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:25:17.364766+00:00
-- url     : https://prove2.me/submissions/71700d39-6e48-4f0a-b893-5e9a7e61fcb7

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
namespace Section14Records_12_2208_2240
private theorem valid2208 : RecordDataValid section14Catalog 12 (⟨321,(20),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2209 : RecordDataValid section14Catalog 12 (⟨321,(21),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2210 : RecordDataValid section14Catalog 12 (⟨321,(22),[8,12],[10],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2211 : RecordDataValid section14Catalog 12 (⟨321,(23),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2212 : RecordDataValid section14Catalog 12 (⟨321,(24),[8,12],[10],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2213 : RecordDataValid section14Catalog 12 (⟨478,(0),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2214 : RecordDataValid section14Catalog 12 (⟨478,(1),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2215 : RecordDataValid section14Catalog 12 (⟨478,(2),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2216 : RecordDataValid section14Catalog 12 (⟨478,(3),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2217 : RecordDataValid section14Catalog 12 (⟨478,(4),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2218 : RecordDataValid section14Catalog 12 (⟨478,(5),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2219 : RecordDataValid section14Catalog 12 (⟨478,(6),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2220 : RecordDataValid section14Catalog 12 (⟨478,(7),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2221 : RecordDataValid section14Catalog 12 (⟨478,(8),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2222 : RecordDataValid section14Catalog 12 (⟨478,(9),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2223 : RecordDataValid section14Catalog 12 (⟨483,(0),[4,8,12,16],[6],1250⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1250,[4,8,12,16],1254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2224 : RecordDataValid section14Catalog 12 (⟨483,(0),[12],[2],1702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1702,[12],1707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2225 : RecordDataValid section14Catalog 12 (⟨483,(1),[4,8,12,16],[6],1251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1251,[4,8,12,16],1255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2226 : RecordDataValid section14Catalog 12 (⟨483,(1),[12],[2],1703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1703,[12],1708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2227 : RecordDataValid section14Catalog 12 (⟨483,(2),[4,8,12,16],[6],1252⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1252,[4,8,12,16],1256⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2228 : RecordDataValid section14Catalog 12 (⟨483,(2),[12],[2],1704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1704,[12],1709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2229 : RecordDataValid section14Catalog 12 (⟨483,(3),[4,8,12,16],[6],1251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1251,[4,8,12,16],1255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2230 : RecordDataValid section14Catalog 12 (⟨483,(3),[12],[2],1703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1703,[12],1708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2231 : RecordDataValid section14Catalog 12 (⟨483,(4),[4,8,12,16],[6],1253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1253,[4,8,12,16],1257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2232 : RecordDataValid section14Catalog 12 (⟨483,(4),[12],[2],1705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1705,[12],1710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2233 : RecordDataValid section14Catalog 12 (⟨483,(5),[4,8,12,16],[6],1250⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1250,[4,8,12,16],1254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2234 : RecordDataValid section14Catalog 12 (⟨483,(5),[12],[2],1702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1702,[12],1707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2235 : RecordDataValid section14Catalog 12 (⟨483,(6),[4,8,12,16],[6],1251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1251,[4,8,12,16],1255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2236 : RecordDataValid section14Catalog 12 (⟨483,(6),[12],[2],1703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1703,[12],1708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2237 : RecordDataValid section14Catalog 12 (⟨483,(7),[4,8,12,16],[6],1252⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1252,[4,8,12,16],1256⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2238 : RecordDataValid section14Catalog 12 (⟨483,(7),[12],[2],1704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1704,[12],1709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2239 : RecordDataValid section14Catalog 12 (⟨483,(8),[4,8,12,16],[6],1251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1251,[4,8,12,16],1255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2208).take 32 = [⟨321,(20),[8,12],[10],882⟩,⟨321,(21),[8,12],[10],1497⟩,⟨321,(22),[8,12],[10],1512⟩,⟨321,(23),[8,12],[10],101⟩,⟨321,(24),[8,12],[10],1512⟩,⟨478,(0),[4,8,12,16],[10],3⟩,⟨478,(1),[4,8,12,16],[10],3⟩,⟨478,(2),[4,8,12,16],[10],3⟩,⟨478,(3),[4,8,12,16],[10],3⟩,⟨478,(4),[4,8,12,16],[10],3⟩,⟨478,(5),[4,8,12,16],[10],3⟩,⟨478,(6),[4,8,12,16],[10],3⟩,⟨478,(7),[4,8,12,16],[10],3⟩,⟨478,(8),[4,8,12,16],[10],3⟩,⟨478,(9),[4,8,12,16],[10],3⟩,⟨483,(0),[4,8,12,16],[6],1250⟩,⟨483,(0),[12],[2],1702⟩,⟨483,(1),[4,8,12,16],[6],1251⟩,⟨483,(1),[12],[2],1703⟩,⟨483,(2),[4,8,12,16],[6],1252⟩,⟨483,(2),[12],[2],1704⟩,⟨483,(3),[4,8,12,16],[6],1251⟩,⟨483,(3),[12],[2],1703⟩,⟨483,(4),[4,8,12,16],[6],1253⟩,⟨483,(4),[12],[2],1705⟩,⟨483,(5),[4,8,12,16],[6],1250⟩,⟨483,(5),[12],[2],1702⟩,⟨483,(6),[4,8,12,16],[6],1251⟩,⟨483,(6),[12],[2],1703⟩,⟨483,(7),[4,8,12,16],[6],1252⟩,⟨483,(7),[12],[2],1704⟩,⟨483,(8),[4,8,12,16],[6],1251⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2208
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2209
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2210
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2211
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2212
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2213
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2214
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2215
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2216
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2217
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2218
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2219
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2220
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2221
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2222
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2223
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2224
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2225
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2226
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2227
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2228
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2229
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2230
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2231
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2232
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2233
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2234
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2235
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2236
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2237
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2238
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2239
end Section14Records_12_2208_2240

#print axioms solution
