-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2176_2304
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:28:05.587185+00:00
-- url     : https://prove2.me/submissions/854393d1-4dbc-463a-9e8c-93d4ee5d0d8c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2176_2208
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2176_2208
private theorem valid2176 : RecordDataValid section14Catalog 6 (⟨150,(21),[1,5,6],[170],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2177 : RecordDataValid section14Catalog 6 (⟨150,(22),[1,5,6],[170],627⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨627,[1,5,6,9,10],628⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2178 : RecordDataValid section14Catalog 6 (⟨150,(23),[1,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2179 : RecordDataValid section14Catalog 6 (⟨150,(24),[1,5,6],[170],627⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨627,[1,5,6,9,10],628⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2180 : RecordDataValid section14Catalog 6 (⟨151,(5),[1,5,6],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2181 : RecordDataValid section14Catalog 6 (⟨151,(7),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2182 : RecordDataValid section14Catalog 6 (⟨151,(8),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2183 : RecordDataValid section14Catalog 6 (⟨151,(9),[5,6,13],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2184 : RecordDataValid section14Catalog 6 (⟨151,(15),[1,6],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2185 : RecordDataValid section14Catalog 6 (⟨151,(16),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2186 : RecordDataValid section14Catalog 6 (⟨151,(17),[1,5,6,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2187 : RecordDataValid section14Catalog 6 (⟨151,(19),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2188 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2189 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2190 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,9,10,13,14],[5],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2191 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2192 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2193 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2194 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2195 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2196 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[130,134],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2197 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[146],635⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨635,[1,2,3,5,6,7,13,14,15],636⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2198 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2199 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[150],637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2200 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[186],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2201 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2202 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2203 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,2,5,6,14],[190],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2204 : RecordDataValid section14Catalog 6 (⟨153,(-1),[1,5,6,13],[194,198],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2205 : RecordDataValid section14Catalog 6 (⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2206 : RecordDataValid section14Catalog 6 (⟨153,(-1),[2,6,9,10,14],[16,20],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2207 : RecordDataValid section14Catalog 6 (⟨153,(-1),[2,6,14],[40,44,56,60],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2176_2208 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2176).take 32 = [⟨150,(21),[1,5,6],[170],621⟩,⟨150,(22),[1,5,6],[170],627⟩,⟨150,(23),[1,5,6],[170],101⟩,⟨150,(24),[1,5,6],[170],627⟩,⟨151,(5),[1,5,6],[170],3⟩,⟨151,(7),[1,5,6,13],[170],3⟩,⟨151,(8),[1,5,6,13],[170],3⟩,⟨151,(9),[5,6,13],[170],143⟩,⟨151,(15),[1,6],[170],3⟩,⟨151,(16),[1,5,6,13],[170],3⟩,⟨151,(17),[1,5,6,13],[170],48⟩,⟨151,(19),[5,6],[170],143⟩,⟨153,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],631⟩,⟨153,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨153,(-1),[1,2,5,6,9,10,13,14],[5],631⟩,⟨153,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨153,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨153,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],631⟩,⟨153,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],632⟩,⟨153,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],633⟩,⟨153,(-1),[1,2,5,6,13,14],[130,134],634⟩,⟨153,(-1),[1,2,5,6,13,14],[146],635⟩,⟨153,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],636⟩,⟨153,(-1),[1,2,5,6,13,14],[150],637⟩,⟨153,(-1),[1,2,5,6,13,14],[186],879⟩,⟨153,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],880⟩,⟨153,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨153,(-1),[1,2,5,6,14],[190],879⟩,⟨153,(-1),[1,5,6,13],[194,198],880⟩,⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩,⟨153,(-1),[2,6,9,10,14],[16,20],632⟩,⟨153,(-1),[2,6,14],[40,44,56,60],632⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2176
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2177
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2178
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2179
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2180
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2181
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2182
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2183
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2184
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2185
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2186
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2187
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2188
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2189
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2190
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2191
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2192
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2193
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2194
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2195
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2196
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2197
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2198
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2199
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2200
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2201
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2202
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2203
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2204
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2205
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2206
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2207
end Section14Records_6_2176_2208

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2176_2208


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2208_2240
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2208_2240
private theorem valid2208 : RecordDataValid section14Catalog 6 (⟨153,(-1),[2,6,14],[211,215,235,239,251,255],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2209 : RecordDataValid section14Catalog 6 (⟨153,(-1),[5,6],[131,135],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2210 : RecordDataValid section14Catalog 6 (⟨153,(-1),[6],[195,199],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2211 : RecordDataValid section14Catalog 6 (⟨155,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2212 : RecordDataValid section14Catalog 6 (⟨155,(0),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2213 : RecordDataValid section14Catalog 6 (⟨155,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2214 : RecordDataValid section14Catalog 6 (⟨155,(1),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2215 : RecordDataValid section14Catalog 6 (⟨155,(2),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2216 : RecordDataValid section14Catalog 6 (⟨155,(2),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2217 : RecordDataValid section14Catalog 6 (⟨155,(3),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2218 : RecordDataValid section14Catalog 6 (⟨155,(3),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2219 : RecordDataValid section14Catalog 6 (⟨155,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2220 : RecordDataValid section14Catalog 6 (⟨155,(4),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2221 : RecordDataValid section14Catalog 6 (⟨155,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2222 : RecordDataValid section14Catalog 6 (⟨155,(5),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2223 : RecordDataValid section14Catalog 6 (⟨155,(6),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2224 : RecordDataValid section14Catalog 6 (⟨155,(6),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2225 : RecordDataValid section14Catalog 6 (⟨155,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2226 : RecordDataValid section14Catalog 6 (⟨155,(7),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2227 : RecordDataValid section14Catalog 6 (⟨155,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2228 : RecordDataValid section14Catalog 6 (⟨155,(8),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2229 : RecordDataValid section14Catalog 6 (⟨155,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2230 : RecordDataValid section14Catalog 6 (⟨155,(9),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2231 : RecordDataValid section14Catalog 6 (⟨155,(10),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2232 : RecordDataValid section14Catalog 6 (⟨155,(10),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2233 : RecordDataValid section14Catalog 6 (⟨155,(11),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2234 : RecordDataValid section14Catalog 6 (⟨155,(11),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2235 : RecordDataValid section14Catalog 6 (⟨155,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2236 : RecordDataValid section14Catalog 6 (⟨155,(12),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2237 : RecordDataValid section14Catalog 6 (⟨155,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2238 : RecordDataValid section14Catalog 6 (⟨155,(13),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2239 : RecordDataValid section14Catalog 6 (⟨155,(14),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2208_2240 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2208).take 32 = [⟨153,(-1),[2,6,14],[211,215,235,239,251,255],636⟩,⟨153,(-1),[5,6],[131,135],636⟩,⟨153,(-1),[6],[195,199],636⟩,⟨155,(0),[1,2,5,6,13,14],[170],3⟩,⟨155,(0),[5,6],[174],3⟩,⟨155,(1),[1,2,5,6,13,14],[170],3⟩,⟨155,(1),[5,6],[174],3⟩,⟨155,(2),[1,2,5,6,13,14],[170],3⟩,⟨155,(2),[5,6],[174],3⟩,⟨155,(3),[1,2,5,6,13,14],[170],3⟩,⟨155,(3),[5,6],[174],3⟩,⟨155,(4),[1,2,5,6,13,14],[170],3⟩,⟨155,(4),[5,6],[174],3⟩,⟨155,(5),[1,2,5,6,13,14],[170],3⟩,⟨155,(5),[5,6],[174],3⟩,⟨155,(6),[1,2,5,6,13,14],[170],3⟩,⟨155,(6),[5,6],[174],3⟩,⟨155,(7),[1,2,5,6,13,14],[170],3⟩,⟨155,(7),[5,6],[174],3⟩,⟨155,(8),[1,2,5,6,13,14],[170],3⟩,⟨155,(8),[5,6],[174],3⟩,⟨155,(9),[1,2,5,6,13,14],[170],3⟩,⟨155,(9),[5,6],[174],3⟩,⟨155,(10),[1,2,5,6,13,14],[170],3⟩,⟨155,(10),[5,6],[174],3⟩,⟨155,(11),[1,2,5,6,13,14],[170],3⟩,⟨155,(11),[5,6],[174],3⟩,⟨155,(12),[1,2,5,6,13,14],[170],3⟩,⟨155,(12),[5,6],[174],3⟩,⟨155,(13),[1,2,5,6,13,14],[170],3⟩,⟨155,(13),[5,6],[174],3⟩,⟨155,(14),[1,2,5,6,13,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2208
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2209
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2210
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2211
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2212
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2213
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2214
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2215
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2216
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2217
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2218
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2219
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2220
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2221
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2222
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2223
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2224
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2225
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2226
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2227
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2228
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2229
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2230
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2231
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2232
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2233
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2234
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2235
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2236
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2237
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2238
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2239
end Section14Records_6_2208_2240

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2208_2240


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2240_2272
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2240_2272
private theorem valid2240 : RecordDataValid section14Catalog 6 (⟨155,(14),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2241 : RecordDataValid section14Catalog 6 (⟨155,(15),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2242 : RecordDataValid section14Catalog 6 (⟨155,(15),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2243 : RecordDataValid section14Catalog 6 (⟨155,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2244 : RecordDataValid section14Catalog 6 (⟨155,(16),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2245 : RecordDataValid section14Catalog 6 (⟨155,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2246 : RecordDataValid section14Catalog 6 (⟨155,(17),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2247 : RecordDataValid section14Catalog 6 (⟨155,(18),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2248 : RecordDataValid section14Catalog 6 (⟨155,(18),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2249 : RecordDataValid section14Catalog 6 (⟨155,(19),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2250 : RecordDataValid section14Catalog 6 (⟨155,(19),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2251 : RecordDataValid section14Catalog 6 (⟨155,(20),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2252 : RecordDataValid section14Catalog 6 (⟨155,(20),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2253 : RecordDataValid section14Catalog 6 (⟨155,(21),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2254 : RecordDataValid section14Catalog 6 (⟨155,(21),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2255 : RecordDataValid section14Catalog 6 (⟨155,(22),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2256 : RecordDataValid section14Catalog 6 (⟨155,(22),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2257 : RecordDataValid section14Catalog 6 (⟨155,(23),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2258 : RecordDataValid section14Catalog 6 (⟨155,(23),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2259 : RecordDataValid section14Catalog 6 (⟨155,(24),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2260 : RecordDataValid section14Catalog 6 (⟨155,(24),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2261 : RecordDataValid section14Catalog 6 (⟨157,(0),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2262 : RecordDataValid section14Catalog 6 (⟨157,(0),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2263 : RecordDataValid section14Catalog 6 (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2264 : RecordDataValid section14Catalog 6 (⟨157,(1),[5,6],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2265 : RecordDataValid section14Catalog 6 (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2266 : RecordDataValid section14Catalog 6 (⟨157,(2),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2267 : RecordDataValid section14Catalog 6 (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2268 : RecordDataValid section14Catalog 6 (⟨157,(3),[5,6],[174],290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨290,[1,2,3,5,6,7,13,14,15],291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2269 : RecordDataValid section14Catalog 6 (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2270 : RecordDataValid section14Catalog 6 (⟨157,(4),[5,6],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2271 : RecordDataValid section14Catalog 6 (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2240_2272 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2240).take 32 = [⟨155,(14),[5,6],[174],3⟩,⟨155,(15),[1,2,5,6,13,14],[170],3⟩,⟨155,(15),[5,6],[174],3⟩,⟨155,(16),[1,2,5,6,13,14],[170],3⟩,⟨155,(16),[5,6],[174],3⟩,⟨155,(17),[1,2,5,6,13,14],[170],3⟩,⟨155,(17),[5,6],[174],3⟩,⟨155,(18),[1,2,5,6,13,14],[170],3⟩,⟨155,(18),[5,6],[174],3⟩,⟨155,(19),[1,2,5,6,13,14],[170],3⟩,⟨155,(19),[5,6],[174],3⟩,⟨155,(20),[1,2,5,6,13,14],[170],3⟩,⟨155,(20),[5,6],[174],3⟩,⟨155,(21),[1,2,5,6,13,14],[170],3⟩,⟨155,(21),[5,6],[174],3⟩,⟨155,(22),[1,2,5,6,13,14],[170],3⟩,⟨155,(22),[5,6],[174],3⟩,⟨155,(23),[1,2,5,6,13,14],[170],3⟩,⟨155,(23),[5,6],[174],3⟩,⟨155,(24),[1,2,5,6,13,14],[170],3⟩,⟨155,(24),[5,6],[174],3⟩,⟨157,(0),[1,2,5,6,13,14],[170],10⟩,⟨157,(0),[5,6],[174],288⟩,⟨157,(1),[1,2,5,6,13,14],[170],393⟩,⟨157,(1),[5,6],[174],289⟩,⟨157,(2),[1,2,5,6,13,14],[170],394⟩,⟨157,(2),[5,6],[174],288⟩,⟨157,(3),[1,2,5,6,13,14],[170],395⟩,⟨157,(3),[5,6],[174],290⟩,⟨157,(4),[1,2,5,6,13,14],[170],396⟩,⟨157,(4),[5,6],[174],291⟩,⟨157,(5),[1,2,5,6,13,14],[170],10⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2240
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2241
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2242
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2243
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2244
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2245
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2246
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2247
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2248
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2249
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2250
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2251
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2252
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2253
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2254
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2255
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2256
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2257
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2258
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2259
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2260
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2261
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2262
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2263
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2264
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2265
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2266
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2267
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2268
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2269
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2270
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2271
end Section14Records_6_2240_2272

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2240_2272


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2272_2304
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2272_2304
private theorem valid2272 : RecordDataValid section14Catalog 6 (⟨157,(5),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2273 : RecordDataValid section14Catalog 6 (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2274 : RecordDataValid section14Catalog 6 (⟨157,(6),[5,6],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2275 : RecordDataValid section14Catalog 6 (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2276 : RecordDataValid section14Catalog 6 (⟨157,(7),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2277 : RecordDataValid section14Catalog 6 (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2278 : RecordDataValid section14Catalog 6 (⟨157,(8),[5,6],[174],290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨290,[1,2,3,5,6,7,13,14,15],291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2279 : RecordDataValid section14Catalog 6 (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2280 : RecordDataValid section14Catalog 6 (⟨157,(9),[5,6],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2281 : RecordDataValid section14Catalog 6 (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2282 : RecordDataValid section14Catalog 6 (⟨157,(10),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2283 : RecordDataValid section14Catalog 6 (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2284 : RecordDataValid section14Catalog 6 (⟨157,(11),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2285 : RecordDataValid section14Catalog 6 (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2286 : RecordDataValid section14Catalog 6 (⟨157,(12),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2287 : RecordDataValid section14Catalog 6 (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2288 : RecordDataValid section14Catalog 6 (⟨157,(13),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2289 : RecordDataValid section14Catalog 6 (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2290 : RecordDataValid section14Catalog 6 (⟨157,(14),[5,6],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2291 : RecordDataValid section14Catalog 6 (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2292 : RecordDataValid section14Catalog 6 (⟨157,(15),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2293 : RecordDataValid section14Catalog 6 (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2294 : RecordDataValid section14Catalog 6 (⟨157,(16),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2295 : RecordDataValid section14Catalog 6 (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2296 : RecordDataValid section14Catalog 6 (⟨157,(17),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2297 : RecordDataValid section14Catalog 6 (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2298 : RecordDataValid section14Catalog 6 (⟨157,(18),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2299 : RecordDataValid section14Catalog 6 (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2300 : RecordDataValid section14Catalog 6 (⟨157,(19),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2301 : RecordDataValid section14Catalog 6 (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2302 : RecordDataValid section14Catalog 6 (⟨157,(20),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2303 : RecordDataValid section14Catalog 6 (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2272_2304 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2272).take 32 = [⟨157,(5),[5,6],[174],288⟩,⟨157,(6),[1,2,5,6,13,14],[170],393⟩,⟨157,(6),[5,6],[174],289⟩,⟨157,(7),[1,2,5,6,13,14],[170],394⟩,⟨157,(7),[5,6],[174],288⟩,⟨157,(8),[1,2,5,6,13,14],[170],395⟩,⟨157,(8),[5,6],[174],290⟩,⟨157,(9),[1,2,5,6,13,14],[170],396⟩,⟨157,(9),[5,6],[174],291⟩,⟨157,(10),[1,2,5,6,13,14],[170],18⟩,⟨157,(10),[5,6],[174],292⟩,⟨157,(11),[1,2,5,6,13,14],[170],397⟩,⟨157,(11),[5,6],[174],292⟩,⟨157,(12),[1,2,5,6,13,14],[170],397⟩,⟨157,(12),[5,6],[174],292⟩,⟨157,(13),[1,2,5,6,13,14],[170],397⟩,⟨157,(13),[5,6],[174],292⟩,⟨157,(14),[1,2,5,6,13,14],[170],396⟩,⟨157,(14),[5,6],[174],291⟩,⟨157,(15),[1,2,5,6,13,14],[170],21⟩,⟨157,(15),[5,6],[174],293⟩,⟨157,(16),[1,2,5,6,13,14],[170],398⟩,⟨157,(16),[5,6],[174],293⟩,⟨157,(17),[1,2,5,6,13,14],[170],398⟩,⟨157,(17),[5,6],[174],293⟩,⟨157,(18),[1,2,5,6,13,14],[170],398⟩,⟨157,(18),[5,6],[174],293⟩,⟨157,(19),[1,2,5,6,13,14],[170],398⟩,⟨157,(19),[5,6],[174],293⟩,⟨157,(20),[1,2,5,6,13,14],[170],24⟩,⟨157,(20),[5,6],[174],294⟩,⟨157,(21),[1,2,5,6,13,14],[170],399⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2272
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2273
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2274
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2275
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2276
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2277
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2278
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2279
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2280
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2281
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2282
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2283
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2284
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2285
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2286
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2287
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2288
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2289
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2290
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2291
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2292
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2293
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2294
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2295
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2296
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2297
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2298
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2299
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2300
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2301
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2302
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2303
end Section14Records_6_2272_2304

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2272_2304

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2176).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2176 2240 2304 (by decide) (by decide) (all_of_interval_split P xs 2176 2208 2240 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2176_2208 hnum) (Freiman.workReverse20260919_s0006_records_2208_2240 hnum)) (all_of_interval_split P xs 2240 2272 2304 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2240_2272 hnum) (Freiman.workReverse20260919_s0006_records_2272_2304 hnum)))

#print axioms solution
