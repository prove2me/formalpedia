-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2144_2176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:31:42.081958+00:00
-- url     : https://prove2.me/submissions/140ed525-73c5-49f0-9454-d500c2ce10de

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
namespace Section14Records_6_2144_2176
private theorem valid2144 : RecordDataValid section14Catalog 6 (⟨146,(5),[1,5,6,13],[170],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2145 : RecordDataValid section14Catalog 6 (⟨146,(6),[1,5,6,13],[170],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2146 : RecordDataValid section14Catalog 6 (⟨146,(7),[1,5,6,13],[170],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2147 : RecordDataValid section14Catalog 6 (⟨146,(8),[1,5,6,13],[170],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2148 : RecordDataValid section14Catalog 6 (⟨146,(9),[1,5,6,13],[170],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2149 : RecordDataValid section14Catalog 6 (⟨146,(10),[1,5,6,13],[170],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2150 : RecordDataValid section14Catalog 6 (⟨146,(11),[1,5,6,13],[170],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2151 : RecordDataValid section14Catalog 6 (⟨146,(12),[1,5,6,13],[170],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2152 : RecordDataValid section14Catalog 6 (⟨146,(13),[1,5,6,13],[170],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2153 : RecordDataValid section14Catalog 6 (⟨146,(14),[1,5,6,13],[170],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2154 : RecordDataValid section14Catalog 6 (⟨146,(15),[1,5,6,13],[170],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2155 : RecordDataValid section14Catalog 6 (⟨150,(0),[1,5,6],[170],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2156 : RecordDataValid section14Catalog 6 (⟨150,(1),[1,5,6],[170],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2157 : RecordDataValid section14Catalog 6 (⟨150,(2),[1,5,6],[170],622⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨622,[1,4,5,6,8,9,10,12],623⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2158 : RecordDataValid section14Catalog 6 (⟨150,(3),[1,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2159 : RecordDataValid section14Catalog 6 (⟨150,(4),[1,5,6],[170],622⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨622,[1,4,5,6,8,9,10,12],623⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2160 : RecordDataValid section14Catalog 6 (⟨150,(5),[1,5,6],[170],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2161 : RecordDataValid section14Catalog 6 (⟨150,(6),[1,5,6],[170],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2162 : RecordDataValid section14Catalog 6 (⟨150,(7),[1,5,6],[170],623⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨623,[1,4,5,6,8,9,10,12],624⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2163 : RecordDataValid section14Catalog 6 (⟨150,(8),[1,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2164 : RecordDataValid section14Catalog 6 (⟨150,(9),[1,5,6],[170],623⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨623,[1,4,5,6,8,9,10,12],624⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2165 : RecordDataValid section14Catalog 6 (⟨150,(10),[1,5,6],[170],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2166 : RecordDataValid section14Catalog 6 (⟨150,(11),[1,5,6],[170],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2167 : RecordDataValid section14Catalog 6 (⟨150,(12),[1,5,6],[170],624⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨624,[1,4,5,6,8,9,10,12],625⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2168 : RecordDataValid section14Catalog 6 (⟨150,(13),[1,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2169 : RecordDataValid section14Catalog 6 (⟨150,(14),[1,5,6],[170],624⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨624,[1,4,5,6,8,9,10,12],625⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2170 : RecordDataValid section14Catalog 6 (⟨150,(15),[1,5,6],[170],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2171 : RecordDataValid section14Catalog 6 (⟨150,(16),[1,5,6],[170],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2172 : RecordDataValid section14Catalog 6 (⟨150,(17),[1,5,6],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2173 : RecordDataValid section14Catalog 6 (⟨150,(18),[1,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2174 : RecordDataValid section14Catalog 6 (⟨150,(19),[1,5,6],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2175 : RecordDataValid section14Catalog 6 (⟨150,(20),[1,5,6],[170],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2144).take 32 = [⟨146,(5),[1,5,6,13],[170],610⟩,⟨146,(6),[1,5,6,13],[170],611⟩,⟨146,(7),[1,5,6,13],[170],612⟩,⟨146,(8),[1,5,6,13],[170],613⟩,⟨146,(9),[1,5,6,13],[170],614⟩,⟨146,(10),[1,5,6,13],[170],615⟩,⟨146,(11),[1,5,6,13],[170],616⟩,⟨146,(12),[1,5,6,13],[170],617⟩,⟨146,(13),[1,5,6,13],[170],618⟩,⟨146,(14),[1,5,6,13],[170],619⟩,⟨146,(15),[1,5,6,13],[170],620⟩,⟨150,(0),[1,5,6],[170],387⟩,⟨150,(1),[1,5,6],[170],621⟩,⟨150,(2),[1,5,6],[170],622⟩,⟨150,(3),[1,5,6],[170],101⟩,⟨150,(4),[1,5,6],[170],622⟩,⟨150,(5),[1,5,6],[170],387⟩,⟨150,(6),[1,5,6],[170],621⟩,⟨150,(7),[1,5,6],[170],623⟩,⟨150,(8),[1,5,6],[170],101⟩,⟨150,(9),[1,5,6],[170],623⟩,⟨150,(10),[1,5,6],[170],387⟩,⟨150,(11),[1,5,6],[170],621⟩,⟨150,(12),[1,5,6],[170],624⟩,⟨150,(13),[1,5,6],[170],101⟩,⟨150,(14),[1,5,6],[170],624⟩,⟨150,(15),[1,5,6],[170],625⟩,⟨150,(16),[1,5,6],[170],626⟩,⟨150,(17),[1,5,6],[170],286⟩,⟨150,(18),[1,5,6],[170],101⟩,⟨150,(19),[1,5,6],[170],286⟩,⟨150,(20),[1,5,6],[170],387⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2144
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2145
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2146
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2147
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2148
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2149
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2150
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2151
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2152
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2153
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2154
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2155
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2156
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2157
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2158
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2159
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2160
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2161
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2162
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2163
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2164
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2165
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2166
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2167
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2168
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2169
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2170
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2171
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2172
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2173
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2174
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2175
end Section14Records_6_2144_2176

#print axioms solution
