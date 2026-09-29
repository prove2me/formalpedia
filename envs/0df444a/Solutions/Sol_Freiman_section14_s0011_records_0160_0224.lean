-- Prove2me | solution 1 for Freiman.section14_s0011_records_0160_0224
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:19:36.324703+00:00
-- url     : https://prove2.me/submissions/2df1ab0f-857d-4810-8c45-c09a0932d16c

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
namespace Section14Records_11_160_224
private theorem valid160 : RecordDataValid section14Catalog 11 (⟨167,(0),[11],[2],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid161 : RecordDataValid section14Catalog 11 (⟨167,(1),[11],[2],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid162 : RecordDataValid section14Catalog 11 (⟨167,(2),[11],[2],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid163 : RecordDataValid section14Catalog 11 (⟨167,(3),[11],[2],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid164 : RecordDataValid section14Catalog 11 (⟨167,(4),[11],[2],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid165 : RecordDataValid section14Catalog 11 (⟨167,(5),[11],[2],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid166 : RecordDataValid section14Catalog 11 (⟨167,(6),[11],[2],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid167 : RecordDataValid section14Catalog 11 (⟨167,(7),[11],[2],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid168 : RecordDataValid section14Catalog 11 (⟨167,(8),[11],[2],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid169 : RecordDataValid section14Catalog 11 (⟨167,(9),[11],[2],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid170 : RecordDataValid section14Catalog 11 (⟨167,(10),[11],[2],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid171 : RecordDataValid section14Catalog 11 (⟨167,(11),[11],[2],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid172 : RecordDataValid section14Catalog 11 (⟨167,(12),[11],[2],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid173 : RecordDataValid section14Catalog 11 (⟨167,(13),[11],[2],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid174 : RecordDataValid section14Catalog 11 (⟨167,(14),[11],[2],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid175 : RecordDataValid section14Catalog 11 (⟨167,(15),[11],[2],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid176 : RecordDataValid section14Catalog 11 (⟨171,(0),[11],[2],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid177 : RecordDataValid section14Catalog 11 (⟨171,(1),[11],[2],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid178 : RecordDataValid section14Catalog 11 (⟨171,(2),[11],[2],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid179 : RecordDataValid section14Catalog 11 (⟨171,(3),[11],[2],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid180 : RecordDataValid section14Catalog 11 (⟨172,(0),[11],[2],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid181 : RecordDataValid section14Catalog 11 (⟨172,(1),[11],[2],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid182 : RecordDataValid section14Catalog 11 (⟨172,(2),[11],[2],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid183 : RecordDataValid section14Catalog 11 (⟨172,(3),[11],[2],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid184 : RecordDataValid section14Catalog 11 (⟨172,(4),[11],[2],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid185 : RecordDataValid section14Catalog 11 (⟨172,(5),[11],[2],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid186 : RecordDataValid section14Catalog 11 (⟨172,(6),[11],[2],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid187 : RecordDataValid section14Catalog 11 (⟨172,(7),[11],[2],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid188 : RecordDataValid section14Catalog 11 (⟨172,(8),[11],[2],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid189 : RecordDataValid section14Catalog 11 (⟨172,(9),[11],[2],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid190 : RecordDataValid section14Catalog 11 (⟨172,(10),[11],[2],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid191 : RecordDataValid section14Catalog 11 (⟨172,(11),[11],[2],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid192 : RecordDataValid section14Catalog 11 (⟨172,(12),[11],[2],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid193 : RecordDataValid section14Catalog 11 (⟨172,(13),[11],[2],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid194 : RecordDataValid section14Catalog 11 (⟨172,(14),[11],[2],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid195 : RecordDataValid section14Catalog 11 (⟨172,(15),[11],[2],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid196 : RecordDataValid section14Catalog 11 (⟨175,(0),[11],[2],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid197 : RecordDataValid section14Catalog 11 (⟨175,(1),[11],[2],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid198 : RecordDataValid section14Catalog 11 (⟨175,(2),[11],[2],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid199 : RecordDataValid section14Catalog 11 (⟨175,(3),[11],[2],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid200 : RecordDataValid section14Catalog 11 (⟨175,(4),[11],[2],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid201 : RecordDataValid section14Catalog 11 (⟨175,(5),[11],[2],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid202 : RecordDataValid section14Catalog 11 (⟨175,(6),[11],[2],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid203 : RecordDataValid section14Catalog 11 (⟨175,(7),[11],[2],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid204 : RecordDataValid section14Catalog 11 (⟨175,(8),[11],[2],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid205 : RecordDataValid section14Catalog 11 (⟨175,(9),[11],[2],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid206 : RecordDataValid section14Catalog 11 (⟨175,(10),[11],[2],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid207 : RecordDataValid section14Catalog 11 (⟨175,(11),[11],[2],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid208 : RecordDataValid section14Catalog 11 (⟨175,(12),[11],[2],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid209 : RecordDataValid section14Catalog 11 (⟨175,(13),[11],[2],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid210 : RecordDataValid section14Catalog 11 (⟨175,(14),[11],[2],659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨659,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],660⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid211 : RecordDataValid section14Catalog 11 (⟨175,(15),[11],[2],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid212 : RecordDataValid section14Catalog 11 (⟨178,(0),[11],[2],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid213 : RecordDataValid section14Catalog 11 (⟨178,(1),[11],[2],661⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨661,[1,2,3,5,6,7,10,11,13,14,15],662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid214 : RecordDataValid section14Catalog 11 (⟨178,(2),[11],[2],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid215 : RecordDataValid section14Catalog 11 (⟨178,(3),[11],[2],662⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨662,[1,2,3,5,6,7,10,11,13,14,15],663⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid216 : RecordDataValid section14Catalog 11 (⟨178,(4),[11],[2],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid217 : RecordDataValid section14Catalog 11 (⟨178,(5),[11],[2],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid218 : RecordDataValid section14Catalog 11 (⟨178,(6),[11],[2],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid219 : RecordDataValid section14Catalog 11 (⟨178,(7),[11],[2],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid220 : RecordDataValid section14Catalog 11 (⟨178,(8),[11],[2],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid221 : RecordDataValid section14Catalog 11 (⟨178,(9),[11],[2],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid222 : RecordDataValid section14Catalog 11 (⟨178,(10),[11],[2],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid223 : RecordDataValid section14Catalog 11 (⟨178,(11),[11],[2],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 160).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 160).take 64 = [⟨167,(0),[11],[2],418⟩,⟨167,(1),[11],[2],419⟩,⟨167,(2),[11],[2],420⟩,⟨167,(3),[11],[2],421⟩,⟨167,(4),[11],[2],422⟩,⟨167,(5),[11],[2],419⟩,⟨167,(6),[11],[2],420⟩,⟨167,(7),[11],[2],421⟩,⟨167,(8),[11],[2],418⟩,⟨167,(9),[11],[2],419⟩,⟨167,(10),[11],[2],420⟩,⟨167,(11),[11],[2],421⟩,⟨167,(12),[11],[2],423⟩,⟨167,(13),[11],[2],419⟩,⟨167,(14),[11],[2],420⟩,⟨167,(15),[11],[2],421⟩,⟨171,(0),[11],[2],650⟩,⟨171,(1),[11],[2],651⟩,⟨171,(2),[11],[2],652⟩,⟨171,(3),[11],[2],653⟩,⟨172,(0),[11],[2],428⟩,⟨172,(1),[11],[2],429⟩,⟨172,(2),[11],[2],430⟩,⟨172,(3),[11],[2],431⟩,⟨172,(4),[11],[2],432⟩,⟨172,(5),[11],[2],429⟩,⟨172,(6),[11],[2],430⟩,⟨172,(7),[11],[2],431⟩,⟨172,(8),[11],[2],428⟩,⟨172,(9),[11],[2],429⟩,⟨172,(10),[11],[2],430⟩,⟨172,(11),[11],[2],431⟩,⟨172,(12),[11],[2],433⟩,⟨172,(13),[11],[2],429⟩,⟨172,(14),[11],[2],430⟩,⟨172,(15),[11],[2],431⟩,⟨175,(0),[11],[2],654⟩,⟨175,(1),[11],[2],655⟩,⟨175,(2),[11],[2],656⟩,⟨175,(3),[11],[2],657⟩,⟨175,(4),[11],[2],654⟩,⟨175,(5),[11],[2],655⟩,⟨175,(6),[11],[2],658⟩,⟨175,(7),[11],[2],657⟩,⟨175,(8),[11],[2],654⟩,⟨175,(9),[11],[2],655⟩,⟨175,(10),[11],[2],656⟩,⟨175,(11),[11],[2],657⟩,⟨175,(12),[11],[2],654⟩,⟨175,(13),[11],[2],655⟩,⟨175,(14),[11],[2],659⟩,⟨175,(15),[11],[2],657⟩,⟨178,(0),[11],[2],660⟩,⟨178,(1),[11],[2],661⟩,⟨178,(2),[11],[2],660⟩,⟨178,(3),[11],[2],662⟩,⟨178,(4),[11],[2],663⟩,⟨178,(5),[11],[2],663⟩,⟨178,(6),[11],[2],663⟩,⟨178,(7),[11],[2],663⟩,⟨178,(8),[11],[2],664⟩,⟨178,(9),[11],[2],664⟩,⟨178,(10),[11],[2],664⟩,⟨178,(11),[11],[2],664⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid160
  · exact recordValid_of_data section14Catalog 11 _ hnum valid161
  · exact recordValid_of_data section14Catalog 11 _ hnum valid162
  · exact recordValid_of_data section14Catalog 11 _ hnum valid163
  · exact recordValid_of_data section14Catalog 11 _ hnum valid164
  · exact recordValid_of_data section14Catalog 11 _ hnum valid165
  · exact recordValid_of_data section14Catalog 11 _ hnum valid166
  · exact recordValid_of_data section14Catalog 11 _ hnum valid167
  · exact recordValid_of_data section14Catalog 11 _ hnum valid168
  · exact recordValid_of_data section14Catalog 11 _ hnum valid169
  · exact recordValid_of_data section14Catalog 11 _ hnum valid170
  · exact recordValid_of_data section14Catalog 11 _ hnum valid171
  · exact recordValid_of_data section14Catalog 11 _ hnum valid172
  · exact recordValid_of_data section14Catalog 11 _ hnum valid173
  · exact recordValid_of_data section14Catalog 11 _ hnum valid174
  · exact recordValid_of_data section14Catalog 11 _ hnum valid175
  · exact recordValid_of_data section14Catalog 11 _ hnum valid176
  · exact recordValid_of_data section14Catalog 11 _ hnum valid177
  · exact recordValid_of_data section14Catalog 11 _ hnum valid178
  · exact recordValid_of_data section14Catalog 11 _ hnum valid179
  · exact recordValid_of_data section14Catalog 11 _ hnum valid180
  · exact recordValid_of_data section14Catalog 11 _ hnum valid181
  · exact recordValid_of_data section14Catalog 11 _ hnum valid182
  · exact recordValid_of_data section14Catalog 11 _ hnum valid183
  · exact recordValid_of_data section14Catalog 11 _ hnum valid184
  · exact recordValid_of_data section14Catalog 11 _ hnum valid185
  · exact recordValid_of_data section14Catalog 11 _ hnum valid186
  · exact recordValid_of_data section14Catalog 11 _ hnum valid187
  · exact recordValid_of_data section14Catalog 11 _ hnum valid188
  · exact recordValid_of_data section14Catalog 11 _ hnum valid189
  · exact recordValid_of_data section14Catalog 11 _ hnum valid190
  · exact recordValid_of_data section14Catalog 11 _ hnum valid191
  · exact recordValid_of_data section14Catalog 11 _ hnum valid192
  · exact recordValid_of_data section14Catalog 11 _ hnum valid193
  · exact recordValid_of_data section14Catalog 11 _ hnum valid194
  · exact recordValid_of_data section14Catalog 11 _ hnum valid195
  · exact recordValid_of_data section14Catalog 11 _ hnum valid196
  · exact recordValid_of_data section14Catalog 11 _ hnum valid197
  · exact recordValid_of_data section14Catalog 11 _ hnum valid198
  · exact recordValid_of_data section14Catalog 11 _ hnum valid199
  · exact recordValid_of_data section14Catalog 11 _ hnum valid200
  · exact recordValid_of_data section14Catalog 11 _ hnum valid201
  · exact recordValid_of_data section14Catalog 11 _ hnum valid202
  · exact recordValid_of_data section14Catalog 11 _ hnum valid203
  · exact recordValid_of_data section14Catalog 11 _ hnum valid204
  · exact recordValid_of_data section14Catalog 11 _ hnum valid205
  · exact recordValid_of_data section14Catalog 11 _ hnum valid206
  · exact recordValid_of_data section14Catalog 11 _ hnum valid207
  · exact recordValid_of_data section14Catalog 11 _ hnum valid208
  · exact recordValid_of_data section14Catalog 11 _ hnum valid209
  · exact recordValid_of_data section14Catalog 11 _ hnum valid210
  · exact recordValid_of_data section14Catalog 11 _ hnum valid211
  · exact recordValid_of_data section14Catalog 11 _ hnum valid212
  · exact recordValid_of_data section14Catalog 11 _ hnum valid213
  · exact recordValid_of_data section14Catalog 11 _ hnum valid214
  · exact recordValid_of_data section14Catalog 11 _ hnum valid215
  · exact recordValid_of_data section14Catalog 11 _ hnum valid216
  · exact recordValid_of_data section14Catalog 11 _ hnum valid217
  · exact recordValid_of_data section14Catalog 11 _ hnum valid218
  · exact recordValid_of_data section14Catalog 11 _ hnum valid219
  · exact recordValid_of_data section14Catalog 11 _ hnum valid220
  · exact recordValid_of_data section14Catalog 11 _ hnum valid221
  · exact recordValid_of_data section14Catalog 11 _ hnum valid222
  · exact recordValid_of_data section14Catalog 11 _ hnum valid223
end Section14Records_11_160_224

#print axioms solution
