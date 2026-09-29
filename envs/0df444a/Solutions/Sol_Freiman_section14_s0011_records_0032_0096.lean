-- Prove2me | solution 1 for Freiman.section14_s0011_records_0032_0096
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:16:26.837967+00:00
-- url     : https://prove2.me/submissions/4c52416b-57e9-47fc-a2f1-5142b46125ff

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
namespace Section14Records_11_32_96
private theorem valid32 : RecordDataValid section14Catalog 11 (⟨30,(1),[11,12],[2],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid33 : RecordDataValid section14Catalog 11 (⟨30,(2),[11],[2],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid34 : RecordDataValid section14Catalog 11 (⟨30,(3),[11],[2],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid35 : RecordDataValid section14Catalog 11 (⟨30,(4),[11],[2],231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨231,[1,2,3,4,5,6,7,8,9,10,11,12],231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid36 : RecordDataValid section14Catalog 11 (⟨30,(5),[11],[2],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid37 : RecordDataValid section14Catalog 11 (⟨30,(6),[11],[2],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid38 : RecordDataValid section14Catalog 11 (⟨30,(7),[11],[2],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid39 : RecordDataValid section14Catalog 11 (⟨30,(8),[11],[2],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid40 : RecordDataValid section14Catalog 11 (⟨30,(9),[11],[2],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid41 : RecordDataValid section14Catalog 11 (⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid42 : RecordDataValid section14Catalog 11 (⟨38,(-1),[4,8,11,12,16],[1],248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨248,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid43 : RecordDataValid section14Catalog 11 (⟨38,(-1),[11],[3],340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨340,[1,2,3,5,6,7,9,10,11,13,14,15],341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid44 : RecordDataValid section14Catalog 11 (⟨47,(0),[11],[2],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid45 : RecordDataValid section14Catalog 11 (⟨47,(1),[11],[2],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid46 : RecordDataValid section14Catalog 11 (⟨47,(2),[11],[2],261⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨261,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid47 : RecordDataValid section14Catalog 11 (⟨47,(3),[11],[2],262⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨262,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid48 : RecordDataValid section14Catalog 11 (⟨47,(4),[11],[2],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid49 : RecordDataValid section14Catalog 11 (⟨47,(5),[11],[2],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid50 : RecordDataValid section14Catalog 11 (⟨47,(6),[11],[2],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid51 : RecordDataValid section14Catalog 11 (⟨47,(7),[11],[2],264⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨264,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],265⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid52 : RecordDataValid section14Catalog 11 (⟨47,(8),[11],[2],265⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨265,[1,2,3,4,5,6,7,10,11,13,14,15,16],266⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid53 : RecordDataValid section14Catalog 11 (⟨47,(9),[11],[2],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid54 : RecordDataValid section14Catalog 11 (⟨47,(10),[11],[2],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid55 : RecordDataValid section14Catalog 11 (⟨47,(11),[11],[2],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid56 : RecordDataValid section14Catalog 11 (⟨47,(12),[11],[2],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid57 : RecordDataValid section14Catalog 11 (⟨47,(13),[11],[2],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid58 : RecordDataValid section14Catalog 11 (⟨47,(14),[11],[2],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid59 : RecordDataValid section14Catalog 11 (⟨47,(15),[11],[2],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid60 : RecordDataValid section14Catalog 11 (⟨47,(16),[11],[2],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid61 : RecordDataValid section14Catalog 11 (⟨47,(17),[11],[2],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid62 : RecordDataValid section14Catalog 11 (⟨47,(18),[11],[2],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid63 : RecordDataValid section14Catalog 11 (⟨47,(19),[11],[2],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid64 : RecordDataValid section14Catalog 11 (⟨47,(20),[11],[2],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid65 : RecordDataValid section14Catalog 11 (⟨47,(21),[11],[2],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid66 : RecordDataValid section14Catalog 11 (⟨47,(22),[11],[2],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid67 : RecordDataValid section14Catalog 11 (⟨47,(23),[11],[2],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid68 : RecordDataValid section14Catalog 11 (⟨47,(24),[11],[2],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid69 : RecordDataValid section14Catalog 11 (⟨53,(0),[11],[2],279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨279,[1,2,3,4,5,6,7,8,9,10,11,12],280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid70 : RecordDataValid section14Catalog 11 (⟨53,(1),[11],[2],280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨280,[1,2,3,4,5,6,7,8,9,10,11,12],281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid71 : RecordDataValid section14Catalog 11 (⟨53,(2),[11],[2],281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨281,[1,2,3,4,5,6,7,8,9,10,11,12],282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid72 : RecordDataValid section14Catalog 11 (⟨53,(3),[11],[2],282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨282,[1,2,3,4,5,6,7,8,9,10,11,12],283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid73 : RecordDataValid section14Catalog 11 (⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid74 : RecordDataValid section14Catalog 11 (⟨60,(-1),[4,8,11,12,16],[1],343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨343,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid75 : RecordDataValid section14Catalog 11 (⟨60,(-1),[11],[3],385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid76 : RecordDataValid section14Catalog 11 (⟨69,(0),[11],[2],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid77 : RecordDataValid section14Catalog 11 (⟨69,(1),[11],[2],1691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1691,[11],1696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid78 : RecordDataValid section14Catalog 11 (⟨69,(2),[11],[2],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid79 : RecordDataValid section14Catalog 11 (⟨69,(3),[11],[2],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid80 : RecordDataValid section14Catalog 11 (⟨69,(4),[11],[2],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid81 : RecordDataValid section14Catalog 11 (⟨69,(5),[11],[2],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid82 : RecordDataValid section14Catalog 11 (⟨69,(6),[11],[2],1691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1691,[11],1696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid83 : RecordDataValid section14Catalog 11 (⟨69,(7),[11],[2],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid84 : RecordDataValid section14Catalog 11 (⟨69,(8),[11],[2],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid85 : RecordDataValid section14Catalog 11 (⟨69,(9),[11],[2],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid86 : RecordDataValid section14Catalog 11 (⟨69,(10),[11],[2],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid87 : RecordDataValid section14Catalog 11 (⟨69,(11),[11],[2],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid88 : RecordDataValid section14Catalog 11 (⟨69,(12),[11],[2],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid89 : RecordDataValid section14Catalog 11 (⟨69,(13),[11],[2],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid90 : RecordDataValid section14Catalog 11 (⟨69,(14),[11],[2],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid91 : RecordDataValid section14Catalog 11 (⟨69,(15),[11],[2],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid92 : RecordDataValid section14Catalog 11 (⟨69,(16),[11],[2],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid93 : RecordDataValid section14Catalog 11 (⟨69,(17),[11],[2],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid94 : RecordDataValid section14Catalog 11 (⟨69,(18),[11],[2],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid95 : RecordDataValid section14Catalog 11 (⟨69,(19),[11],[2],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 32).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 32).take 64 = [⟨30,(1),[11,12],[2],153⟩,⟨30,(2),[11],[2],200⟩,⟨30,(3),[11],[2],230⟩,⟨30,(4),[11],[2],231⟩,⟨30,(5),[11],[2],230⟩,⟨30,(6),[11],[2],232⟩,⟨30,(7),[11],[2],232⟩,⟨30,(8),[11],[2],233⟩,⟨30,(9),[11],[2],233⟩,⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩,⟨38,(-1),[4,8,11,12,16],[1],248⟩,⟨38,(-1),[11],[3],340⟩,⟨47,(0),[11],[2],189⟩,⟨47,(1),[11],[2],260⟩,⟨47,(2),[11],[2],261⟩,⟨47,(3),[11],[2],262⟩,⟨47,(4),[11],[2],263⟩,⟨47,(5),[11],[2],189⟩,⟨47,(6),[11],[2],260⟩,⟨47,(7),[11],[2],264⟩,⟨47,(8),[11],[2],265⟩,⟨47,(9),[11],[2],266⟩,⟨47,(10),[11],[2],194⟩,⟨47,(11),[11],[2],267⟩,⟨47,(12),[11],[2],268⟩,⟨47,(13),[11],[2],268⟩,⟨47,(14),[11],[2],266⟩,⟨47,(15),[11],[2],196⟩,⟨47,(16),[11],[2],269⟩,⟨47,(17),[11],[2],270⟩,⟨47,(18),[11],[2],270⟩,⟨47,(19),[11],[2],270⟩,⟨47,(20),[11],[2],198⟩,⟨47,(21),[11],[2],271⟩,⟨47,(22),[11],[2],272⟩,⟨47,(23),[11],[2],272⟩,⟨47,(24),[11],[2],272⟩,⟨53,(0),[11],[2],279⟩,⟨53,(1),[11],[2],280⟩,⟨53,(2),[11],[2],281⟩,⟨53,(3),[11],[2],282⟩,⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩,⟨60,(-1),[4,8,11,12,16],[1],343⟩,⟨60,(-1),[11],[3],385⟩,⟨69,(0),[11],[2],189⟩,⟨69,(1),[11],[2],1691⟩,⟨69,(2),[11],[2],375⟩,⟨69,(3),[11],[2],376⟩,⟨69,(4),[11],[2],377⟩,⟨69,(5),[11],[2],189⟩,⟨69,(6),[11],[2],1691⟩,⟨69,(7),[11],[2],375⟩,⟨69,(8),[11],[2],376⟩,⟨69,(9),[11],[2],377⟩,⟨69,(10),[11],[2],194⟩,⟨69,(11),[11],[2],378⟩,⟨69,(12),[11],[2],378⟩,⟨69,(13),[11],[2],378⟩,⟨69,(14),[11],[2],377⟩,⟨69,(15),[11],[2],196⟩,⟨69,(16),[11],[2],379⟩,⟨69,(17),[11],[2],379⟩,⟨69,(18),[11],[2],379⟩,⟨69,(19),[11],[2],379⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid32
  · exact recordValid_of_data section14Catalog 11 _ hnum valid33
  · exact recordValid_of_data section14Catalog 11 _ hnum valid34
  · exact recordValid_of_data section14Catalog 11 _ hnum valid35
  · exact recordValid_of_data section14Catalog 11 _ hnum valid36
  · exact recordValid_of_data section14Catalog 11 _ hnum valid37
  · exact recordValid_of_data section14Catalog 11 _ hnum valid38
  · exact recordValid_of_data section14Catalog 11 _ hnum valid39
  · exact recordValid_of_data section14Catalog 11 _ hnum valid40
  · exact recordValid_of_data section14Catalog 11 _ hnum valid41
  · exact recordValid_of_data section14Catalog 11 _ hnum valid42
  · exact recordValid_of_data section14Catalog 11 _ hnum valid43
  · exact recordValid_of_data section14Catalog 11 _ hnum valid44
  · exact recordValid_of_data section14Catalog 11 _ hnum valid45
  · exact recordValid_of_data section14Catalog 11 _ hnum valid46
  · exact recordValid_of_data section14Catalog 11 _ hnum valid47
  · exact recordValid_of_data section14Catalog 11 _ hnum valid48
  · exact recordValid_of_data section14Catalog 11 _ hnum valid49
  · exact recordValid_of_data section14Catalog 11 _ hnum valid50
  · exact recordValid_of_data section14Catalog 11 _ hnum valid51
  · exact recordValid_of_data section14Catalog 11 _ hnum valid52
  · exact recordValid_of_data section14Catalog 11 _ hnum valid53
  · exact recordValid_of_data section14Catalog 11 _ hnum valid54
  · exact recordValid_of_data section14Catalog 11 _ hnum valid55
  · exact recordValid_of_data section14Catalog 11 _ hnum valid56
  · exact recordValid_of_data section14Catalog 11 _ hnum valid57
  · exact recordValid_of_data section14Catalog 11 _ hnum valid58
  · exact recordValid_of_data section14Catalog 11 _ hnum valid59
  · exact recordValid_of_data section14Catalog 11 _ hnum valid60
  · exact recordValid_of_data section14Catalog 11 _ hnum valid61
  · exact recordValid_of_data section14Catalog 11 _ hnum valid62
  · exact recordValid_of_data section14Catalog 11 _ hnum valid63
  · exact recordValid_of_data section14Catalog 11 _ hnum valid64
  · exact recordValid_of_data section14Catalog 11 _ hnum valid65
  · exact recordValid_of_data section14Catalog 11 _ hnum valid66
  · exact recordValid_of_data section14Catalog 11 _ hnum valid67
  · exact recordValid_of_data section14Catalog 11 _ hnum valid68
  · exact recordValid_of_data section14Catalog 11 _ hnum valid69
  · exact recordValid_of_data section14Catalog 11 _ hnum valid70
  · exact recordValid_of_data section14Catalog 11 _ hnum valid71
  · exact recordValid_of_data section14Catalog 11 _ hnum valid72
  · exact recordValid_of_data section14Catalog 11 _ hnum valid73
  · exact recordValid_of_data section14Catalog 11 _ hnum valid74
  · exact recordValid_of_data section14Catalog 11 _ hnum valid75
  · exact recordValid_of_data section14Catalog 11 _ hnum valid76
  · exact recordValid_of_data section14Catalog 11 _ hnum valid77
  · exact recordValid_of_data section14Catalog 11 _ hnum valid78
  · exact recordValid_of_data section14Catalog 11 _ hnum valid79
  · exact recordValid_of_data section14Catalog 11 _ hnum valid80
  · exact recordValid_of_data section14Catalog 11 _ hnum valid81
  · exact recordValid_of_data section14Catalog 11 _ hnum valid82
  · exact recordValid_of_data section14Catalog 11 _ hnum valid83
  · exact recordValid_of_data section14Catalog 11 _ hnum valid84
  · exact recordValid_of_data section14Catalog 11 _ hnum valid85
  · exact recordValid_of_data section14Catalog 11 _ hnum valid86
  · exact recordValid_of_data section14Catalog 11 _ hnum valid87
  · exact recordValid_of_data section14Catalog 11 _ hnum valid88
  · exact recordValid_of_data section14Catalog 11 _ hnum valid89
  · exact recordValid_of_data section14Catalog 11 _ hnum valid90
  · exact recordValid_of_data section14Catalog 11 _ hnum valid91
  · exact recordValid_of_data section14Catalog 11 _ hnum valid92
  · exact recordValid_of_data section14Catalog 11 _ hnum valid93
  · exact recordValid_of_data section14Catalog 11 _ hnum valid94
  · exact recordValid_of_data section14Catalog 11 _ hnum valid95
end Section14Records_11_32_96

#print axioms solution
