-- Prove2me | solution 1 for Freiman.section14_s0011_records_0992_1056
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:46:21.819122+00:00
-- url     : https://prove2.me/submissions/31b4d7fe-c57b-4014-9129-b39db7987a2e

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
namespace Section14Records_11_992_1056
private theorem valid992 : RecordDataValid section14Catalog 11 (⟨426,(0),[11],[2],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid993 : RecordDataValid section14Catalog 11 (⟨426,(1),[11],[2],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid994 : RecordDataValid section14Catalog 11 (⟨426,(2),[11],[2],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid995 : RecordDataValid section14Catalog 11 (⟨426,(3),[11],[2],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid996 : RecordDataValid section14Catalog 11 (⟨426,(4),[11],[2],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid997 : RecordDataValid section14Catalog 11 (⟨426,(5),[11],[2],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid998 : RecordDataValid section14Catalog 11 (⟨426,(6),[11],[2],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid999 : RecordDataValid section14Catalog 11 (⟨426,(7),[11],[2],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1000 : RecordDataValid section14Catalog 11 (⟨426,(8),[11],[2],1102⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1102,[3,5,7,8,9,11,12,15],1106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1001 : RecordDataValid section14Catalog 11 (⟨426,(9),[11],[2],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1002 : RecordDataValid section14Catalog 11 (⟨428,(0),[11],[2],1103⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1103,[3,7,11,15],1107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1003 : RecordDataValid section14Catalog 11 (⟨428,(1),[11],[2],1103⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1103,[3,7,11,15],1107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1004 : RecordDataValid section14Catalog 11 (⟨428,(2),[11],[2],1104⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1104,[3,7,11,15],1108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1005 : RecordDataValid section14Catalog 11 (⟨428,(3),[11],[2],1105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1105,[3,7,11,15],1109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1006 : RecordDataValid section14Catalog 11 (⟨428,(4),[11],[2],1106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1106,[3,7,11,15],1110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1007 : RecordDataValid section14Catalog 11 (⟨428,(5),[11],[2],1107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1107,[3,7,11,15],1111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1008 : RecordDataValid section14Catalog 11 (⟨428,(6),[11],[2],1107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1107,[3,7,11,15],1111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1009 : RecordDataValid section14Catalog 11 (⟨428,(7),[11],[2],1107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1107,[3,7,11,15],1111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1010 : RecordDataValid section14Catalog 11 (⟨428,(8),[11],[2],1105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1105,[3,7,11,15],1109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1011 : RecordDataValid section14Catalog 11 (⟨428,(9),[11],[2],1106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1106,[3,7,11,15],1110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1012 : RecordDataValid section14Catalog 11 (⟨431,(0),[11],[2],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1013 : RecordDataValid section14Catalog 11 (⟨431,(1),[11],[2],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1014 : RecordDataValid section14Catalog 11 (⟨431,(2),[11],[2],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1015 : RecordDataValid section14Catalog 11 (⟨431,(3),[11],[2],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1016 : RecordDataValid section14Catalog 11 (⟨431,(4),[11],[2],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1017 : RecordDataValid section14Catalog 11 (⟨431,(5),[11],[2],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1018 : RecordDataValid section14Catalog 11 (⟨431,(6),[11],[2],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1019 : RecordDataValid section14Catalog 11 (⟨431,(7),[11],[2],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1020 : RecordDataValid section14Catalog 11 (⟨431,(8),[11],[2],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1021 : RecordDataValid section14Catalog 11 (⟨431,(9),[11],[2],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1022 : RecordDataValid section14Catalog 11 (⟨431,(10),[11],[2],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1023 : RecordDataValid section14Catalog 11 (⟨431,(11),[11],[2],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1024 : RecordDataValid section14Catalog 11 (⟨431,(12),[11],[2],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1025 : RecordDataValid section14Catalog 11 (⟨431,(13),[11],[2],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1026 : RecordDataValid section14Catalog 11 (⟨431,(14),[11],[2],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1027 : RecordDataValid section14Catalog 11 (⟨431,(15),[11],[2],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1028 : RecordDataValid section14Catalog 11 (⟨431,(16),[11],[2],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1029 : RecordDataValid section14Catalog 11 (⟨431,(17),[11],[2],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1030 : RecordDataValid section14Catalog 11 (⟨431,(18),[11],[2],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1031 : RecordDataValid section14Catalog 11 (⟨431,(19),[11],[2],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1032 : RecordDataValid section14Catalog 11 (⟨431,(20),[11],[2],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1033 : RecordDataValid section14Catalog 11 (⟨431,(21),[11],[2],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1034 : RecordDataValid section14Catalog 11 (⟨431,(22),[11],[2],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1035 : RecordDataValid section14Catalog 11 (⟨431,(23),[11],[2],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1036 : RecordDataValid section14Catalog 11 (⟨431,(24),[11],[2],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1037 : RecordDataValid section14Catalog 11 (⟨433,(0),[11],[2],1115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1115,[3,7,11,15],1119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1038 : RecordDataValid section14Catalog 11 (⟨433,(1),[11],[2],1115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1115,[3,7,11,15],1119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1039 : RecordDataValid section14Catalog 11 (⟨433,(2),[11],[2],1116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1116,[3,7,11,15],1120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1040 : RecordDataValid section14Catalog 11 (⟨433,(3),[11],[2],1117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1117,[3,7,11,15],1121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1041 : RecordDataValid section14Catalog 11 (⟨433,(4),[11],[2],1118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1118,[3,7,11,15],1122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1042 : RecordDataValid section14Catalog 11 (⟨433,(5),[11],[2],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1043 : RecordDataValid section14Catalog 11 (⟨433,(6),[11],[2],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1044 : RecordDataValid section14Catalog 11 (⟨433,(7),[11],[2],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1045 : RecordDataValid section14Catalog 11 (⟨433,(8),[11],[2],1117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1117,[3,7,11,15],1121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1046 : RecordDataValid section14Catalog 11 (⟨433,(9),[11],[2],1118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1118,[3,7,11,15],1122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1047 : RecordDataValid section14Catalog 11 (⟨436,(0),[11],[2],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1048 : RecordDataValid section14Catalog 11 (⟨436,(1),[11],[2],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1049 : RecordDataValid section14Catalog 11 (⟨436,(2),[11],[2],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1050 : RecordDataValid section14Catalog 11 (⟨436,(3),[11],[2],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1051 : RecordDataValid section14Catalog 11 (⟨436,(4),[11],[2],1123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1123,[3,5,7,8,9,11,12,15],1127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1052 : RecordDataValid section14Catalog 11 (⟨436,(5),[11],[2],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1053 : RecordDataValid section14Catalog 11 (⟨436,(6),[11],[2],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1054 : RecordDataValid section14Catalog 11 (⟨436,(7),[11],[2],1124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1124,[3,5,7,8,9,11,12,15],1128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1055 : RecordDataValid section14Catalog 11 (⟨436,(8),[11],[2],1125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1125,[3,5,7,8,9,11,12,15],1129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 992).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 992).take 64 = [⟨426,(0),[11],[2],1098⟩,⟨426,(1),[11],[2],1099⟩,⟨426,(2),[11],[2],1100⟩,⟨426,(3),[11],[2],1100⟩,⟨426,(4),[11],[2],1100⟩,⟨426,(5),[11],[2],1098⟩,⟨426,(6),[11],[2],1099⟩,⟨426,(7),[11],[2],1101⟩,⟨426,(8),[11],[2],1102⟩,⟨426,(9),[11],[2],1101⟩,⟨428,(0),[11],[2],1103⟩,⟨428,(1),[11],[2],1103⟩,⟨428,(2),[11],[2],1104⟩,⟨428,(3),[11],[2],1105⟩,⟨428,(4),[11],[2],1106⟩,⟨428,(5),[11],[2],1107⟩,⟨428,(6),[11],[2],1107⟩,⟨428,(7),[11],[2],1107⟩,⟨428,(8),[11],[2],1105⟩,⟨428,(9),[11],[2],1106⟩,⟨431,(0),[11],[2],1108⟩,⟨431,(1),[11],[2],1109⟩,⟨431,(2),[11],[2],1110⟩,⟨431,(3),[11],[2],1110⟩,⟨431,(4),[11],[2],1110⟩,⟨431,(5),[11],[2],1108⟩,⟨431,(6),[11],[2],1109⟩,⟨431,(7),[11],[2],1111⟩,⟨431,(8),[11],[2],1112⟩,⟨431,(9),[11],[2],1111⟩,⟨431,(10),[11],[2],1108⟩,⟨431,(11),[11],[2],1109⟩,⟨431,(12),[11],[2],1113⟩,⟨431,(13),[11],[2],1112⟩,⟨431,(14),[11],[2],1113⟩,⟨431,(15),[11],[2],1108⟩,⟨431,(16),[11],[2],1109⟩,⟨431,(17),[11],[2],1111⟩,⟨431,(18),[11],[2],1112⟩,⟨431,(19),[11],[2],1111⟩,⟨431,(20),[11],[2],1108⟩,⟨431,(21),[11],[2],1109⟩,⟨431,(22),[11],[2],1114⟩,⟨431,(23),[11],[2],1112⟩,⟨431,(24),[11],[2],1114⟩,⟨433,(0),[11],[2],1115⟩,⟨433,(1),[11],[2],1115⟩,⟨433,(2),[11],[2],1116⟩,⟨433,(3),[11],[2],1117⟩,⟨433,(4),[11],[2],1118⟩,⟨433,(5),[11],[2],1119⟩,⟨433,(6),[11],[2],1119⟩,⟨433,(7),[11],[2],1119⟩,⟨433,(8),[11],[2],1117⟩,⟨433,(9),[11],[2],1118⟩,⟨436,(0),[11],[2],1120⟩,⟨436,(1),[11],[2],1121⟩,⟨436,(2),[11],[2],1122⟩,⟨436,(3),[11],[2],1122⟩,⟨436,(4),[11],[2],1123⟩,⟨436,(5),[11],[2],1120⟩,⟨436,(6),[11],[2],1121⟩,⟨436,(7),[11],[2],1124⟩,⟨436,(8),[11],[2],1125⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid992
  · exact recordValid_of_data section14Catalog 11 _ hnum valid993
  · exact recordValid_of_data section14Catalog 11 _ hnum valid994
  · exact recordValid_of_data section14Catalog 11 _ hnum valid995
  · exact recordValid_of_data section14Catalog 11 _ hnum valid996
  · exact recordValid_of_data section14Catalog 11 _ hnum valid997
  · exact recordValid_of_data section14Catalog 11 _ hnum valid998
  · exact recordValid_of_data section14Catalog 11 _ hnum valid999
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1000
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1001
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1002
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1003
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1004
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1005
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1006
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1007
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1008
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1009
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1010
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1011
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1012
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1013
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1014
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1015
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1016
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1017
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1018
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1019
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1020
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1021
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1022
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1023
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1024
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1025
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1026
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1027
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1028
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1029
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1030
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1031
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1032
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1033
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1034
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1035
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1036
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1037
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1038
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1039
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1040
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1041
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1042
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1043
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1044
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1045
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1046
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1047
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1048
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1049
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1050
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1051
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1052
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1053
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1054
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1055
end Section14Records_11_992_1056

#print axioms solution
