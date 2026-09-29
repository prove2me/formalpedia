-- Prove2me | solution 1 for Freiman.section14_s0011_records_0928_0992
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:44:12.604277+00:00
-- url     : https://prove2.me/submissions/f7f183b5-6cb2-4652-a9ae-a0170bef0442

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
namespace Section14Records_11_928_992
private theorem valid928 : RecordDataValid section14Catalog 11 (⟨406,(0),[11],[2],1628⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1628,[7,11],1633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid929 : RecordDataValid section14Catalog 11 (⟨406,(1),[11],[2],955⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨955,[3,7,11],959⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid930 : RecordDataValid section14Catalog 11 (⟨406,(2),[11],[2],954⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨954,[3,7,11],958⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid931 : RecordDataValid section14Catalog 11 (⟨406,(3),[11],[2],956⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨956,[3,7,11],960⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid932 : RecordDataValid section14Catalog 11 (⟨408,(0),[11],[2],957⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨957,[3,7,11,15],961⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid933 : RecordDataValid section14Catalog 11 (⟨408,(1),[11],[2],958⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨958,[3,7,11,15],962⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid934 : RecordDataValid section14Catalog 11 (⟨408,(2),[11],[2],959⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨959,[3,7,11,15],963⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid935 : RecordDataValid section14Catalog 11 (⟨408,(3),[11],[2],960⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨960,[3,7,11,15],964⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid936 : RecordDataValid section14Catalog 11 (⟨408,(4),[11],[2],961⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨961,[3,7,11,15],965⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid937 : RecordDataValid section14Catalog 11 (⟨411,(0),[11],[2],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid938 : RecordDataValid section14Catalog 11 (⟨411,(1),[11],[2],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid939 : RecordDataValid section14Catalog 11 (⟨411,(2),[11],[2],962⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨962,[3,7,11],966⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid940 : RecordDataValid section14Catalog 11 (⟨411,(3),[11],[2],962⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨962,[3,7,11],966⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid941 : RecordDataValid section14Catalog 11 (⟨411,(4),[11],[2],963⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨963,[3,7,11],967⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid942 : RecordDataValid section14Catalog 11 (⟨411,(5),[11],[2],963⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨963,[3,7,11],967⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid943 : RecordDataValid section14Catalog 11 (⟨411,(6),[11],[2],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid944 : RecordDataValid section14Catalog 11 (⟨411,(7),[11],[2],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid945 : RecordDataValid section14Catalog 11 (⟨411,(8),[11],[2],940⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨940,[3,7,11],944⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid946 : RecordDataValid section14Catalog 11 (⟨411,(9),[11],[2],940⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨940,[3,7,11],944⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid947 : RecordDataValid section14Catalog 11 (⟨413,(-1),[3,7,11,15],[0],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid948 : RecordDataValid section14Catalog 11 (⟨413,(-1),[11],[1],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid949 : RecordDataValid section14Catalog 11 (⟨413,(-1),[11],[3],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid950 : RecordDataValid section14Catalog 11 (⟨415,(0),[11],[2],1697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1697,[11],1702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid951 : RecordDataValid section14Catalog 11 (⟨415,(1),[11],[2],1697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1697,[11],1702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid952 : RecordDataValid section14Catalog 11 (⟨415,(2),[11],[2],1698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1698,[11],1703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid953 : RecordDataValid section14Catalog 11 (⟨415,(3),[11],[2],1698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1698,[11],1703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid954 : RecordDataValid section14Catalog 11 (⟨415,(4),[11],[2],1699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1699,[11],1704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid955 : RecordDataValid section14Catalog 11 (⟨415,(5),[11],[2],1700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1700,[11],1705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid956 : RecordDataValid section14Catalog 11 (⟨415,(6),[11],[2],1699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1699,[11],1704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid957 : RecordDataValid section14Catalog 11 (⟨415,(7),[11],[2],1701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1701,[11],1706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid958 : RecordDataValid section14Catalog 11 (⟨415,(8),[11],[2],1699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1699,[11],1704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid959 : RecordDataValid section14Catalog 11 (⟨415,(9),[11],[2],1700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1700,[11],1705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid960 : RecordDataValid section14Catalog 11 (⟨420,(0),[11],[2],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid961 : RecordDataValid section14Catalog 11 (⟨420,(1),[11],[2],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid962 : RecordDataValid section14Catalog 11 (⟨420,(2),[11],[2],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid963 : RecordDataValid section14Catalog 11 (⟨420,(3),[11],[2],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid964 : RecordDataValid section14Catalog 11 (⟨420,(4),[11],[2],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid965 : RecordDataValid section14Catalog 11 (⟨420,(5),[11],[2],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid966 : RecordDataValid section14Catalog 11 (⟨420,(6),[11],[2],1090⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1090,[3,5,7,8,9,11,12,15],1094⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid967 : RecordDataValid section14Catalog 11 (⟨420,(7),[11],[2],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid968 : RecordDataValid section14Catalog 11 (⟨420,(8),[11],[2],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid969 : RecordDataValid section14Catalog 11 (⟨420,(9),[11],[2],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid970 : RecordDataValid section14Catalog 11 (⟨420,(10),[11],[2],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid971 : RecordDataValid section14Catalog 11 (⟨420,(11),[11],[2],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid972 : RecordDataValid section14Catalog 11 (⟨420,(12),[11],[2],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid973 : RecordDataValid section14Catalog 11 (⟨420,(13),[11],[2],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid974 : RecordDataValid section14Catalog 11 (⟨420,(14),[11],[2],1091⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1091,[3,5,7,8,9,11,12,15],1095⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid975 : RecordDataValid section14Catalog 11 (⟨420,(15),[11],[2],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid976 : RecordDataValid section14Catalog 11 (⟨423,(0),[11],[2],1092⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1092,[3,7,11,15],1096⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid977 : RecordDataValid section14Catalog 11 (⟨423,(1),[11],[2],1093⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1093,[3,7,11,15],1097⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid978 : RecordDataValid section14Catalog 11 (⟨423,(2),[11],[2],1092⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1092,[3,7,11,15],1096⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid979 : RecordDataValid section14Catalog 11 (⟨423,(3),[11],[2],1094⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1094,[3,7,11,15],1098⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid980 : RecordDataValid section14Catalog 11 (⟨423,(4),[11],[2],1095⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1095,[3,7,11,15],1099⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid981 : RecordDataValid section14Catalog 11 (⟨423,(5),[11],[2],1095⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1095,[3,7,11,15],1099⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid982 : RecordDataValid section14Catalog 11 (⟨423,(6),[11],[2],1095⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1095,[3,7,11,15],1099⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid983 : RecordDataValid section14Catalog 11 (⟨423,(7),[11],[2],1095⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1095,[3,7,11,15],1099⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid984 : RecordDataValid section14Catalog 11 (⟨423,(8),[11],[2],1096⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1096,[3,7,11,15],1100⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid985 : RecordDataValid section14Catalog 11 (⟨423,(9),[11],[2],1096⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1096,[3,7,11,15],1100⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid986 : RecordDataValid section14Catalog 11 (⟨423,(10),[11],[2],1096⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1096,[3,7,11,15],1100⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid987 : RecordDataValid section14Catalog 11 (⟨423,(11),[11],[2],1096⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1096,[3,7,11,15],1100⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid988 : RecordDataValid section14Catalog 11 (⟨423,(12),[11],[2],1097⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1097,[3,7,11,15],1101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid989 : RecordDataValid section14Catalog 11 (⟨423,(13),[11],[2],1097⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1097,[3,7,11,15],1101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid990 : RecordDataValid section14Catalog 11 (⟨423,(14),[11],[2],1097⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1097,[3,7,11,15],1101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid991 : RecordDataValid section14Catalog 11 (⟨423,(15),[11],[2],1097⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1097,[3,7,11,15],1101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 928).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 928).take 64 = [⟨406,(0),[11],[2],1628⟩,⟨406,(1),[11],[2],955⟩,⟨406,(2),[11],[2],954⟩,⟨406,(3),[11],[2],956⟩,⟨408,(0),[11],[2],957⟩,⟨408,(1),[11],[2],958⟩,⟨408,(2),[11],[2],959⟩,⟨408,(3),[11],[2],960⟩,⟨408,(4),[11],[2],961⟩,⟨411,(0),[11],[2],873⟩,⟨411,(1),[11],[2],873⟩,⟨411,(2),[11],[2],962⟩,⟨411,(3),[11],[2],962⟩,⟨411,(4),[11],[2],963⟩,⟨411,(5),[11],[2],963⟩,⟨411,(6),[11],[2],939⟩,⟨411,(7),[11],[2],939⟩,⟨411,(8),[11],[2],940⟩,⟨411,(9),[11],[2],940⟩,⟨413,(-1),[3,7,11,15],[0],881⟩,⟨413,(-1),[11],[1],883⟩,⟨413,(-1),[11],[3],910⟩,⟨415,(0),[11],[2],1697⟩,⟨415,(1),[11],[2],1697⟩,⟨415,(2),[11],[2],1698⟩,⟨415,(3),[11],[2],1698⟩,⟨415,(4),[11],[2],1699⟩,⟨415,(5),[11],[2],1700⟩,⟨415,(6),[11],[2],1699⟩,⟨415,(7),[11],[2],1701⟩,⟨415,(8),[11],[2],1699⟩,⟨415,(9),[11],[2],1700⟩,⟨420,(0),[11],[2],1086⟩,⟨420,(1),[11],[2],1087⟩,⟨420,(2),[11],[2],1088⟩,⟨420,(3),[11],[2],1089⟩,⟨420,(4),[11],[2],1086⟩,⟨420,(5),[11],[2],1087⟩,⟨420,(6),[11],[2],1090⟩,⟨420,(7),[11],[2],1089⟩,⟨420,(8),[11],[2],1086⟩,⟨420,(9),[11],[2],1087⟩,⟨420,(10),[11],[2],1088⟩,⟨420,(11),[11],[2],1089⟩,⟨420,(12),[11],[2],1086⟩,⟨420,(13),[11],[2],1087⟩,⟨420,(14),[11],[2],1091⟩,⟨420,(15),[11],[2],1089⟩,⟨423,(0),[11],[2],1092⟩,⟨423,(1),[11],[2],1093⟩,⟨423,(2),[11],[2],1092⟩,⟨423,(3),[11],[2],1094⟩,⟨423,(4),[11],[2],1095⟩,⟨423,(5),[11],[2],1095⟩,⟨423,(6),[11],[2],1095⟩,⟨423,(7),[11],[2],1095⟩,⟨423,(8),[11],[2],1096⟩,⟨423,(9),[11],[2],1096⟩,⟨423,(10),[11],[2],1096⟩,⟨423,(11),[11],[2],1096⟩,⟨423,(12),[11],[2],1097⟩,⟨423,(13),[11],[2],1097⟩,⟨423,(14),[11],[2],1097⟩,⟨423,(15),[11],[2],1097⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid928
  · exact recordValid_of_data section14Catalog 11 _ hnum valid929
  · exact recordValid_of_data section14Catalog 11 _ hnum valid930
  · exact recordValid_of_data section14Catalog 11 _ hnum valid931
  · exact recordValid_of_data section14Catalog 11 _ hnum valid932
  · exact recordValid_of_data section14Catalog 11 _ hnum valid933
  · exact recordValid_of_data section14Catalog 11 _ hnum valid934
  · exact recordValid_of_data section14Catalog 11 _ hnum valid935
  · exact recordValid_of_data section14Catalog 11 _ hnum valid936
  · exact recordValid_of_data section14Catalog 11 _ hnum valid937
  · exact recordValid_of_data section14Catalog 11 _ hnum valid938
  · exact recordValid_of_data section14Catalog 11 _ hnum valid939
  · exact recordValid_of_data section14Catalog 11 _ hnum valid940
  · exact recordValid_of_data section14Catalog 11 _ hnum valid941
  · exact recordValid_of_data section14Catalog 11 _ hnum valid942
  · exact recordValid_of_data section14Catalog 11 _ hnum valid943
  · exact recordValid_of_data section14Catalog 11 _ hnum valid944
  · exact recordValid_of_data section14Catalog 11 _ hnum valid945
  · exact recordValid_of_data section14Catalog 11 _ hnum valid946
  · exact recordValid_of_data section14Catalog 11 _ hnum valid947
  · exact recordValid_of_data section14Catalog 11 _ hnum valid948
  · exact recordValid_of_data section14Catalog 11 _ hnum valid949
  · exact recordValid_of_data section14Catalog 11 _ hnum valid950
  · exact recordValid_of_data section14Catalog 11 _ hnum valid951
  · exact recordValid_of_data section14Catalog 11 _ hnum valid952
  · exact recordValid_of_data section14Catalog 11 _ hnum valid953
  · exact recordValid_of_data section14Catalog 11 _ hnum valid954
  · exact recordValid_of_data section14Catalog 11 _ hnum valid955
  · exact recordValid_of_data section14Catalog 11 _ hnum valid956
  · exact recordValid_of_data section14Catalog 11 _ hnum valid957
  · exact recordValid_of_data section14Catalog 11 _ hnum valid958
  · exact recordValid_of_data section14Catalog 11 _ hnum valid959
  · exact recordValid_of_data section14Catalog 11 _ hnum valid960
  · exact recordValid_of_data section14Catalog 11 _ hnum valid961
  · exact recordValid_of_data section14Catalog 11 _ hnum valid962
  · exact recordValid_of_data section14Catalog 11 _ hnum valid963
  · exact recordValid_of_data section14Catalog 11 _ hnum valid964
  · exact recordValid_of_data section14Catalog 11 _ hnum valid965
  · exact recordValid_of_data section14Catalog 11 _ hnum valid966
  · exact recordValid_of_data section14Catalog 11 _ hnum valid967
  · exact recordValid_of_data section14Catalog 11 _ hnum valid968
  · exact recordValid_of_data section14Catalog 11 _ hnum valid969
  · exact recordValid_of_data section14Catalog 11 _ hnum valid970
  · exact recordValid_of_data section14Catalog 11 _ hnum valid971
  · exact recordValid_of_data section14Catalog 11 _ hnum valid972
  · exact recordValid_of_data section14Catalog 11 _ hnum valid973
  · exact recordValid_of_data section14Catalog 11 _ hnum valid974
  · exact recordValid_of_data section14Catalog 11 _ hnum valid975
  · exact recordValid_of_data section14Catalog 11 _ hnum valid976
  · exact recordValid_of_data section14Catalog 11 _ hnum valid977
  · exact recordValid_of_data section14Catalog 11 _ hnum valid978
  · exact recordValid_of_data section14Catalog 11 _ hnum valid979
  · exact recordValid_of_data section14Catalog 11 _ hnum valid980
  · exact recordValid_of_data section14Catalog 11 _ hnum valid981
  · exact recordValid_of_data section14Catalog 11 _ hnum valid982
  · exact recordValid_of_data section14Catalog 11 _ hnum valid983
  · exact recordValid_of_data section14Catalog 11 _ hnum valid984
  · exact recordValid_of_data section14Catalog 11 _ hnum valid985
  · exact recordValid_of_data section14Catalog 11 _ hnum valid986
  · exact recordValid_of_data section14Catalog 11 _ hnum valid987
  · exact recordValid_of_data section14Catalog 11 _ hnum valid988
  · exact recordValid_of_data section14Catalog 11 _ hnum valid989
  · exact recordValid_of_data section14Catalog 11 _ hnum valid990
  · exact recordValid_of_data section14Catalog 11 _ hnum valid991
end Section14Records_11_928_992

#print axioms solution
