-- Prove2me | solution 1 for Freiman.section14_s0011_records_0864_0928
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:42:38.973952+00:00
-- url     : https://prove2.me/submissions/14e7f2e9-38db-4102-a5d6-6c04a2561b24

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
namespace Section14Records_11_864_928
private theorem valid864 : RecordDataValid section14Catalog 11 (⟨356,(6),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid865 : RecordDataValid section14Catalog 11 (⟨356,(7),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid866 : RecordDataValid section14Catalog 11 (⟨356,(8),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid867 : RecordDataValid section14Catalog 11 (⟨356,(9),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid868 : RecordDataValid section14Catalog 11 (⟨360,(0),[11],[2],1539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1539,[7,11],1544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid869 : RecordDataValid section14Catalog 11 (⟨360,(1),[11],[2],942⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨942,[3,7,11],946⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid870 : RecordDataValid section14Catalog 11 (⟨360,(2),[11],[2],941⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨941,[3,7,11],945⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid871 : RecordDataValid section14Catalog 11 (⟨360,(3),[11],[2],943⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨943,[3,7,11],947⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid872 : RecordDataValid section14Catalog 11 (⟨363,(0),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid873 : RecordDataValid section14Catalog 11 (⟨363,(1),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid874 : RecordDataValid section14Catalog 11 (⟨363,(2),[11],[2],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid875 : RecordDataValid section14Catalog 11 (⟨363,(3),[11],[2],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid876 : RecordDataValid section14Catalog 11 (⟨365,(0),[11],[2],337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨337,[1,2,3,4,5,6,7,8,9,10,11,12],338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid877 : RecordDataValid section14Catalog 11 (⟨365,(1),[11],[2],944⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨944,[3,7,11],948⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid878 : RecordDataValid section14Catalog 11 (⟨365,(2),[11],[2],945⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨945,[3,7,11],949⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid879 : RecordDataValid section14Catalog 11 (⟨365,(3),[11],[2],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid880 : RecordDataValid section14Catalog 11 (⟨365,(4),[11],[2],940⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨940,[3,7,11],944⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid881 : RecordDataValid section14Catalog 11 (⟨368,(0),[11],[2],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid882 : RecordDataValid section14Catalog 11 (⟨368,(1),[11],[2],347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨347,[1,2,3,5,6,7,9,10,11],348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid883 : RecordDataValid section14Catalog 11 (⟨368,(2),[11],[2],348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨348,[1,2,3,5,6,7,9,10,11],349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid884 : RecordDataValid section14Catalog 11 (⟨368,(3),[11],[2],348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨348,[1,2,3,5,6,7,9,10,11],349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid885 : RecordDataValid section14Catalog 11 (⟨368,(4),[11],[2],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid886 : RecordDataValid section14Catalog 11 (⟨368,(5),[11],[2],351⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨351,[1,2,3,5,6,7,9,10,11],352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid887 : RecordDataValid section14Catalog 11 (⟨368,(6),[11],[2],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid888 : RecordDataValid section14Catalog 11 (⟨368,(7),[11],[2],353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨353,[1,2,3,5,6,7,9,10,11],354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid889 : RecordDataValid section14Catalog 11 (⟨368,(8),[11],[2],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid890 : RecordDataValid section14Catalog 11 (⟨368,(9),[11],[2],351⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨351,[1,2,3,5,6,7,9,10,11],352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid891 : RecordDataValid section14Catalog 11 (⟨372,(0),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid892 : RecordDataValid section14Catalog 11 (⟨372,(1),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid893 : RecordDataValid section14Catalog 11 (⟨372,(2),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid894 : RecordDataValid section14Catalog 11 (⟨372,(3),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid895 : RecordDataValid section14Catalog 11 (⟨372,(4),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid896 : RecordDataValid section14Catalog 11 (⟨372,(5),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid897 : RecordDataValid section14Catalog 11 (⟨372,(6),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid898 : RecordDataValid section14Catalog 11 (⟨372,(7),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid899 : RecordDataValid section14Catalog 11 (⟨372,(8),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid900 : RecordDataValid section14Catalog 11 (⟨372,(9),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid901 : RecordDataValid section14Catalog 11 (⟨376,(0),[11],[2],1541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1541,[7,11],1546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid902 : RecordDataValid section14Catalog 11 (⟨376,(1),[11],[2],947⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨947,[3,7,11],951⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid903 : RecordDataValid section14Catalog 11 (⟨376,(2),[11],[2],946⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨946,[3,7,11],950⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid904 : RecordDataValid section14Catalog 11 (⟨376,(3),[11],[2],948⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨948,[3,7,11],952⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid905 : RecordDataValid section14Catalog 11 (⟨379,(0),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid906 : RecordDataValid section14Catalog 11 (⟨379,(1),[11],[2],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid907 : RecordDataValid section14Catalog 11 (⟨379,(2),[11],[2],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid908 : RecordDataValid section14Catalog 11 (⟨379,(3),[11],[2],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid909 : RecordDataValid section14Catalog 11 (⟨381,(0),[11],[2],364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨364,[1,2,3,4,5,6,7,8,9,10,11,12],365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid910 : RecordDataValid section14Catalog 11 (⟨381,(1),[11],[2],949⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨949,[3,7,11],953⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid911 : RecordDataValid section14Catalog 11 (⟨381,(2),[11],[2],945⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨945,[3,7,11],949⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid912 : RecordDataValid section14Catalog 11 (⟨381,(3),[11],[2],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid913 : RecordDataValid section14Catalog 11 (⟨381,(4),[11],[2],950⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨950,[3,7,11],954⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid914 : RecordDataValid section14Catalog 11 (⟨399,(0),[11],[2],1692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1692,[11],1697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid915 : RecordDataValid section14Catalog 11 (⟨399,(1),[11],[2],1692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1692,[11],1697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid916 : RecordDataValid section14Catalog 11 (⟨399,(2),[11],[2],1693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1693,[11],1698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid917 : RecordDataValid section14Catalog 11 (⟨399,(3),[11],[2],1693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1693,[11],1698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid918 : RecordDataValid section14Catalog 11 (⟨399,(4),[11],[2],1694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1694,[11],1699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid919 : RecordDataValid section14Catalog 11 (⟨399,(5),[11],[2],1695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1695,[11],1700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid920 : RecordDataValid section14Catalog 11 (⟨399,(6),[11],[2],1694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1694,[11],1699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid921 : RecordDataValid section14Catalog 11 (⟨399,(7),[11],[2],1696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1696,[11],1701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid922 : RecordDataValid section14Catalog 11 (⟨399,(8),[11],[2],1694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1694,[11],1699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid923 : RecordDataValid section14Catalog 11 (⟨399,(9),[11],[2],1695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1695,[11],1700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid924 : RecordDataValid section14Catalog 11 (⟨403,(0),[11],[2],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid925 : RecordDataValid section14Catalog 11 (⟨403,(1),[11],[2],951⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨951,[3,7,11,15],955⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid926 : RecordDataValid section14Catalog 11 (⟨403,(2),[11],[2],952⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨952,[3,7,11,15],956⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid927 : RecordDataValid section14Catalog 11 (⟨403,(3),[11],[2],953⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨953,[3,7,11,15],957⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 864).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 864).take 64 = [⟨356,(6),[11],[2],2⟩,⟨356,(7),[11],[2],2⟩,⟨356,(8),[11],[2],2⟩,⟨356,(9),[11],[2],2⟩,⟨360,(0),[11],[2],1539⟩,⟨360,(1),[11],[2],942⟩,⟨360,(2),[11],[2],941⟩,⟨360,(3),[11],[2],943⟩,⟨363,(0),[11],[2],2⟩,⟨363,(1),[11],[2],2⟩,⟨363,(2),[11],[2],159⟩,⟨363,(3),[11],[2],99⟩,⟨365,(0),[11],[2],337⟩,⟨365,(1),[11],[2],944⟩,⟨365,(2),[11],[2],945⟩,⟨365,(3),[11],[2],939⟩,⟨365,(4),[11],[2],940⟩,⟨368,(0),[11],[2],347⟩,⟨368,(1),[11],[2],347⟩,⟨368,(2),[11],[2],348⟩,⟨368,(3),[11],[2],348⟩,⟨368,(4),[11],[2],349⟩,⟨368,(5),[11],[2],351⟩,⟨368,(6),[11],[2],349⟩,⟨368,(7),[11],[2],353⟩,⟨368,(8),[11],[2],349⟩,⟨368,(9),[11],[2],351⟩,⟨372,(0),[11],[2],2⟩,⟨372,(1),[11],[2],2⟩,⟨372,(2),[11],[2],2⟩,⟨372,(3),[11],[2],2⟩,⟨372,(4),[11],[2],2⟩,⟨372,(5),[11],[2],2⟩,⟨372,(6),[11],[2],2⟩,⟨372,(7),[11],[2],2⟩,⟨372,(8),[11],[2],2⟩,⟨372,(9),[11],[2],2⟩,⟨376,(0),[11],[2],1541⟩,⟨376,(1),[11],[2],947⟩,⟨376,(2),[11],[2],946⟩,⟨376,(3),[11],[2],948⟩,⟨379,(0),[11],[2],2⟩,⟨379,(1),[11],[2],2⟩,⟨379,(2),[11],[2],159⟩,⟨379,(3),[11],[2],99⟩,⟨381,(0),[11],[2],364⟩,⟨381,(1),[11],[2],949⟩,⟨381,(2),[11],[2],945⟩,⟨381,(3),[11],[2],939⟩,⟨381,(4),[11],[2],950⟩,⟨399,(0),[11],[2],1692⟩,⟨399,(1),[11],[2],1692⟩,⟨399,(2),[11],[2],1693⟩,⟨399,(3),[11],[2],1693⟩,⟨399,(4),[11],[2],1694⟩,⟨399,(5),[11],[2],1695⟩,⟨399,(6),[11],[2],1694⟩,⟨399,(7),[11],[2],1696⟩,⟨399,(8),[11],[2],1694⟩,⟨399,(9),[11],[2],1695⟩,⟨403,(0),[11],[2],711⟩,⟨403,(1),[11],[2],951⟩,⟨403,(2),[11],[2],952⟩,⟨403,(3),[11],[2],953⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid864
  · exact recordValid_of_data section14Catalog 11 _ hnum valid865
  · exact recordValid_of_data section14Catalog 11 _ hnum valid866
  · exact recordValid_of_data section14Catalog 11 _ hnum valid867
  · exact recordValid_of_data section14Catalog 11 _ hnum valid868
  · exact recordValid_of_data section14Catalog 11 _ hnum valid869
  · exact recordValid_of_data section14Catalog 11 _ hnum valid870
  · exact recordValid_of_data section14Catalog 11 _ hnum valid871
  · exact recordValid_of_data section14Catalog 11 _ hnum valid872
  · exact recordValid_of_data section14Catalog 11 _ hnum valid873
  · exact recordValid_of_data section14Catalog 11 _ hnum valid874
  · exact recordValid_of_data section14Catalog 11 _ hnum valid875
  · exact recordValid_of_data section14Catalog 11 _ hnum valid876
  · exact recordValid_of_data section14Catalog 11 _ hnum valid877
  · exact recordValid_of_data section14Catalog 11 _ hnum valid878
  · exact recordValid_of_data section14Catalog 11 _ hnum valid879
  · exact recordValid_of_data section14Catalog 11 _ hnum valid880
  · exact recordValid_of_data section14Catalog 11 _ hnum valid881
  · exact recordValid_of_data section14Catalog 11 _ hnum valid882
  · exact recordValid_of_data section14Catalog 11 _ hnum valid883
  · exact recordValid_of_data section14Catalog 11 _ hnum valid884
  · exact recordValid_of_data section14Catalog 11 _ hnum valid885
  · exact recordValid_of_data section14Catalog 11 _ hnum valid886
  · exact recordValid_of_data section14Catalog 11 _ hnum valid887
  · exact recordValid_of_data section14Catalog 11 _ hnum valid888
  · exact recordValid_of_data section14Catalog 11 _ hnum valid889
  · exact recordValid_of_data section14Catalog 11 _ hnum valid890
  · exact recordValid_of_data section14Catalog 11 _ hnum valid891
  · exact recordValid_of_data section14Catalog 11 _ hnum valid892
  · exact recordValid_of_data section14Catalog 11 _ hnum valid893
  · exact recordValid_of_data section14Catalog 11 _ hnum valid894
  · exact recordValid_of_data section14Catalog 11 _ hnum valid895
  · exact recordValid_of_data section14Catalog 11 _ hnum valid896
  · exact recordValid_of_data section14Catalog 11 _ hnum valid897
  · exact recordValid_of_data section14Catalog 11 _ hnum valid898
  · exact recordValid_of_data section14Catalog 11 _ hnum valid899
  · exact recordValid_of_data section14Catalog 11 _ hnum valid900
  · exact recordValid_of_data section14Catalog 11 _ hnum valid901
  · exact recordValid_of_data section14Catalog 11 _ hnum valid902
  · exact recordValid_of_data section14Catalog 11 _ hnum valid903
  · exact recordValid_of_data section14Catalog 11 _ hnum valid904
  · exact recordValid_of_data section14Catalog 11 _ hnum valid905
  · exact recordValid_of_data section14Catalog 11 _ hnum valid906
  · exact recordValid_of_data section14Catalog 11 _ hnum valid907
  · exact recordValid_of_data section14Catalog 11 _ hnum valid908
  · exact recordValid_of_data section14Catalog 11 _ hnum valid909
  · exact recordValid_of_data section14Catalog 11 _ hnum valid910
  · exact recordValid_of_data section14Catalog 11 _ hnum valid911
  · exact recordValid_of_data section14Catalog 11 _ hnum valid912
  · exact recordValid_of_data section14Catalog 11 _ hnum valid913
  · exact recordValid_of_data section14Catalog 11 _ hnum valid914
  · exact recordValid_of_data section14Catalog 11 _ hnum valid915
  · exact recordValid_of_data section14Catalog 11 _ hnum valid916
  · exact recordValid_of_data section14Catalog 11 _ hnum valid917
  · exact recordValid_of_data section14Catalog 11 _ hnum valid918
  · exact recordValid_of_data section14Catalog 11 _ hnum valid919
  · exact recordValid_of_data section14Catalog 11 _ hnum valid920
  · exact recordValid_of_data section14Catalog 11 _ hnum valid921
  · exact recordValid_of_data section14Catalog 11 _ hnum valid922
  · exact recordValid_of_data section14Catalog 11 _ hnum valid923
  · exact recordValid_of_data section14Catalog 11 _ hnum valid924
  · exact recordValid_of_data section14Catalog 11 _ hnum valid925
  · exact recordValid_of_data section14Catalog 11 _ hnum valid926
  · exact recordValid_of_data section14Catalog 11 _ hnum valid927
end Section14Records_11_864_928

#print axioms solution
