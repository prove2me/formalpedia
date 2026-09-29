-- Prove2me | solution 1 for Freiman.section14_s0016_records_0864_0896
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:08:46.496802+00:00
-- url     : https://prove2.me/submissions/59ad8722-d069-4e38-881a-53db5443456a

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
namespace Section14Records_16_864_896
private theorem valid864 : RecordDataValid section14Catalog 16 (⟨146,(3),[4,8,12,16],[10],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid865 : RecordDataValid section14Catalog 16 (⟨146,(4),[4,8,12,16],[10],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid866 : RecordDataValid section14Catalog 16 (⟨146,(5),[4,8,12,16],[10],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid867 : RecordDataValid section14Catalog 16 (⟨146,(6),[4,8,12,16],[10],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid868 : RecordDataValid section14Catalog 16 (⟨146,(7),[4,8,12,16],[10],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid869 : RecordDataValid section14Catalog 16 (⟨146,(8),[4,8,12,16],[10],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid870 : RecordDataValid section14Catalog 16 (⟨146,(9),[4,8,12,16],[10],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid871 : RecordDataValid section14Catalog 16 (⟨146,(10),[4,8,12,16],[10],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid872 : RecordDataValid section14Catalog 16 (⟨146,(11),[4,8,12,16],[10],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid873 : RecordDataValid section14Catalog 16 (⟨146,(12),[4,8,12,16],[10],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid874 : RecordDataValid section14Catalog 16 (⟨146,(13),[4,8,12,16],[10],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid875 : RecordDataValid section14Catalog 16 (⟨146,(14),[4,8,12,16],[10],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid876 : RecordDataValid section14Catalog 16 (⟨146,(15),[4,8,12,16],[10],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid877 : RecordDataValid section14Catalog 16 (⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid878 : RecordDataValid section14Catalog 16 (⟨153,(-1),[3,4,7,8,12,15,16],[5],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid879 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,8,10,12,16],[8,12],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid880 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,8,11,12,16],[1],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid881 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,8,12,16],[9,13],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid882 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,8,12,16],[2],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid883 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,8,12,16],[7,11,15],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid884 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,8,12,16],[6],637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid885 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,8,12,16],[14],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid886 : RecordDataValid section14Catalog 16 (⟨153,(-1),[4,16],[3],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid887 : RecordDataValid section14Catalog 16 (⟨157,(0),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid888 : RecordDataValid section14Catalog 16 (⟨157,(1),[4,8,16],[10],1272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1272,[4,8,16],1276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid889 : RecordDataValid section14Catalog 16 (⟨157,(2),[4,8,16],[10],1273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1273,[4,8,16],1277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid890 : RecordDataValid section14Catalog 16 (⟨157,(3),[4,8,16],[10],1274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1274,[4,8,16],1278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid891 : RecordDataValid section14Catalog 16 (⟨157,(4),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid892 : RecordDataValid section14Catalog 16 (⟨157,(5),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid893 : RecordDataValid section14Catalog 16 (⟨157,(6),[4,8,16],[10],1272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1272,[4,8,16],1276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid894 : RecordDataValid section14Catalog 16 (⟨157,(7),[4,8,16],[10],1273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1273,[4,8,16],1277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid895 : RecordDataValid section14Catalog 16 (⟨157,(8),[4,8,16],[10],1274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1274,[4,8,16],1278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 864).take 32 = [⟨146,(3),[4,8,12,16],[10],871⟩,⟨146,(4),[4,8,12,16],[10],609⟩,⟨146,(5),[4,8,12,16],[10],610⟩,⟨146,(6),[4,8,12,16],[10],611⟩,⟨146,(7),[4,8,12,16],[10],612⟩,⟨146,(8),[4,8,12,16],[10],613⟩,⟨146,(9),[4,8,12,16],[10],614⟩,⟨146,(10),[4,8,12,16],[10],615⟩,⟨146,(11),[4,8,12,16],[10],616⟩,⟨146,(12),[4,8,12,16],[10],617⟩,⟨146,(13),[4,8,12,16],[10],618⟩,⟨146,(14),[4,8,12,16],[10],619⟩,⟨146,(15),[4,8,12,16],[10],620⟩,⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩,⟨153,(-1),[3,4,7,8,12,15,16],[5],633⟩,⟨153,(-1),[4,8,10,12,16],[8,12],632⟩,⟨153,(-1),[4,8,11,12,16],[1],633⟩,⟨153,(-1),[4,8,12,16],[9,13],633⟩,⟨153,(-1),[4,8,12,16],[2],634⟩,⟨153,(-1),[4,8,12,16],[7,11,15],636⟩,⟨153,(-1),[4,8,12,16],[6],637⟩,⟨153,(-1),[4,8,12,16],[14],879⟩,⟨153,(-1),[4,16],[3],634⟩,⟨157,(0),[3,4,7,8,15,16],[10],10⟩,⟨157,(1),[4,8,16],[10],1272⟩,⟨157,(2),[4,8,16],[10],1273⟩,⟨157,(3),[4,8,16],[10],1274⟩,⟨157,(4),[4,8,16],[10],1275⟩,⟨157,(5),[3,4,7,8,15,16],[10],10⟩,⟨157,(6),[4,8,16],[10],1272⟩,⟨157,(7),[4,8,16],[10],1273⟩,⟨157,(8),[4,8,16],[10],1274⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid864
  · exact recordValid_of_data section14Catalog 16 _ hnum valid865
  · exact recordValid_of_data section14Catalog 16 _ hnum valid866
  · exact recordValid_of_data section14Catalog 16 _ hnum valid867
  · exact recordValid_of_data section14Catalog 16 _ hnum valid868
  · exact recordValid_of_data section14Catalog 16 _ hnum valid869
  · exact recordValid_of_data section14Catalog 16 _ hnum valid870
  · exact recordValid_of_data section14Catalog 16 _ hnum valid871
  · exact recordValid_of_data section14Catalog 16 _ hnum valid872
  · exact recordValid_of_data section14Catalog 16 _ hnum valid873
  · exact recordValid_of_data section14Catalog 16 _ hnum valid874
  · exact recordValid_of_data section14Catalog 16 _ hnum valid875
  · exact recordValid_of_data section14Catalog 16 _ hnum valid876
  · exact recordValid_of_data section14Catalog 16 _ hnum valid877
  · exact recordValid_of_data section14Catalog 16 _ hnum valid878
  · exact recordValid_of_data section14Catalog 16 _ hnum valid879
  · exact recordValid_of_data section14Catalog 16 _ hnum valid880
  · exact recordValid_of_data section14Catalog 16 _ hnum valid881
  · exact recordValid_of_data section14Catalog 16 _ hnum valid882
  · exact recordValid_of_data section14Catalog 16 _ hnum valid883
  · exact recordValid_of_data section14Catalog 16 _ hnum valid884
  · exact recordValid_of_data section14Catalog 16 _ hnum valid885
  · exact recordValid_of_data section14Catalog 16 _ hnum valid886
  · exact recordValid_of_data section14Catalog 16 _ hnum valid887
  · exact recordValid_of_data section14Catalog 16 _ hnum valid888
  · exact recordValid_of_data section14Catalog 16 _ hnum valid889
  · exact recordValid_of_data section14Catalog 16 _ hnum valid890
  · exact recordValid_of_data section14Catalog 16 _ hnum valid891
  · exact recordValid_of_data section14Catalog 16 _ hnum valid892
  · exact recordValid_of_data section14Catalog 16 _ hnum valid893
  · exact recordValid_of_data section14Catalog 16 _ hnum valid894
  · exact recordValid_of_data section14Catalog 16 _ hnum valid895
end Section14Records_16_864_896

#print axioms solution
