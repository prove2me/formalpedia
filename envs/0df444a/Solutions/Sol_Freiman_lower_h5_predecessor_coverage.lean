-- Prove2me | solution 1 for Freiman.lower_h5_predecessor_coverage
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T09:40:50.887457+00:00
-- url     : https://prove2.me/submissions/bf8aaf53-85d0-418d-954c-b6eda7dcdeca

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerH5Data
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Definitions.Def_Freiman_certificates
import Definitions.Def_Freiman_lowerH5Model
import Theorems.Thm_Freiman_lowerHistory_goodness_from_endpoints
import Theorems.Thm_Freiman_lowerHistory_greater_from_sign
import Theorems.Thm_Freiman_lowerHistory_equal_endpoint_cases
import Theorems.Thm_Freiman_lowerHistory_mixed_endpoint_cases
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerHistory_pull_from_mobius
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Theorems.Thm_Freiman_cert_witness_excludes


open Freiman
attribute [local instance] Classical.propDecidable

namespace M7H5CoverageCuts14

private theorem threshold_value (c : CertField) (x y : CertField × CertField)
    (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold, lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

private theorem tau_nonnegative : 0 ≤ certFieldVal lowerHistoryTau := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [lowerHistoryTau, certFieldVal]

private theorem cf213_value :
    certFieldVal (lowerHistoryCF [2,1,3] lowerHistoryTau) = lowerTheta 30 := by
  rw [Freiman.lowerHistory_cf_value _ _ tau_nonnegative]
  norm_num [certFieldVal, lowerHistoryTau, lowerTau, lowerTheta]
  congr 1 <;> ring

private theorem h7_value (p : LowerPair) :
    certThresholdVal lowerHistoryH7.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (31/100) 3 63 25 66 := by
  simp only [lowerHistoryH7, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 3 (by simp),
    lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 66 (by simp)]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem h9_value (p : LowerPair) :
    certThresholdVal lowerHistoryH9.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 := by
  simp only [lowerHistoryH9, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 36 (by simp),
    lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 66 (by simp)]
  norm_num [certFieldVal]
  ring

private theorem h18_value (p : LowerPair) :
    certThresholdVal lowerH5H18.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (183/250) 25 36 30 63 := by
  simp only [lowerH5H18, threshold_value, lowerThreshold,
    lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 36 (by simp),
    lowerHistory_theta_values 63 (by simp), cf213_value]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem h2_value (p : LowerPair) :
    certThresholdVal lowerHistoryH2.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (37/50) 63 70 66 90 := by
  simp only [lowerHistoryH2, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 70 (by simp),
    lowerHistory_theta_values 66 (by simp),
    lowerHistory_theta_values 90 (by simp)]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem h5_value (p : LowerPair) :
    certThresholdVal lowerHistoryH5.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (279/500) 35 63 63 70 := by
  simp only [lowerHistoryH5, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 35 (by simp),
    lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 70 (by simp)]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem a3_cut (p : LowerPair) (h : lowerA p 3) :
    lowerHistoryAtBase (lowerNormalize p) [lowerHistoryComplement lowerHistoryH7] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  subst b
  change lowerScale (lowerNormalize p) < certThresholdVal lowerHistoryH7.threshold
    (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
  rw [h7_value p]
  exact h

private theorem a9_a16_cuts (p : LowerPair) (h3 : ¬lowerA p 3)
    (h9 : lowerA p 9) (h16 : lowerA p 16) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryH7,lowerHistoryH9,lowerHistoryComplement lowerH5H18] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · change certThresholdVal lowerHistoryH7.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) ≤
      lowerScale (lowerNormalize p)
    rw [h7_value p]
    exact le_of_not_gt h3
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH9.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
    rw [h9_value p]
    exact h9
  · change certThresholdVal lowerH5H18.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) <
      lowerScale (lowerNormalize p)
    rw [h18_value p]
    exact h16

private theorem a9_not_a16_cuts (p : LowerPair) (h3 : ¬lowerA p 3)
    (h9 : lowerA p 9) (h16 : ¬lowerA p 16) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryH7,lowerHistoryH9,lowerH5H18] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · change certThresholdVal lowerHistoryH7.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) ≤
      lowerScale (lowerNormalize p)
    rw [h7_value p]
    exact le_of_not_gt h3
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH9.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
    rw [h9_value p]
    exact h9
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerH5H18.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
    rw [h18_value p]
    exact le_of_not_gt h16

private theorem not_h2_not_h5_cuts (p : LowerPair) (h2 : ¬lowerH p 2) (h5 : ¬lowerH p 5) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH2.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
    rw [h2_value p]
    exact le_of_not_gt h2
  · change certThresholdVal lowerHistoryH5.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) ≤
      lowerScale (lowerNormalize p)
    rw [h5_value p]
    exact le_of_not_gt h5

end M7H5CoverageCuts14


open Freiman
namespace M7H5CatalogPick14

private def fitsKey (z : LowerH5Kind × LowerPair) (c : LowerH5Case) : Prop :=
  c.kind = z.1 ∧
  c.context = ⟨z.2,lowerH5ExpectedParity z.1⟩ ∧
  c.words = lowerH5ExpectedWords z.1 ∧
  c.reflect = decide (z.1 ≠ .a) ∧
  c.oldCuts.toFinset = (lowerH5ExpectedCuts z.1).toFinset

private instance (z : LowerH5Kind × LowerPair) (c : LowerH5Case) :
    Decidable (fitsKey z c) := by
  unfold fitsKey
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem catalog_check :
    ∀ z ∈ lowerH5ExpectedKeys, ∃ c ∈ lowerH5Cases, fitsKey z c := by
  decide +kernel

private theorem catalog_pick (k : LowerH5Kind) (x y : List ℕ+)
    (hk : (k,(x,y)) ∈ lowerH5ExpectedKeys) :
    ∃ c ∈ lowerH5Cases,
      c.kind = k ∧
      c.context = ⟨(x,y), lowerH5ExpectedParity k⟩ ∧
      c.words = lowerH5ExpectedWords k ∧
      c.reflect = decide (k ≠ .a) ∧
      c.oldCuts.toFinset = (lowerH5ExpectedCuts k).toFinset :=
  catalog_check (k,(x,y)) hk

private theorem cuts_transfer (base : LowerPair) (c : LowerH5Case) (k : LowerH5Kind)
    (he : c.oldCuts.toFinset = (lowerH5ExpectedCuts k).toFinset)
    (hc : lowerHistoryAtBase base (lowerH5ExpectedCuts k)) :
    lowerHistoryAtBase base c.oldCuts := by
  intro b hb
  apply hc b
  apply List.mem_toFinset.mp
  rw [←he]
  exact List.mem_toFinset.mpr hb

end M7H5CatalogPick14


open Freiman
namespace M7H5Nonreflect14

private def lowerB : CertBound :=
  ⟨true,false,⟨⟨-363/299,257/299,0,0⟩,⟨4/13,1/13,0,0⟩,
    ⟨9/13,-1/13,0,0⟩,⟨15/37,-1/37,0,0⟩,⟨1/2,1/6,0,0⟩⟩⟩
private def upperB : CertBound :=
  ⟨false,true,⟨⟨871317/2766500,-100161/5533000,0,0⟩,
    ⟨735/1006,1/1006,0,0⟩,⟨17/22,-1/22,0,0⟩,
    ⟨4/13,1/13,0,0⟩,⟨125/214,-1/214,0,0⟩⟩⟩
private def rect : CertRectangle := ⟨1/4,1/3,3/4,4/5⟩
private def witness : CertWitness :=
  ⟨lowerB,upperB,rect,
    certBernsteinCoefficients (certCrossPolynomial lowerB.threshold upperB.threshold) rect,
    fun _ _ => 0⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem valid : certWitnessValid witness := by
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,Or.inr (Or.inr rfl)⟩
  · norm_num [witness,rect,certRectangleValid]
  · norm_num [witness,rect]
  · norm_num [witness,lowerB,certThresholdDataValid,certFieldLower,
      certDirectedTerm,certSqrt3Lower,certSqrt3Upper,certSqrt7Lower,certSqrt7Upper,
      certSqrt21Lower,certSqrt21Upper]
  · norm_num [witness,upperB,certThresholdDataValid,certFieldLower,
      certDirectedTerm,certSqrt3Lower,certSqrt3Upper,certSqrt7Lower,certSqrt7Upper,
      certSqrt21Lower,certSqrt21Upper]
  · intro i j
    simp only [certCoefficientBoundValid, show witness.lowerBounds i j = 0 from rfl,
      le_refl, if_true, true_and]
    fin_cases i <;> fin_cases j <;> decide +kernel

end M7H5Nonreflect14


open Freiman
namespace M7H5Nonreflect14
attribute [local instance] Classical.propDecidable

private theorem endpointLaw : LowerHistoryEndpointLaw := by
  intro base C hc w upper
  by_cases hp : lowerHistoryWordParity C w false = lowerHistoryWordParity C w true
  · exact lowerHistory_equal_endpoint_cases lowerHistory_width_threshold
      lowerHistory_cf_value base C hc w upper hp
  · exact lowerHistory_mixed_endpoint_cases lowerHistory_width_threshold
      lowerHistory_cf_value base C hc w upper hp

private theorem goodLaw : LowerHistoryGoodnessLaw :=
  lowerHistory_goodness_from_endpoints
    (lowerHistory_greater_from_sign lowerHistory_sign_value) endpointLaw

private theorem pullLaw : LowerHistoryPullLaw :=
  lowerHistory_pull_from_mobius lowerHistory_cf_value lowerHistory_inv_value

private def context : LowerHistoryContext := ⟨([3],[3,1]),(false,false)⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem relaxed_eq : lowerHistoryRelaxedGoodness context = some [lowerB] := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem pull_eq : lowerHistoryPull lowerHistoryH5 ([1],[]) false = upperB := by
  decide +kernel

private theorem normalize_idem (p : LowerPair) :
    lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  unfold lowerNormalize
  split_ifs <;> simp_all
  all_goals (exfalso; linarith)

private theorem good_normalize (p : LowerPair) (hg : lowerGood p) :
    lowerGood (lowerNormalize p) := by
  simpa only [lowerGood,lowerChild,normalize_idem] using hg

private theorem box_normalize (p : LowerPair) (hb : lowerParameterBox p) :
    lowerParameterBox (lowerNormalize p) := by
  unfold lowerNormalize
  split_ifs
  · exact hb
  · exact ⟨hb.2.2.1,hb.2.2.2,hb.1,hb.2.1⟩

private theorem ends3_not31 (w : List ℕ+) (h3 : lowerEnds w [3]) :
    ¬lowerEnds w [3,1] := by
  intro h31
  have h := (h3.getLast (by simp)).trans (h31.getLast (by simp)).symm
  norm_num at h

private theorem fits (q : LowerPair)
    (hl : lowerEnds q.1 [3]) (hr : lowerEnds q.2 [3,1])
    (hp : q.1.length % 2 = q.2.length % 2) :
    lowerHistoryContextFits q context := by
  have hn1 := ends3_not31 q.1 hl
  have hn2 : ¬lowerEnds q.2 [3] := fun h => ends3_not31 q.2 h hr
  refine ⟨⟨hl,?_,?_⟩,⟨hr,?_,?_⟩,?_⟩
  · change lowerEnds q.1 [3] ↔ lowerEnds [3] [3]
    exact iff_of_true hl (by unfold lowerEnds; decide)
  · change lowerEnds q.1 [3,1] ↔ lowerEnds [3] [3,1]
    exact iff_of_false hn1 (by unfold lowerEnds; decide)
  · change lowerEnds q.2 [3] ↔ lowerEnds [3,1] [3]
    exact iff_of_false hn2 (by unfold lowerEnds; decide)
  · change lowerEnds q.2 [3,1] ↔ lowerEnds [3,1] [3,1]
    exact iff_of_true hr (by unfold lowerEnds; decide)
  · simp [context,hp]

private theorem ratio_three (w : List ℕ+) (hs : lowerEnds w [3]) :
    lowerRatio w ≤ (1/3 : ℝ) := by
  obtain ⟨u,rfl⟩ := hs
  rw [lowerEarlyTerminal_ratio_append]
  norm_num only [List.reverse_cons,List.reverse_nil,List.nil_append,prefixEval,
    PNat.val_ofNat,Nat.cast_ofNat]
  have hr := (lowerEarlyTerminal_ratio_range u).1
  apply (div_le_iff₀ (by linarith : 0 < 3 + lowerRatio u)).2
  linarith

private theorem ratio_three_one (w : List ℕ+) (hs : lowerEnds w [3,1]) :
    (3/4 : ℝ) ≤ lowerRatio w := by
  obtain ⟨u,rfl⟩ := hs
  rw [lowerEarlyTerminal_ratio_append]
  norm_num only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    prefixEval,PNat.val_ofNat,Nat.cast_ofNat,Nat.cast_one]
  have hr := (lowerEarlyTerminal_ratio_range u).1
  have hd : 0 < 3 + lowerRatio u := by linarith
  have hu : (1 : ℝ)/(3+lowerRatio u) ≤ 1/3 := by
    apply (div_le_iff₀ hd).2
    linarith
  apply (le_div_iff₀ (by positivity : 0 < 1 + 1/(3+lowerRatio u))).2
  linarith

private theorem in_rectangle (q : LowerPair) (hb : lowerParameterBox q)
    (hl : lowerEnds q.1 [3]) (hr : lowerEnds q.2 [3,1]) :
    certRectangleMem rect (lowerRatio q.1) (lowerRatio q.2) := by
  norm_num only [certRectangleMem,rect,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]
  exact ⟨hb.1,ratio_three _ hl,ratio_three_one _ hr,hb.2.2.2⟩

private theorem threshold_value (c : CertField) (x y : CertField × CertField)
    (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold,lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal,certThresholdNum,certThresholdDen] <;> ring

private theorem h5_value (p : LowerPair) :
    certThresholdVal lowerHistoryH5.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (279/500) 35 63 63 70 := by
  simp only [lowerHistoryH5,lowerHistoryPB,threshold_value,lowerThreshold,
    lowerHistory_theta_values 35 (by simp),
    lowerHistory_theta_values 63 (by simp),lowerHistory_theta_values 70 (by simp)]
  norm_num [lowerHistoryRat,certFieldVal]

private theorem nonreflect_bounds (p : LowerPair)
    (hg : lowerGood p) (hb : lowerParameterBox p)
    (hl : lowerEnds (lowerNormalize p).1 [3])
    (hr : lowerEnds (lowerNormalize p).2 [3,1])
    (hn : lowerNormalize (lowerChild p ([1],[])) = lowerChild p ([1],[]))
    (ha : lowerH5Active (lowerChild p ([1],[]))) :
    certRectangleMem rect (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) ∧
    lowerHistoryAtBase (lowerNormalize p) [lowerB,upperB] := by
  let q := lowerNormalize p
  have hpar : q.1.length % 2 = q.2.length % 2 := by
    have hm := ha.1
    simp only [lowerMixed,lowerChild,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.length_append,List.length_cons,List.length_nil] at hm
    dsimp [q]
    omega
  have hf := fits q hl hr hpar
  obtain ⟨bs,hbs,hbsval⟩ := goodLaw q context hf (normalize_idem p) (good_normalize p hg)
  rw [relaxed_eq,Option.some.injEq] at hbs
  subst bs
  have hu : lowerHistoryAtBase (lowerNormalize (lowerChild p ([1],[]))) [lowerHistoryH5] := by
    intro b hmem
    simp only [List.mem_singleton] at hmem
    subst b
    change lowerScale (lowerNormalize (lowerChild p ([1],[]))) <
      certThresholdVal lowerHistoryH5.threshold
        (lowerRatio (lowerNormalize (lowerChild p ([1],[]))).1)
        (lowerRatio (lowerNormalize (lowerChild p ([1],[]))).2)
    rw [h5_value]
    exact ha.2.2.1
  rw [hn] at hu
  have hfields :
      0 < certFieldVal lowerHistoryH5.threshold.c ∧
      0 ≤ certFieldVal lowerHistoryH5.threshold.x0 ∧
      0 ≤ certFieldVal lowerHistoryH5.threshold.x1 ∧
      0 ≤ certFieldVal lowerHistoryH5.threshold.y0 ∧
      0 ≤ certFieldVal lowerHistoryH5.threshold.y1 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    norm_num [lowerHistoryH5,lowerHistoryPB,lowerHistoryThreshold,lowerHistorySort,
      lowerHistoryLex,lowerHistoryTheta,lowerHistoryCF,lowerHistoryMatrix,
      lowerHistoryDiv,lowerHistoryInv,lowerHistoryRat,lowerHistoryTau,
      certFieldScale,certFieldAdd,certFieldSub,certFieldMul,certFieldVal]
    all_goals (repeat' constructor) <;> nlinarith
  have hpu := (pullLaw q ([1],[]) lowerHistoryH5 false hfields.1 hfields.2.1
    hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2).mp
      (by simpa [lowerHistoryOrient,lowerHistoryAppend,lowerChild,q] using hu)
  rw [pull_eq] at hpu
  refine ⟨in_rectangle q (box_normalize p hb) hl hr,?_⟩
  intro b hmem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl
  · exact hbsval lowerB (by simp)
  · exact hpu upperB (by simp)

end M7H5Nonreflect14


open Freiman
namespace M7H5Nonreflect14

private theorem h5_one_nonreflect_impossible {t : ℝ} (p : LowerPair)
    (hs : lowerState t p)
    (hl : lowerEnds (lowerNormalize p).1 [3])
    (hr : lowerEnds (lowerNormalize p).2 [3,1])
    (hn : lowerNormalize (lowerChild p ([1],[])) = lowerChild p ([1],[]))
    (ha : lowerH5Active (lowerChild p ([1],[]))) : False := by
  obtain ⟨hrect,hbounds⟩ := nonreflect_bounds p hs.2.1 hs.2.2.2 hl hr hn ha
  exact cert_witness_excludes witness valid
    (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
    (lowerScale (lowerNormalize p)) hrect
    ⟨hbounds lowerB (by simp),hbounds upperB (by simp)⟩

end M7H5Nonreflect14

set_option maxRecDepth 20000

open Freiman
attribute [local instance] Classical.propDecidable

private theorem suffix3_getlast (w : List ℕ+) : lowerEnds w [3] ↔ w.getLast? = some 3 := by
  constructor
  · intro h
    rcases h with ⟨u,rfl⟩
    simp
  · intro h
    rw [List.getLast?_eq_some_iff] at h
    obtain ⟨l, rfl⟩ := h
    exact List.suffix_append _ _

private theorem guardSuffix_iff (w u : List ℕ+) :
    lowerGuardSuffix w u = true ↔ lowerEnds w u := by
  constructor
  · intro h
    simp only [lowerGuardSuffix, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [lowerEnds, List.suffix_iff_eq_drop]
    exact h.2.symm
  · intro h
    simp only [lowerGuardSuffix, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.length_le, (List.suffix_iff_eq_drop.mp h).symm⟩

private theorem state_suffix3 (w : List ℕ+) :
    lowerEnds (lowerGuardState w) [3] ↔ lowerEnds w [3] := by
  unfold lowerGuardState
  split_ifs with h3131 h313 h31 h3
  · constructor
    · intro hs
      exact False.elim (by
        have z := hs.getLast (by simp)
        norm_num at z)
    · intro h; exact False.elim (by
        have a := h.getLast (by simp)
        have b := (guardSuffix_iff _ _).mp h3131 |>.getLast (by simp)
        have : (3 : ℕ+) = 1 := a.trans b.symm
        norm_num at this)
  · constructor
    · intro _
      exact List.IsSuffix.trans (List.suffix_append [3,1] [3])
        ((guardSuffix_iff _ _).mp h313)
    · intro _
      exact List.suffix_append [3,1] [3]
  · constructor
    · intro hs
      exact False.elim (by
        have z := hs.getLast (by simp)
        norm_num at z)
    · intro h; exact False.elim (by
        have a := h.getLast (by simp)
        have b := (guardSuffix_iff _ _).mp h31 |>.getLast (by simp)
        have : (3 : ℕ+) = 1 := a.trans b.symm
        norm_num at this)
  · constructor
    · exact fun _ => (guardSuffix_iff _ _).mp h3
    · intro _
      exact List.suffix_append [] [3]
  · rw [show w.drop (w.length - 1) = (if hw : w = [] then [] else [w.getLast hw]) by
      split_ifs with hw
      · subst w; rfl
      · exact List.drop_length_sub_one hw]
    split_ifs with hw
    · subst w; simp
    · rw [suffix3_getlast, suffix3_getlast]
      have hn : ¬ lowerEnds w [3] := by
        intro hs
        exact h3 ((guardSuffix_iff _ _).mpr hs)
      simpa [List.getLast?_eq_getLast, hw] using hn

private theorem state_suffix31 (w : List ℕ+) :
    lowerEnds (lowerGuardState w) [3,1] ↔ lowerEnds w [3,1] := by
  unfold lowerGuardState
  split_ifs with h3131 h313 h31 h3
  · constructor
    · intro _
      exact List.IsSuffix.trans (List.suffix_append [3,1] [3,1])
        ((guardSuffix_iff _ _).mp h3131)
    · intro _
      exact List.suffix_append [3,1] [3,1]
  · constructor
    · intro hs
      exact False.elim (by
        have z := hs.getLast (by simp)
        norm_num at z)
    · intro hs
      exact False.elim (by
        have a := hs.getLast (by simp)
        have b := (guardSuffix_iff _ _).mp h313 |>.getLast (by simp)
        have : (1 : ℕ+) = 3 := a.trans b.symm
        norm_num at this)
  · constructor
    · intro _; exact (guardSuffix_iff _ _).mp h31
    · intro _; exact List.suffix_append [] [3,1]
  · constructor
    · intro hs
      exact False.elim (by have z := hs.length_le; norm_num at z)
    · intro hs
      exact (h31 ((guardSuffix_iff _ _).mpr hs)).elim
  · constructor
    · intro hs
      by_cases hw : w = []
      · subst w
        have z := hs.length_le
        norm_num at z
      · rw [List.drop_length_sub_one hw] at hs
        have z := hs.length_le
        norm_num at z
    · intro hs
      exact (h31 ((guardSuffix_iff _ _).mpr hs)).elim

private theorem suffix_append_iff_of_length_le (s w u : List ℕ+) (hu : s.length ≤ u.length) :
    lowerEnds (w ++ u) s ↔ lowerEnds u s := by
  simp only [lowerEnds, List.suffix_iff_eq_drop]
  have he : (w ++ u).length - s.length = w.length + (u.length - s.length) := by
    simp only [List.length_append]
    omega
  rw [he, List.drop_length_add_append]

private theorem suffix3_append_state (w u : List ℕ+) :
    lowerEnds (w ++ u) [3] ↔ lowerEnds (lowerGuardState w ++ u) [3] := by
  cases u with
  | nil => simpa using (state_suffix3 w).symm
  | cons a u =>
      rw [suffix_append_iff_of_length_le [3] w (a::u) (by simp),
        suffix_append_iff_of_length_le [3] (lowerGuardState w) (a::u) (by simp)]

private theorem suffix31_append_state (w u : List ℕ+) :
    lowerEnds (w ++ u) [3,1] ↔ lowerEnds (lowerGuardState w ++ u) [3,1] := by
  cases u with
  | nil => simpa using (state_suffix31 w).symm
  | cons a u =>
      cases u with
      | nil =>
          change [3] ++ [1] <:+ w ++ [a] ↔
            [3] ++ [1] <:+ lowerGuardState w ++ [a]
          rw [List.suffix_append_inj_of_length_eq (by simp),
            List.suffix_append_inj_of_length_eq (by simp)]
          change lowerEnds w [3] ∧ [1] = [a] ↔
            lowerEnds (lowerGuardState w) [3] ∧ [1] = [a]
          rw [state_suffix3]
      | cons b u =>
          rw [suffix_append_iff_of_length_le [3,1] w (a::b::u) (by simp),
            suffix_append_iff_of_length_le [3,1] (lowerGuardState w) (a::b::u) (by simp)]

private def finalMixed (c : LowerGuardCase) (l : LowerLabel) : Bool :=
  c.mixed.xor (decide (l.1.length % 2 ≠ l.2.length % 2))

private def leftContexts : List (List ℕ+) := [[1],[2],[3],[3,1]]

private def h5ContextState (s : List ℕ+) : List ℕ+ :=
  if lowerGuardSuffix s [3,1] then [3,1] else s.drop (s.length-1)

private def noReflectShape (c : LowerGuardCase) (l : LowerLabel) : Prop :=
  c.mixed = false ∧ h5ContextState c.before.1 = [3] ∧
    h5ContextState c.before.2 ∈ [[1],[2]] ∧ l = ([1],[])

private def reflectShape (c : LowerGuardCase) (l : LowerLabel) : Prop :=
  (c.mixed = false ∧ h5ContextState c.before.1 ∈ leftContexts ∧
    h5ContextState c.before.2 = [3,1] ∧
    (l = ([1],[]) ∨ (l = ([2],[]) ∧
      c.branch ∈ ["E/H3","E/H9/H16","E/H9/notH16","E/H9/left31"]))) ∨
  (c.mixed = true ∧ h5ContextState c.before.1 ∈ leftContexts ∧
    h5ContextState c.before.2 = [3] ∧
    l = ([2],[1]) ∧
    c.branch ∈ ["M/notH5/H21/H17", "M/notH5/H21/notH17",
      "M/notH5/notH21/chain"])

private def noReflectShapeB (c : LowerGuardCase) (l : LowerLabel) : Bool :=
  (c.mixed == false) && (h5ContextState c.before.1 == [3]) &&
    ((h5ContextState c.before.2 == [1]) || (h5ContextState c.before.2 == [2])) &&
    (l == ([1],[]))

private def reflectShapeB (c : LowerGuardCase) (l : LowerLabel) : Bool :=
  ((c.mixed == false) && leftContexts.contains (h5ContextState c.before.1) &&
    (h5ContextState c.before.2 == [3,1]) &&
    ((l == ([1],[])) || ((l == ([2],[])) &&
      ["E/H3","E/H9/H16","E/H9/notH16","E/H9/left31"].contains c.branch))) ||
  ((c.mixed == true) && leftContexts.contains (h5ContextState c.before.1) &&
    (h5ContextState c.before.2 == [3]) &&
    (l == ([2],[1])) &&
    ["M/notH5/H21/H17", "M/notH5/H21/notH17",
      "M/notH5/notH21/chain"].contains c.branch)

private def ambiguousShapeB (c : LowerGuardCase) (l : LowerLabel) : Bool :=
  (c.mixed == false) && (h5ContextState c.before.1 == [3]) &&
    (h5ContextState c.before.2 == [3,1]) && (l == ([1],[]))

private def guardFinalOK (c : LowerGuardCase) (l : LowerLabel) : Bool :=
  if finalMixed c l then
    (!(lowerGuardSuffix (c.before.1 ++ l.1.reverse) [3,1] &&
        !(lowerGuardSuffix (c.before.2 ++ l.2) [3])) || noReflectShapeB c l || ambiguousShapeB c l) &&
    (!(lowerGuardSuffix (c.before.2 ++ l.2) [3,1] &&
        !(lowerGuardSuffix (c.before.1 ++ l.1.reverse) [3])) || reflectShapeB c l)
  else true

private def guardCatalogFinalOK : Bool :=
  lowerGuardCases.all fun c => c.labels.all fun l => guardFinalOK c l

private theorem guard_block_1 :
    lowerGuardCaseChunk1.all (fun c => c.labels.all fun l => guardFinalOK c l) = true := by decide
private theorem guard_block_2 :
    lowerGuardCaseChunk2.all (fun c => c.labels.all fun l => guardFinalOK c l) = true := by decide
private theorem guard_all : guardCatalogFinalOK = true := by
  simpa [guardCatalogFinalOK, lowerGuardCases, List.all_append] using
    And.intro guard_block_1 guard_block_2

private theorem guard_final (c : LowerGuardCase) (hc : c ∈ lowerGuardCases)
    (l : LowerLabel) (hl : l ∈ c.labels) : guardFinalOK c l = true := by
  have h1 := List.all_eq_true.mp guard_all c hc
  exact List.all_eq_true.mp h1 l hl


private theorem parity_same_add (a b u v : ℕ) (h : a % 2 = b % 2) :
    (u % 2 ≠ v % 2) ↔ (a+u) % 2 ≠ (b+v) % 2 := by
  rw [Nat.add_mod, Nat.add_mod, h]
  omega

private theorem parity_diff_add (a b u v : ℕ) (h : a % 2 ≠ b % 2) :
    (u % 2 = v % 2) ↔ (a+u) % 2 ≠ (b+v) % 2 := by
  rw [Nat.add_mod, Nat.add_mod]
  omega

private theorem normalize_mixed (p : LowerPair) : lowerMixed (lowerNormalize p) ↔ lowerMixed p := by
  unfold lowerNormalize
  split <;> simp only [lowerMixed, Prod.fst, Prod.snd, ne_eq]
  exact ne_comm

private theorem finalMixed_iff (p : LowerPair) (c : LowerGuardCase) (l : LowerLabel)
    (hf : lowerGuardFits c p) : finalMixed c l = true ↔ lowerMixed (lowerChild p l) := by
  rcases hf with ⟨_, hm, _⟩
  have hn := normalize_mixed p
  unfold lowerMixed at hn
  unfold lowerChild lowerMixed
  simp only [List.length_append, List.length_reverse]
  cases hc : c.mixed
  · have hp : ¬ lowerMixed p := by simpa [hc] using hm
    have hp' : ¬ (p.1.length % 2 ≠ p.2.length % 2) := by simpa [lowerMixed] using hp
    have hq : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
      exact not_ne_iff.mp (fun hne => hp' (hn.mp hne))
    simp only [finalMixed, hc, Bool.false_xor, decide_eq_true_eq]
    exact parity_same_add _ _ _ _ hq
  · have hp : lowerMixed p := by simpa [hc] using hm
    have hq : (lowerNormalize p).1.length % 2 ≠ (lowerNormalize p).2.length % 2 := hn.mpr hp
    simp only [finalMixed, hc, Bool.true_xor]
    constructor
    · intro he
      have hpv : l.1.length % 2 = l.2.length % 2 := by simpa using he
      exact (parity_diff_add _ _ _ _ hq).mp hpv
    · intro he
      have hpv := (parity_diff_add _ _ _ _ hq).mpr he
      simpa using hpv


private def ambiguousShape (c : LowerGuardCase) (l : LowerLabel) : Prop :=
  c.mixed = false ∧ h5ContextState c.before.1 = [3] ∧
    h5ContextState c.before.2 = [3,1] ∧ l = ([1],[])

private theorem guard_noReflect (p : LowerPair) (c : LowerGuardCase) (l : LowerLabel)
    (hc : c ∈ lowerGuardCases) (hf : lowerGuardFits c p) (hl : l ∈ c.labels)
    (hm : lowerMixed (lowerChild p l))
    (h31 : lowerEnds (lowerChild p l).1 [3,1])
    (hn3 : ¬ lowerEnds (lowerChild p l).2 [3]) :
    noReflectShape c l ∨ ambiguousShape c l := by
  have hb := guard_final c hc l hl
  have hfm : finalMixed c l = true := (finalMixed_iff p c l hf).mpr hm
  rw [guardFinalOK, hfm] at hb
  simp only [ite_true] at hb
  have hcxt := hf.1
  simp only [lowerChild, Prod.fst, Prod.snd] at h31 hn3
  have hb31 : lowerGuardSuffix (c.before.1 ++ l.1.reverse) [3,1] = true := by
    apply (guardSuffix_iff _ _).mpr
    simpa only [hcxt, Prod.fst] using
      (suffix31_append_state (lowerNormalize p).1 l.1.reverse).mp h31
  have hb3 : lowerGuardSuffix (c.before.2 ++ l.2) [3] = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    apply hn3
    apply (suffix3_append_state (lowerNormalize p).2 l.2).mpr
    simpa only [hcxt, Prod.snd] using (guardSuffix_iff _ _).mp he
  rw [hb31, hb3] at hb
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at hb
  have hbfull : (noReflectShapeB c l = true ∨ ambiguousShapeB c l = true) ∧
      ((!(lowerGuardSuffix (c.before.2 ++ l.2) [3,1] &&
        !lowerGuardSuffix (c.before.1 ++ l.1.reverse) [3]) || reflectShapeB c l) = true) := by
    simpa only [Bool.and_eq_true, Bool.or_eq_true] using hb
  rcases hbfull.1 with hs | hs
  · left
    simp only [noReflectShapeB, Bool.and_eq_true, beq_iff_eq,
      Bool.or_eq_true] at hs
    rcases hs with ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩
    exact ⟨h1,h2,(by simpa using h3),h4⟩
  · right
    simp only [ambiguousShapeB, Bool.and_eq_true, beq_iff_eq] at hs
    rcases hs with ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩
    exact ⟨h1,h2,(by simpa using h3),h4⟩

private theorem guard_reflect (p : LowerPair) (c : LowerGuardCase) (l : LowerLabel)
    (hc : c ∈ lowerGuardCases) (hf : lowerGuardFits c p) (hl : l ∈ c.labels)
    (hm : lowerMixed (lowerChild p l))
    (h31 : lowerEnds (lowerChild p l).2 [3,1])
    (hn3 : ¬ lowerEnds (lowerChild p l).1 [3]) :
    reflectShape c l := by
  have hb := guard_final c hc l hl
  have hfm : finalMixed c l = true := (finalMixed_iff p c l hf).mpr hm
  rw [guardFinalOK, hfm] at hb
  simp only [ite_true] at hb
  have hcxt := hf.1
  simp only [lowerChild, Prod.fst, Prod.snd] at h31 hn3
  have hb31 : lowerGuardSuffix (c.before.2 ++ l.2) [3,1] = true := by
    apply (guardSuffix_iff _ _).mpr
    simpa only [hcxt, Prod.snd] using
      (suffix31_append_state (lowerNormalize p).2 l.2).mp h31
  have hb3 : lowerGuardSuffix (c.before.1 ++ l.1.reverse) [3] = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    apply hn3
    apply (suffix3_append_state (lowerNormalize p).1 l.1.reverse).mpr
    simpa only [hcxt, Prod.fst] using (guardSuffix_iff _ _).mp he
  rw [hb31, hb3] at hb
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at hb
  have hbfull :
      ((!(lowerGuardSuffix (c.before.1 ++ l.1.reverse) [3,1] &&
        !lowerGuardSuffix (c.before.2 ++ l.2) [3]) || noReflectShapeB c l ||
        ambiguousShapeB c l) = true) ∧ reflectShapeB c l = true := by
    simpa only [Bool.and_eq_true] using hb
  simp only [reflectShapeB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hbfull
  rcases hbfull.2 with hs | hs
  · left
    rcases hs with ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩
    have h4' : l = ([1],[]) ∨ (l = ([2],[]) ∧
        c.branch ∈ ["E/H3","E/H9/H16","E/H9/notH16","E/H9/left31"]) := by
      rcases h4 with h | ⟨h,hb⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by simpa using hb⟩
    exact ⟨h1,(by simpa [leftContexts] using h2),h3,h4'⟩
  · right
    rcases hs with ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩
    exact ⟨h1,(by simpa [leftContexts] using h2),h3,h4,
      (by simpa using h5)⟩


private theorem suffix_singleton_getlast (w : List ℕ+) (a : ℕ+) :
    lowerEnds w [a] ↔ w.getLast? = some a := by
  constructor
  · rintro ⟨u,rfl⟩
    simp
  · intro h
    rw [List.getLast?_eq_some_iff] at h
    obtain ⟨u,rfl⟩ := h
    exact List.suffix_append _ _

private theorem guardState_getlast (w : List ℕ+) :
    (lowerGuardState w).getLast? = w.getLast? := by
  unfold lowerGuardState
  split_ifs with h1 h2 h3 h4
  · obtain ⟨u,rfl⟩ := (guardSuffix_iff _ _).mp h1
    simp
  · obtain ⟨u,rfl⟩ := (guardSuffix_iff _ _).mp h2
    simp
  · obtain ⟨u,rfl⟩ := (guardSuffix_iff _ _).mp h3
    simp
  · obtain ⟨u,rfl⟩ := (guardSuffix_iff _ _).mp h4
    simp
  · by_cases hw : w = []
    · subst w; simp
    · rw [List.drop_length_sub_one hw]
      simp [List.getLast?_eq_getLast, hw]

private theorem state_suffix_singleton (w : List ℕ+) (a : ℕ+) :
    lowerEnds (lowerGuardState w) [a] ↔ lowerEnds w [a] := by
  rw [suffix_singleton_getlast, suffix_singleton_getlast, guardState_getlast]

private theorem h5_state_main_singleton (s : List ℕ+) (a : ℕ+)
    (he : h5ContextState s = [a]) : lowerEnds s [a] := by
  unfold h5ContextState at he
  split at he
  · simp at he
  · have hd : s.drop (s.length - 1) <:+ s := List.drop_suffix _ _
    rw [he] at hd
    exact hd

private theorem h5_state_main31 (s : List ℕ+)
    (he : h5ContextState s = [3,1]) : lowerEnds s [3,1] := by
  unfold h5ContextState at he
  split at he
  · rename_i hz
    exact (guardSuffix_iff _ _).mp hz
  · have hh := congrArg List.length he
    simp at hh
    omega

private theorem not_ends_3_1 : ¬ lowerEnds ([1] : List ℕ+) [3] := by
  intro h; have z := h.getLast (by simp); norm_num at z
private theorem not_ends_31_1 : ¬ lowerEnds ([1] : List ℕ+) [3,1] := by
  intro h; have z := h.length_le; norm_num at z
private theorem not_ends_3_2 : ¬ lowerEnds ([2] : List ℕ+) [3] := by
  intro h; have z := h.getLast (by simp); norm_num at z
private theorem not_ends_31_2 : ¬ lowerEnds ([2] : List ℕ+) [3,1] := by
  intro h; have z := h.length_le; norm_num at z
private theorem not_ends_31_3 : ¬ lowerEnds ([3] : List ℕ+) [3,1] := by
  intro h; have z := h.length_le; norm_num at z
private theorem not_ends_3_31 : ¬ lowerEnds ([3,1] : List ℕ+) [3] := by
  intro h; have z := h.getLast (by simp); norm_num at z

private theorem h5_context_of_state (w ctx : List ℕ+)
    (hm : ctx ∈ leftContexts) (he : h5ContextState (lowerGuardState w) = ctx) :
    lowerHistorySuffixContext w ctx := by
  simp only [leftContexts, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h1 | h2 | h3c | h31c
  · rw [h1] at he ⊢
    have hm1 := (state_suffix_singleton w 1).mp (h5_state_main_singleton _ 1 he)
    refine ⟨hm1, ?_, ?_⟩
    · constructor
      · intro hs
        have a := hs.getLast (by simp)
        have b := hm1.getLast (by simp)
        have : (3 : ℕ+) = 1 := a.trans b.symm
        norm_num at this
      · intro hs
        exact ((not_ends_3_1 : ¬ lowerEnds [1] [3]) hs).elim
    · constructor
      · intro hs
        unfold h5ContextState at he
        rw [(guardSuffix_iff _ _).mpr ((state_suffix31 w).mpr hs)] at he
        simp at he
      · intro hs
        exact ((not_ends_31_1 : ¬ lowerEnds [1] [3,1]) hs).elim
  · rw [h2] at he ⊢
    have hm2 := (state_suffix_singleton w 2).mp (h5_state_main_singleton _ 2 he)
    refine ⟨hm2, ?_, ?_⟩
    · constructor
      · intro hs
        have a := hs.getLast (by simp)
        have b := hm2.getLast (by simp)
        have : (3 : ℕ+) = 2 := a.trans b.symm
        norm_num at this
      · intro hs
        exact ((not_ends_3_2 : ¬ lowerEnds [2] [3]) hs).elim
    · constructor
      · intro hs
        unfold h5ContextState at he
        rw [(guardSuffix_iff _ _).mpr ((state_suffix31 w).mpr hs)] at he
        simp at he
      · intro hs
        exact ((not_ends_31_2 : ¬ lowerEnds [2] [3,1]) hs).elim
  · rw [h3c] at he ⊢
    have hm3 := (state_suffix_singleton w 3).mp (h5_state_main_singleton _ 3 he)
    refine ⟨hm3, ?_, ?_⟩
    · constructor
      · intro _; simpa [lowerEnds]
      · intro _; exact hm3
    · constructor
      · intro hs
        unfold h5ContextState at he
        rw [(guardSuffix_iff _ _).mpr ((state_suffix31 w).mpr hs)] at he
        simp at he
      · intro hs
        exact ((not_ends_31_3 : ¬ lowerEnds [3] [3,1]) hs).elim
  · rw [h31c] at he ⊢
    have hm31 : lowerEnds w [3,1] :=
      (state_suffix31 w).mp (h5_state_main31 _ he)
    refine ⟨hm31, ?_, ?_⟩
    · constructor
      · intro hs
        have a := hs.getLast (by simp)
        have b := hm31.getLast (by simp)
        have : (3 : ℕ+) = 1 := a.trans b.symm
        norm_num at this
      · intro hs
        exact ((not_ends_3_31 : ¬ lowerEnds [3,1] [3]) hs).elim
    · constructor
      · intro _; simpa [lowerEnds]
      · intro _; exact hm31


private theorem contextFits_equal (p : LowerPair) (a b : List ℕ+) (z : Bool)
    (ha : lowerHistorySuffixContext (lowerNormalize p).1 a)
    (hb : lowerHistorySuffixContext (lowerNormalize p).2 b)
    (hm : ¬ lowerMixed p) :
    lowerHistoryContextFits (lowerNormalize p) ⟨(a,b),(z,z)⟩ := by
  refine ⟨ha,hb,?_⟩
  have hn := normalize_mixed p
  have heq : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
    apply not_ne_iff.mp
    intro hne
    exact hm (hn.mp hne)
  by_cases h1 : (lowerNormalize p).1.length % 2 = 1
  · have h2 : (lowerNormalize p).2.length % 2 = 1 := by omega
    simp [h1,h2]
  · have h2 : (lowerNormalize p).2.length % 2 ≠ 1 := by omega
    simp [h1,h2]

private theorem contextFits_mixed (p : LowerPair) (a b : List ℕ+)
    (ha : lowerHistorySuffixContext (lowerNormalize p).1 a)
    (hb : lowerHistorySuffixContext (lowerNormalize p).2 b)
    (hm : lowerMixed p) :
    lowerHistoryContextFits (lowerNormalize p) ⟨(a,b),(false,true)⟩ := by
  refine ⟨ha,hb,?_⟩
  have hn := (normalize_mixed p).mpr hm
  unfold lowerMixed at hn
  by_cases h1 : (lowerNormalize p).1.length % 2 = 1
  · have h2 : (lowerNormalize p).2.length % 2 ≠ 1 := by omega
    simp [h1,h2]
  · have h2 : (lowerNormalize p).2.length % 2 = 1 := by
      have b1 := Nat.mod_lt (lowerNormalize p).1.length (by omega : 0 < 2)
      have b2 := Nat.mod_lt (lowerNormalize p).2.length (by omega : 0 < 2)
      omega
    simp [h1,h2]


private theorem immediate_of_fields (h : ℕ → LowerPair) (m n : ℕ) (p : LowerPair)
    (l : LowerLabel) (c : LowerH5Case)
    (hmn : m+1=n) (hp : p = h m)
    (hfit : lowerHistoryContextFits (lowerNormalize p) c.context)
    (hstep : h n = lowerChild p l)
    (hw : c.words = (l.1.reverse,l.2))
    (hnorm : lowerNormalize (h n) = lowerHistoryOrient (h n) c.reflect)
    (hcuts : lowerHistoryAtBase (lowerNormalize p) c.oldCuts) :
    lowerH5Immediate h n c := by
  refine ⟨m,hmn,?_⟩
  subst p
  refine ⟨hfit,?_,hnorm,hcuts⟩
  rw [hstep, hw]
  rfl

private theorem cuts_transfer (base : LowerPair) (c : LowerH5Case) (k : LowerH5Kind)
    (he : c.oldCuts.toFinset = (lowerH5ExpectedCuts k).toFinset)
    (hc : lowerHistoryAtBase base (lowerH5ExpectedCuts k)) :
    lowerHistoryAtBase base c.oldCuts := by
  intro b hb
  apply hc b
  apply List.mem_toFinset.mp
  rw [← he]
  exact List.mem_toFinset.mpr hb


private theorem emit_case (h : ℕ → LowerPair) (m n : ℕ) (p : LowerPair)
    (l : LowerLabel) (k : LowerH5Kind) (x y : List ℕ+)
    (hk : (k,(x,y)) ∈ lowerH5ExpectedKeys)
    (hmn : m+1=n) (hp : p = h m)
    (hfit : lowerHistoryContextFits (lowerNormalize p)
      ⟨(x,y), lowerH5ExpectedParity k⟩)
    (hstep : h n = lowerChild p l)
    (hw : lowerH5ExpectedWords k = (l.1.reverse,l.2))
    (hnorm : lowerNormalize (h n) = lowerHistoryOrient (h n) (decide (k ≠ .a)))
    (hcuts : lowerHistoryAtBase (lowerNormalize p) (lowerH5ExpectedCuts k)) :
    ∃ c ∈ lowerH5Cases, lowerH5Immediate h n c := by
  obtain ⟨c,hcmem,hkind,hctx,hwords,href,hcutset⟩ :=
    M7H5CatalogPick14.catalog_pick k x y hk
  refine ⟨c,hcmem,immediate_of_fields h m n p l c hmn hp ?_ hstep ?_ ?_ ?_⟩
  · rw [hctx]
    exact hfit
  · rw [hwords, hw]
  · rw [href]
    exact hnorm
  · exact M7H5CatalogPick14.cuts_transfer _ _ _ hcutset hcuts


private theorem b2_kind_cuts (p : LowerPair) (b : String)
    (hb : b ∈ ["E/H3","E/H9/H16","E/H9/notH16","E/H9/left31"])
    (hbranch : lowerGuardBranch b p) :
    ∃ k ∈ [.b2h3,.b2h9h16,.b2h9not],
      lowerHistoryAtBase (lowerNormalize p) (lowerH5ExpectedCuts k) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · refine ⟨.b2h3, by simp, ?_⟩
    exact M7H5CoverageCuts14.a3_cut p (by simpa [lowerGuardBranch] using hbranch.2)
  · refine ⟨.b2h9h16, by simp, ?_⟩
    simp only [lowerGuardBranch] at hbranch
    have hh : ¬lowerA p 3 ∧ lowerA p 9 ∧ lowerA p 16 :=
      ⟨hbranch.1.2.1,hbranch.1.2.2,hbranch.2.2.2⟩
    exact M7H5CoverageCuts14.a9_a16_cuts p hh.1 hh.2.1 hh.2.2
  · refine ⟨.b2h9not, by simp, ?_⟩
    simp only [lowerGuardBranch] at hbranch
    have hh : ¬lowerA p 3 ∧ lowerA p 9 ∧ ¬lowerA p 16 :=
      ⟨hbranch.1.2.1,hbranch.1.2.2,hbranch.2.2.2⟩
    exact M7H5CoverageCuts14.a9_not_a16_cuts p hh.1 hh.2.1 hh.2.2
  · simp only [lowerGuardBranch] at hbranch
    have hh : ¬lowerA p 3 ∧ lowerA p 9 :=
      ⟨hbranch.1.2.1,hbranch.1.2.2⟩
    by_cases h16 : lowerA p 16
    · exact ⟨.b2h9h16, by simp,
        M7H5CoverageCuts14.a9_a16_cuts p hh.1 hh.2 h16⟩
    · exact ⟨.b2h9not, by simp,
        M7H5CoverageCuts14.a9_not_a16_cuts p hh.1 hh.2 h16⟩

private theorem c_cuts (p : LowerPair) (b : String)
    (hb : b ∈ ["M/notH5/H21/H17", "M/notH5/H21/notH17",
      "M/notH5/notH21/chain"])
    (hbranch : lowerGuardBranch b p) :
    lowerHistoryAtBase (lowerNormalize p) (lowerH5ExpectedCuts .cLarge) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;>
    simp only [lowerGuardBranch] at hbranch
  all_goals exact M7H5CoverageCuts14.not_h2_not_h5_cuts p hbranch.1.2.1 hbranch.1.2.2


private theorem append_replicate_ends3 (w : List ℕ+) (k : ℕ) (hk : 0 < k) :
    lowerEnds (w ++ List.replicate k 3) [3] := by
  apply (suffix_singleton_getlast _ _).mpr
  simp [List.getLast?_append, List.getLast?_replicate, hk.ne']

private theorem run_not_active (p : LowerPair) (k : ℕ) (hk : 3 ≤ k) :
    ¬ lowerH5Active (lowerChild p (List.replicate k 3,List.replicate k 3)) := by
  intro ha
  have h1 : lowerEnds (lowerChild p (List.replicate k 3,List.replicate k 3)).1 [3] := by
    simp only [lowerChild, Prod.fst, List.reverse_replicate]
    exact append_replicate_ends3 _ _ (by omega)
  have h2 : lowerEnds (lowerChild p (List.replicate k 3,List.replicate k 3)).2 [3] := by
    simp only [lowerChild, Prod.snd]
    exact append_replicate_ends3 _ _ (by omega)
  have hn3 : lowerEnds (lowerNormalize
      (lowerChild p (List.replicate k 3,List.replicate k 3))).1 [3] := by
    unfold lowerNormalize
    split <;> simp_all
  have hn31 := ha.2.2.2
  unfold lowerL at hn31
  have a := hn3.getLast (by simp)
  have b := hn31.getLast (by simp)
  have : (3 : ℕ+) = 1 := a.trans b.symm
  norm_num at this


private theorem a_key (y : List ℕ+) (hy : y ∈ [[1],[2]]) :
    (.a,([3],y)) ∈ lowerH5ExpectedKeys := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [lowerH5ExpectedKeys]

private theorem b_key (k : LowerH5Kind) (x : List ℕ+)
    (hk : k ∈ [.b1,.b2h3,.b2h9h16,.b2h9not]) (hx : x ∈ leftContexts) :
    (k,(x,[3,1])) ∈ lowerH5ExpectedKeys := by
  simp [leftContexts, lowerH5ExpectedKeys] at hk hx ⊢
  aesop

private theorem c_key (x : List ℕ+) (hx : x ∈ leftContexts) :
    (.cLarge,(x,[3])) ∈ lowerH5ExpectedKeys := by
  simp [leftContexts, lowerH5ExpectedKeys] at hx ⊢
  aesop

private theorem small_left (x : List ℕ+) (hx : x ∈ [[1],[2]]) : x ∈ leftContexts := by
  simp [leftContexts] at hx ⊢
  aesop

private theorem b2_words (k : LowerH5Kind)
    (hk : k ∈ [.b2h3,.b2h9h16,.b2h9not]) :
    lowerH5ExpectedWords k = ([2],[]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> rfl

private theorem b2_parity (k : LowerH5Kind)
    (hk : k ∈ [.b2h3,.b2h9h16,.b2h9not]) :
    lowerH5ExpectedParity k = (false,false) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> rfl

private theorem b2_not_a (k : LowerH5Kind)
    (hk : k ∈ [.b2h3,.b2h9h16,.b2h9not]) : k ≠ .a := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> simp

private theorem coverage_core (hc : lowerH5CatalogValid)
    (hg : ∀ (p : LowerPair), lowerAdmissible p → ∀ l, lowerOffered p l → lowerGuardAllowed p l)
    (hi : ∀ (t : ℝ) (p : LowerPair), lowerInitialRoot t p → ¬(lowerMixed p ∧ lowerL p))
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (hr : ¬lowerEnds (lowerNormalize (h n)).2 [3]) :
    ∃ c ∈ lowerH5Cases, lowerH5Immediate h n c := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    exact (hi t (h 0) hh.1) ⟨ha.1,ha.2.2.2⟩
  obtain ⟨m,hmn⟩ : ∃ m, m+1=n := by
    exact ⟨n-1, by omega⟩
  have hmle : m ≤ n := by omega
  have hmlt : m < n := by omega
  have hs := hh.2.1 m hmle
  obtain ⟨l,hoff,_hpriority,hstep⟩ := hh.2.2 m hmlt
  have hallowed := hg (h m) hs.1 l hoff
  have hstepn : h n = lowerChild (h m) l := by
    rw [← hmn]
    exact hstep
  have ha' : lowerH5Active (lowerChild (h m) l) := by simpa [hstepn] using ha
  rcases hallowed with ⟨c,hcmem,hgfit,hlmem⟩ | ⟨_hrun,k,hk,rfl⟩
  · let child := lowerChild (h m) l
    by_cases hwid : lowerWidth child.2 ≤ lowerWidth child.1
    · have hnorm : lowerNormalize child = child := by
        simp [lowerNormalize, hwid]
      have hleft31 : lowerEnds child.1 [3,1] := by
        have hh := ha'.2.2.2
        unfold lowerL at hh
        simpa [child, hnorm] using hh
      have hright3 : ¬ lowerEnds child.2 [3] := by
        simpa [hstepn, child, hnorm] using hr
      rcases guard_noReflect (h m) c l hcmem hgfit hlmem ha'.1 hleft31 hright3 with
        hshape | hamb
      · rcases hshape with ⟨hcf,hx,hy,hl⟩
        have hnotmixed : ¬ lowerMixed (h m) := by
          intro hmixed
          have := hgfit.2.1.mpr hmixed
          simp [hcf] at this
        let y := h5ContextState c.before.2
        have hy' : y ∈ [[1],[2]] := hy
        have hcx : lowerHistorySuffixContext (lowerNormalize (h m)).1 [3] :=
          h5_context_of_state _ [3] (by simp [leftContexts]) (by
            simpa only [y, hgfit.1, Prod.fst] using hx)
        have hcy : lowerHistorySuffixContext (lowerNormalize (h m)).2 y :=
          h5_context_of_state _ y (small_left y hy') (by
            simp only [y, hgfit.1, Prod.snd])
        have hfit := contextFits_equal (h m) [3] y true hcx hcy hnotmixed
        have hnormal : lowerNormalize (h n) = lowerHistoryOrient (h n) false := by
          rw [hstepn]
          simpa [child, lowerHistoryOrient] using hnorm
        apply emit_case h m n (h m) l .a [3] y
        · exact a_key y hy'
        · exact hmn
        · rfl
        · simpa [lowerH5ExpectedParity] using hfit
        · exact hstepn
        · subst l; rfl
        · simpa using hnormal
        · intro b hb
          simp [lowerH5ExpectedCuts] at hb
      · rcases hamb with ⟨_,hx,hy,hl⟩
        subst l
        have hcx := h5_context_of_state (lowerNormalize (h m)).1 [3]
          (by simp [leftContexts]) (by simpa only [hgfit.1, Prod.fst] using hx)
        have hcy := h5_context_of_state (lowerNormalize (h m)).2 [3,1]
          (by simp [leftContexts]) (by simpa only [hgfit.1, Prod.snd] using hy)
        exact (M7H5Nonreflect14.h5_one_nonreflect_impossible (h m) hs
          hcx.1 hcy.1 hnorm ha').elim
    · have hnorm : lowerNormalize child = (child.2,child.1) := by
        simp [lowerNormalize, hwid]
      have hright31 : lowerEnds child.2 [3,1] := by
        have hh := ha'.2.2.2
        unfold lowerL at hh
        simpa [child, hnorm] using hh
      have hleft3 : ¬ lowerEnds child.1 [3] := by
        simpa [hstepn, child, hnorm] using hr
      rcases guard_reflect (h m) c l hcmem hgfit hlmem ha'.1 hright31 hleft3 with
        heq | hmix
      · rcases heq with ⟨hcf,hx,hy,hl⟩
        have hnotmixed : ¬ lowerMixed (h m) := by
          intro hmixed
          have := hgfit.2.1.mpr hmixed
          simp [hcf] at this
        let x := h5ContextState c.before.1
        have hx' : x ∈ leftContexts := hx
        have hcx := h5_context_of_state (lowerNormalize (h m)).1 x hx' (by
          simp only [x, hgfit.1, Prod.fst])
        have hcy := h5_context_of_state (lowerNormalize (h m)).2 [3,1]
          (by simp [leftContexts]) (by simpa only [hgfit.1, Prod.snd] using hy)
        rcases hl with hl | ⟨hl,hbranch⟩
        · have hfit := contextFits_equal (h m) x [3,1] false hcx hcy hnotmixed
          have hnormal : lowerNormalize (h n) = lowerHistoryOrient (h n) true := by
            rw [hstepn]
            simpa [child, lowerHistoryOrient] using hnorm
          apply emit_case h m n (h m) l .b1 x [3,1]
          · exact b_key .b1 x (by simp) hx'
          · exact hmn
          · rfl
          · simpa [lowerH5ExpectedParity] using hfit
          · exact hstepn
          · subst l; rfl
          · simpa using hnormal
          · intro b hb
            simp [lowerH5ExpectedCuts] at hb
        · subst l
          obtain ⟨kind,hkind,hcuts⟩ := b2_kind_cuts (h m) c.branch hbranch hgfit.2.2
          have hfit := contextFits_equal (h m) x [3,1] false hcx hcy hnotmixed
          have hkna : kind ≠ .a := b2_not_a kind hkind
          have hnormal : lowerNormalize (h n) =
              lowerHistoryOrient (h n) (decide (kind ≠ .a)) := by
            rw [hstepn]
            simp [hkna, child, lowerHistoryOrient]
            exact hnorm
          apply emit_case h m n (h m) ([2],[]) kind x [3,1]
          · apply b_key kind x _ hx'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hkind ⊢
            exact Or.inr hkind
          · exact hmn
          · rfl
          · rw [b2_parity kind hkind]
            exact hfit
          · exact hstepn
          · exact b2_words kind hkind
          · exact hnormal
          · exact hcuts
      · rcases hmix with ⟨hct,hx,hy,hl,hbranch⟩
        have hmixed : lowerMixed (h m) := hgfit.2.1.mp (by simpa using hct)
        let x := h5ContextState c.before.1
        have hx' : x ∈ leftContexts := hx
        have hcx := h5_context_of_state (lowerNormalize (h m)).1 x hx' (by
          simp only [x, hgfit.1, Prod.fst])
        have hcy := h5_context_of_state (lowerNormalize (h m)).2 [3]
          (by simp [leftContexts]) (by simpa only [hgfit.1, Prod.snd] using hy)
        have hfit := contextFits_mixed (h m) x [3] hcx hcy hmixed
        have hcuts := c_cuts (h m) c.branch hbranch hgfit.2.2
        have hnormal : lowerNormalize (h n) = lowerHistoryOrient (h n) true := by
          rw [hstepn]
          simpa [child, lowerHistoryOrient] using hnorm
        apply emit_case h m n (h m) l .cLarge x [3]
        · exact c_key x hx'
        · exact hmn
        · rfl
        · simpa [lowerH5ExpectedParity] using hfit
        · exact hstepn
        · subst l; rfl
        · simpa using hnormal
        · exact hcuts
  · exact (run_not_active (h m) k hk ha').elim


theorem solution (hc : lowerH5CatalogValid)
    (hg : ∀ (p : LowerPair), lowerAdmissible p → ∀ l, lowerOffered p l → lowerGuardAllowed p l)
    (hi : ∀ (t : ℝ) (p : LowerPair), lowerInitialRoot t p → ¬(lowerMixed p ∧ lowerL p))
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (hr : ¬lowerEnds (lowerNormalize (h n)).2 [3]) :
    ∃ c ∈ lowerH5Cases, lowerH5Immediate h n c := by
  exact coverage_core hc hg hi t h n hh ha hr

#print axioms solution
