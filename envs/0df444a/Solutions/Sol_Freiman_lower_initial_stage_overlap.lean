-- Prove2me | solution 1 for Freiman.lower_initial_stage_overlap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-12T22:01:22.280799+00:00
-- url     : https://prove2.me/submissions/b9cbb1a3-76a6-42c2-96c6-d0f3dc87822b

import Definitions.Def_Freiman_lowerInitialStage
import Mathlib.Tactic
import Theorems.Thm_Freiman_lower_entry_context_auxB
import Theorems.Thm_Freiman_lower_entry_family_domain
import Theorems.Thm_Freiman_lower_initial_family_normalization
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_prefixEval_mobius

namespace M7StageOverlap

open Freiman

set_option maxHeartbeats 2000000

private lemma sp_pe_append : ∀ (u v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x)
  | [], v, x => rfl
  | a :: u, v, x => by simp only [List.cons_append, prefixEval, sp_pe_append u v x]

private lemma sp_tau_pos : 0 < lowerTau := by
  unfold lowerTau
  have h : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

private lemma sp_tail_bounds :
    let a := prefixEval [3,1,3,3,2,1,3] lowerTau
    let t := prefixEval [3] lowerTau
    let b := prefixEval [3,3,3,1,2,1,3] lowerTau
    (0:ℝ) < a ∧ a < 265441/1000000 ∧
    267949/1000000 < t ∧ t < 267950/1000000 ∧
    302477/1000000 < b ∧ b < 302478/1000000 := by
  dsimp
  have hs0 := Real.sqrt_nonneg 3
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hlo : (1732050/1000000:ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 3 < (1732051/1000000:ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have htau : 0 ≤ lowerTau := by unfold lowerTau; nlinarith
  repeat' apply And.intro
  all_goals
    rw [prefixEval_mobius _ _ htau]
    norm_num [wordContinuantP, wordContinuantPrevP, wordContinuantQ,
      wordContinuantPrevQ, wordContinuantData, lowerTau]
    try simp only [inv_eq_one_div]
  · positivity
  all_goals
    first
    | rw [div_lt_iff₀ (by positivity)]; nlinarith
    | rw [lt_div_iff₀ (by positivity)]; nlinarith

private theorem stage_point_box
    (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t →
      prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
      0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
      (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
      (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length)
    (hcd : ∀ w : List ℕ+, (lowerInitialWordMatrix w).c = ((lowerCD w).1:ℝ) ∧
      (lowerInitialWordMatrix w).d = ((lowerCD w).2:ℝ))
    (L R : List ℕ+)
    (hdetL : (lowerInitialWordMatrix L).a*(lowerInitialWordMatrix L).d -
      (lowerInitialWordMatrix L).b*(lowerInitialWordMatrix L).c = 1)
    (hdetR : (lowerInitialWordMatrix R).a*(lowerInitialWordMatrix R).d -
      (lowerInitialWordMatrix R).b*(lowerInitialWordMatrix R).c = 1)
    (DLpos : (0:ℝ) < ((lowerCD L).2:ℝ)) (DRpos : (0:ℝ) < ((lowerCD R).2:ℝ))
    (CLlo : (2/3:ℝ) * ((lowerCD L).2:ℝ) < ((lowerCD L).1:ℝ))
    (CLhi : ((lowerCD L).1:ℝ) < (3/4:ℝ) * ((lowerCD L).2:ℝ))
    (CRlo : (2/3:ℝ) * ((lowerCD R).2:ℝ) < ((lowerCD R).1:ℝ))
    (CRhi : ((lowerCD R).1:ℝ) < (3/4:ℝ) * ((lowerCD R).2:ℝ))
    (hq : (200:ℝ) * ((lowerCD L).2:ℝ)^2 < 13 * ((lowerCD R).2:ℝ)^2) :
    prefixEval (L++[3,1,3,3,2,1,3]) lowerTau +
        prefixEval (R++[3,3,3,1,2,1,3]) lowerTau <
      prefixEval (L++[3]) lowerTau + prefixEval (R++[3]) lowerTau := by
  let a := prefixEval [3,1,3,3,2,1,3] lowerTau
  let t := prefixEval [3] lowerTau
  let b := prefixEval [3,3,3,1,2,1,3] lowerTau
  obtain ⟨ha0, ha1, ht0, ht1, hb0, hb1⟩ := sp_tail_bounds
  change 0 < a at ha0
  change a < _ at ha1
  change _ < t at ht0
  change t < _ at ht1
  change _ < b at hb0
  change b < _ at hb1
  have htpos : 0 < t := by linarith
  have hbpos : 0 < b := by linarith
  let ML := lowerInitialWordMatrix L
  let MR := lowerInitialWordMatrix R
  have fLa := (hfrac L a ha0)
  have fLt := (hfrac L t htpos)
  have fRb := (hfrac R b hbpos)
  have fRt := (hfrac R t htpos)
  have cdL := hcd L
  have cdR := hcd R
  have detL : ML.a * ML.d - ML.b * ML.c = 1 := by simpa [ML] using hdetL
  have detR : MR.a * MR.d - MR.b * MR.c = 1 := by simpa [MR] using hdetR
  have dLa : 0 < ML.c*a + ML.d := by simpa [ML, lowerInitialMatDen] using fLa.2.1
  have dLt : 0 < ML.c*t + ML.d := by simpa [ML, lowerInitialMatDen] using fLt.2.1
  have dRb : 0 < MR.c*b + MR.d := by simpa [MR, lowerInitialMatDen] using fRb.2.1
  have dRt : 0 < MR.c*t + MR.d := by simpa [MR, lowerInitialMatDen] using fRt.2.1
  have Lda : ML.c*a + ML.d < (6/5:ℝ) * ((lowerCD L).2:ℝ) := by
    rw [cdL.1, cdL.2]
    have Cp : (0:ℝ) < ((lowerCD L).1:ℝ) := by nlinarith [CLlo, DLpos]
    have h1 := mul_lt_mul_of_pos_right CLhi ha0
    have h2 := mul_lt_mul_of_pos_left ha1 (by positivity : (0:ℝ) < (3/4:ℝ)*((lowerCD L).2:ℝ))
    nlinarith only [h1, h2, DLpos]
  have Ldt : ML.c*t + ML.d < (121/100:ℝ) * ((lowerCD L).2:ℝ) := by
    rw [cdL.1, cdL.2]
    have Cp : (0:ℝ) < ((lowerCD L).1:ℝ) := by nlinarith [CLlo, DLpos]
    have h1 := mul_lt_mul_of_pos_right CLhi htpos
    have h2 := mul_lt_mul_of_pos_left ht1 (by positivity : (0:ℝ) < (3/4:ℝ)*((lowerCD L).2:ℝ))
    nlinarith only [h1, h2, DLpos]
  have Rdb : (6/5:ℝ) * ((lowerCD R).2:ℝ) < MR.c*b + MR.d := by
    rw [cdR.1, cdR.2]
    have h1 := mul_lt_mul_of_pos_right CRlo hbpos
    have h2 := mul_lt_mul_of_pos_left hb0 (by positivity : (0:ℝ) < (2/3:ℝ)*((lowerCD R).2:ℝ))
    nlinarith only [h1, h2, DRpos]
  have Rdt : (117/100:ℝ) * ((lowerCD R).2:ℝ) < MR.c*t + MR.d := by
    rw [cdR.1, cdR.2]
    have h1 := mul_lt_mul_of_pos_right CRlo htpos
    have h2 := mul_lt_mul_of_pos_left ht0 (by positivity : (0:ℝ) < (2/3:ℝ)*((lowerCD R).2:ℝ))
    nlinarith only [h1, h2, DRpos]
  have hden : (b-t) * ((ML.c*a+ML.d)*(ML.c*t+ML.d)) <
      (t-a) * ((MR.c*b+MR.d)*(MR.c*t+MR.d)) := by
    have hLL : (ML.c*a+ML.d)*(ML.c*t+ML.d) <
        (363/250:ℝ) * ((lowerCD L).2:ℝ)^2 := by
      calc
        _ < (6/5:ℝ)*((lowerCD L).2:ℝ) * (ML.c*t+ML.d) := mul_lt_mul_of_pos_right Lda dLt
        _ < (6/5:ℝ)*((lowerCD L).2:ℝ) * ((121/100:ℝ)*((lowerCD L).2:ℝ)) :=
          mul_lt_mul_of_pos_left Ldt (by positivity)
        _ = _ := by ring
    have hRR : (351/250:ℝ) * ((lowerCD R).2:ℝ)^2 <
        (MR.c*b+MR.d)*(MR.c*t+MR.d) := by
      calc
        _ = (6/5:ℝ)*((lowerCD R).2:ℝ) * ((117/100:ℝ)*((lowerCD R).2:ℝ)) := by ring
        _ < (MR.c*b+MR.d) * ((117/100:ℝ)*((lowerCD R).2:ℝ)) :=
          mul_lt_mul_of_pos_right Rdb (by positivity)
        _ < (MR.c*b+MR.d) * (MR.c*t+MR.d) := by exact mul_lt_mul_of_pos_left Rdt (by positivity)
    have hbt : b-t < (34529/1000000:ℝ) := by linarith
    have hta : (2508/1000000:ℝ) < t-a := by linarith
    have hLsq : 0 < ((lowerCD L).2:ℝ)^2 := sq_pos_of_pos DLpos
    have hRsq : 0 < ((lowerCD R).2:ℝ)^2 := sq_pos_of_pos DRpos
    have hleft : (b-t) * ((ML.c*a+ML.d)*(ML.c*t+ML.d)) <
        (34529/1000000:ℝ) * ((363/250:ℝ) * ((lowerCD L).2:ℝ)^2) := by
      have hbt0 : 0 < b-t := by linarith [hb0, ht1]
      calc
        _ < (34529/1000000:ℝ) * ((ML.c*a+ML.d)*(ML.c*t+ML.d)) :=
          mul_lt_mul_of_pos_right hbt (mul_pos dLa dLt)
        _ < _ := mul_lt_mul_of_pos_left hLL (by norm_num)
    have hmid : (34529/1000000:ℝ) * ((363/250:ℝ) * ((lowerCD L).2:ℝ)^2) <
        (2508/1000000:ℝ) * ((351/250:ℝ) * ((lowerCD R).2:ℝ)^2) := by
      nlinarith only [hq, hRsq]
    have hright : (2508/1000000:ℝ) * ((351/250:ℝ) * ((lowerCD R).2:ℝ)^2) <
        (t-a) * ((MR.c*b+MR.d)*(MR.c*t+MR.d)) := by
      have hta0 : 0 < t-a := by linarith [hta]
      calc
        _ < (t-a) * ((351/250:ℝ)*((lowerCD R).2:ℝ)^2) :=
          mul_lt_mul_of_pos_right hta (by positivity)
        _ < _ := mul_lt_mul_of_pos_left hRR hta0
    exact lt_trans hleft (lt_trans hmid hright)
  rw [sp_pe_append, sp_pe_append, sp_pe_append, sp_pe_append]
  change prefixEval L a + prefixEval R b < prefixEval L t + prefixEval R t
  rw [fLa.1, fLt.1, fRb.1, fRt.1]
  unfold lowerInitialMatEval
  change (ML.a*a+ML.b)/(ML.c*a+ML.d) + (MR.a*b+MR.b)/(MR.c*b+MR.d) <
    (ML.a*t+ML.b)/(ML.c*t+ML.d) + (MR.a*t+MR.b)/(MR.c*t+MR.d)
  have hdL : (ML.a*t+ML.b)/(ML.c*t+ML.d) - (ML.a*a+ML.b)/(ML.c*a+ML.d) =
      (t-a)/((ML.c*t+ML.d)*(ML.c*a+ML.d)) := by
    rw [div_sub_div _ _ (ne_of_gt dLt) (ne_of_gt dLa)]
    rw [show (ML.a*t+ML.b)*(ML.c*a+ML.d) - (ML.c*t+ML.d)*(ML.a*a+ML.b) = t-a by
      calc
        _ = (t-a) * (ML.a*ML.d-ML.b*ML.c) := by ring
        _ = t-a := by rw [detL]; ring]
  have hdR : (MR.a*b+MR.b)/(MR.c*b+MR.d) - (MR.a*t+MR.b)/(MR.c*t+MR.d) =
      (b-t)/((MR.c*b+MR.d)*(MR.c*t+MR.d)) := by
    rw [div_sub_div _ _ (ne_of_gt dRb) (ne_of_gt dRt)]
    rw [show (MR.a*b+MR.b)*(MR.c*t+MR.d) - (MR.c*b+MR.d)*(MR.a*t+MR.b) = b-t by
      calc
        _ = (b-t) * (MR.a*MR.d-MR.b*MR.c) := by ring
        _ = b-t := by rw [detR]; ring]
  have hquot : (b-t)/((MR.c*b+MR.d)*(MR.c*t+MR.d)) <
      (t-a)/((ML.c*t+ML.d)*(ML.c*a+ML.d)) := by
    rw [div_lt_div_iff₀ (mul_pos dRb dRt) (mul_pos dLt dLa)]
    nlinarith only [hden]
  nlinarith only [hdL, hdR, hquot]

open Freiman
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

private theorem spp_repeat_succ (n : ℕ) :
    lowerRepeat lowerPeriod (n+1) = lowerRepeat lowerPeriod n ++ lowerPeriod := by
  simp [lowerRepeat, List.replicate_add, List.flatten_append]

private theorem spp_cd_period (w : List ℕ+) :
    lowerCD (w ++ lowerPeriod) =
      (14*(lowerCD w).1 + 53*(lowerCD w).2,
       19*(lowerCD w).1 + 72*(lowerCD w).2) := by
  simp [lowerCD, lowerPeriod, List.foldl_append]
  omega

private theorem spp_D_pos (w : List ℕ+) : 0 < ((lowerCD w).2:ℝ) := by
  have hn : 0 < (lowerCD w).2 := by
    induction w using List.reverseRecOn with
    | nil => norm_num [lowerCD]
    | append_singleton w a ih =>
      have hc : lowerCD (w ++ [a]) =
          ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
        simp [lowerCD, List.foldl_append]
      rw [hc]
      dsimp only
      positivity
  exact_mod_cast hn

private theorem spp_period_ratio (w : List ℕ+) :
    (2/3:ℝ) < lowerRatio (w ++ lowerPeriod) ∧
      lowerRatio (w ++ lowerPeriod) < (3/4:ℝ) := by
  have hd := spp_D_pos w
  have hc : (0:ℝ) ≤ ((lowerCD w).1:ℝ) := by positivity
  rw [lowerRatio,spp_cd_period]
  dsimp only [Prod.fst,Prod.snd]
  push_cast
  have hden : (0:ℝ) < 19*((lowerCD w).1:ℝ)+72*((lowerCD w).2:ℝ) := by positivity
  constructor
  · rw [lt_div_iff₀ hden]; nlinarith
  · rw [div_lt_iff₀ hden]; nlinarith

private theorem spp_cd3 (w : List ℕ+) :
    lowerCD (w ++ [3]) = ((lowerCD w).2,(lowerCD w).1+3*(lowerCD w).2) := by
  simp [lowerCD,List.foldl_append]

private theorem spp_cd313 (w : List ℕ+) :
    lowerCD (w ++ [3,1,3]) = ((lowerCD w).1+4*(lowerCD w).2,
      4*(lowerCD w).1+15*(lowerCD w).2) := by
  simp [lowerCD,List.foldl_append]
  omega

private theorem stage_point_parameters (n : ℕ) :
    let L := [3,2,1,1] ++ lowerRepeat lowerPeriod (n+1)
    let R := [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1)
    L.length % 2 = 0 ∧ R.length % 2 = 0 ∧
    (2/3:ℝ) < lowerRatio L ∧ lowerRatio L < (3/4:ℝ) ∧
    (2/3:ℝ) < lowerRatio R ∧ lowerRatio R < (3/4:ℝ) ∧
    (200:ℝ) * ((lowerCD L).2:ℝ)^2 < 13 * ((lowerCD R).2:ℝ)^2 := by
  let L := [3,2,1,1] ++ lowerRepeat lowerPeriod (n+1)
  let R := [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1)
  change L.length % 2 = 0 ∧ R.length % 2 = 0 ∧ _
  have hl : (2/3:ℝ) < lowerRatio L ∧ lowerRatio L < (3/4:ℝ) := by
    have heq : L = (([3,2,1,1] ++ lowerRepeat lowerPeriod n) ++ lowerPeriod) := by
      dsimp only [L]
      rw [spp_repeat_succ]
      exact (List.append_assoc _ _ _).symm
    rw [heq]
    exact spp_period_ratio _
  have hr : (2/3:ℝ) < lowerRatio R ∧ lowerRatio R < (3/4:ℝ) := by
    have heq : R = (([4,3,2,2] ++ lowerRepeat lowerPeriod n) ++ lowerPeriod) := by
      dsimp only [R]
      rw [spp_repeat_succ]
      exact (List.append_assoc _ _ _).symm
    rw [heq]
    exact spp_period_ratio _
  refine ⟨?_,?_,hl.1,hl.2,hr.1,hr.2,?_⟩
  · simp [L,lowerRepeat,lowerPeriod,List.length_flatten] <;> omega
  · simp [R,lowerRepeat,lowerPeriod,List.length_flatten] <;> omega
  · have hdom := (lower_entry_family_domain .A (n+1) 0 0).1
    have hn : lowerNormalize (lowerFamilyPair .A (n+1) 0 0) =
        (R++[3],L++[3,1,3]) := by
      rw [lower_initial_family_normalization .A (n+1) 0 0 (by decide)]
      simp [lowerFamilyPair,L,R,List.append_assoc]
    rw [hn] at hdom
    have hDL := spp_D_pos L
    have hDR := spp_D_pos R
    have hCL : (0:ℝ) ≤ ((lowerCD L).1:ℝ) := by positivity
    have hCR : (0:ℝ) ≤ ((lowerCD R).1:ℝ) := by positivity
    rw [lowerScale,spp_cd3,spp_cd313] at hdom
    dsimp only [Prod.fst,Prod.snd] at hdom
    push_cast at hdom
    rw [lt_div_iff₀ (by positivity)] at hdom
    have hLlo := hl.1
    have hRhi := hr.2
    rw [lowerRatio,lt_div_iff₀ hDL] at hLlo
    rw [lowerRatio,div_lt_iff₀ hDR] at hRhi
    have hL : (53/3:ℝ) * ((lowerCD L).2:ℝ) <
        4*((lowerCD L).1:ℝ)+15*((lowerCD L).2:ℝ) := by linarith
    have hR : ((lowerCD R).1:ℝ)+3*((lowerCD R).2:ℝ) <
        (15/4:ℝ)*((lowerCD R).2:ℝ) := by linarith
    have hLsq : (2809/9:ℝ)*((lowerCD L).2:ℝ)^2 <
        (4*((lowerCD L).1:ℝ)+15*((lowerCD L).2:ℝ))^2 := by
      nlinarith [mul_pos (sub_pos.mpr hL) (by positivity : (0:ℝ) <
        4*((lowerCD L).1:ℝ)+15*((lowerCD L).2:ℝ)+(53/3:ℝ)*((lowerCD L).2:ℝ))]
    have hRsq : (((lowerCD R).1:ℝ)+3*((lowerCD R).2:ℝ))^2 <
        (225/16:ℝ)*((lowerCD R).2:ℝ)^2 := by
      nlinarith [mul_pos (sub_pos.mpr hR) (by positivity : (0:ℝ) <
        ((lowerCD R).1:ℝ)+3*((lowerCD R).2:ℝ)+(15/4:ℝ)*((lowerCD R).2:ℝ))]
    nlinarith [sq_pos_of_pos hDR]

open Freiman
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

private theorem stage_repeat_succ (n : ℕ) :
    lowerRepeat lowerPeriod (n+1) = lowerRepeat lowerPeriod n ++ lowerPeriod := by
  simp [lowerRepeat, List.replicate_add, List.flatten_append]

private theorem stage_aux_normalize (n : ℕ) :
    lowerNormalize (lowerFamilyPair .auxB n 0 0) = lowerFamilyPair .auxB n 0 0 := by
  obtain ⟨c,hc,_⟩ := lower_entry_context_auxB n 0 0
  have hr : lowerEnds (lowerNormalize (lowerFamilyPair .auxB n 0 0)).2 [3] := hc.2.2.1
  by_cases hw : lowerWidth (lowerFamilyPair .auxB n 0 0).2 ≤
      lowerWidth (lowerFamilyPair .auxB n 0 0).1
  · simp [lowerNormalize, hw]
  · simp only [lowerNormalize, if_neg hw, Prod.snd] at hr
    simp [lowerFamilyPair, lowerEnds, ← List.reverse_prefix] at hr

private theorem stage_Icc_inter (a b c d : ℝ) (hbc : b ≤ d) (hca : c ≤ a) :
    (Set.Icc (min a b) (max a b) ∩ Set.Icc (min c d) (max c d)).Nonempty := by
  refine ⟨max (min a b) (min c d), ?_⟩
  constructor
  · exact ⟨le_max_left _ _, max_le
      (le_trans (min_le_left _ _) (le_max_left _ _))
      ((min_le_left _ _).trans (hca.trans (le_max_left _ _)))⟩
  · exact ⟨le_max_right _ _, max_le
      ((min_le_right _ _).trans (hbc.trans (le_max_right _ _)))
      ((min_le_right _ _).trans (le_max_right _ _))⟩

private theorem stage_overlap_from_point
    (hpoint : ∀ n : ℕ,
      let L := [3,2,1,1] ++ lowerRepeat lowerPeriod (n+1)
      let R := [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1)
      prefixEval (L ++ [3,1,3,3,2,1,3]) lowerTau +
        prefixEval (R ++ [3,3,3,1,2,1,3]) lowerTau <
      prefixEval (L ++ [3]) lowerTau + prefixEval (R ++ [3]) lowerTau)
    (hseams : lowerInitialSeams) (n : ℕ) :
    (lowerInitialStage n ∩ lowerInitialStage (n+1)).Nonempty := by
  let L := [3,2,1,1] ++ lowerRepeat lowerPeriod (n+1)
  let R := [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1)
  let ax := 4 + prefixEval (L ++ [3,1,2,3,1,2,1,3]) lowerTau +
    prefixEval (R ++ [3,2,1,3]) lowerTau
  let ay := 4 + prefixEval (L ++ [3,1,2,1,3]) lowerTau +
    prefixEval (R ++ [3,1,2,1,3]) lowerTau
  let bx := 4 + prefixEval (L ++ [3,1,3,3,2,1,3]) lowerTau +
    prefixEval (R ++ [3,3,3,1,2,1,3]) lowerTau
  let byv := 4 + prefixEval (L ++ [3,1,3,3,1,2,1,3]) lowerTau +
    prefixEval (R ++ [3,3,1,2,1,3]) lowerTau
  have hA : lowerFamilyH .auxB n 0 0 = Set.Icc (min ax ay) (max ax ay) := by
    simp only [lowerFamilyH, stage_aux_normalize]
    simp [lowerFamilyPair, ax, ay, L, R,
      List.append_assoc]
  have hB : lowerFamilyH .A (n+1) 1 0 = Set.Icc (min bx byv) (max bx byv) := by
    have hn := lower_initial_family_normalization .A (n+1) 1 0 (by decide)
    simp only [lowerFamilyH, hn]
    simp [lowerFamilyPair, bx, byv, L, R, List.append_assoc]
    congr 2 <;> ring
  have hy : ay < byv := by
    have hn := hseams.2.2.2.2.2.1 (n+1)
    dsimp [lowerNContact] at hn
    dsimp [ay, byv, L, R]
    linarith
  have hx : bx < ax := by
    have hp := hpoint n
    have hn := hseams.2.2.2.2.2.2 n
    dsimp [lowerNContact] at hn
    dsimp only at hp
    rw [stage_repeat_succ] at hp
    dsimp [bx, ax, L, R]
    rw [stage_repeat_succ]
    simp only [List.append_assoc, lowerPeriod, List.cons_append, List.nil_append] at hp hn ⊢
    linarith
  have hover : (lowerFamilyH .auxB n 0 0 ∩ lowerFamilyH .A (n+1) 1 0).Nonempty := by
    rw [hA,hB]
    exact stage_Icc_inter ax ay bx byv hy.le hx.le
  rcases hover with ⟨x,hx₁,hx₂⟩
  refine ⟨x, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx₁)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1,hx₂⟩)))

private theorem stage_point_for_all (n : ℕ) :
    let L := [3,2,1,1] ++ lowerRepeat lowerPeriod (n+1)
    let R := [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1)
    prefixEval (L ++ [3,1,3,3,2,1,3]) lowerTau +
      prefixEval (R ++ [3,3,3,1,2,1,3]) lowerTau <
    prefixEval (L ++ [3]) lowerTau + prefixEval (R ++ [3]) lowerTau := by
  let L := [3,2,1,1] ++ lowerRepeat lowerPeriod (n+1)
  let R := [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1)
  change prefixEval (L ++ _) _ + prefixEval (R ++ _) _ < _
  obtain ⟨heL,heR,hl0,hl1,hr0,hr1,hq⟩ := stage_point_parameters n
  change L.length % 2 = 0 at heL
  change R.length % 2 = 0 at heR
  change (2/3:ℝ) < lowerRatio L at hl0
  change lowerRatio L < (3/4:ℝ) at hl1
  change (2/3:ℝ) < lowerRatio R at hr0
  change lowerRatio R < (3/4:ℝ) at hr1
  have hDL := spp_D_pos L
  have hDR := spp_D_pos R
  rw [lowerRatio,lt_div_iff₀ hDL] at hl0
  rw [lowerRatio,div_lt_iff₀ hDL] at hl1
  rw [lowerRatio,lt_div_iff₀ hDR] at hr0
  rw [lowerRatio,div_lt_iff₀ hDR] at hr1
  have hdetL : (lowerInitialWordMatrix L).a*(lowerInitialWordMatrix L).d -
      (lowerInitialWordMatrix L).b*(lowerInitialWordMatrix L).c = 1 := by
    have h := (lower_initial_word_fraction L lowerTau sp_tau_pos).2.2
    rw [neg_one_pow_eq_pow_mod_two,heL,pow_zero] at h
    exact h
  have hdetR : (lowerInitialWordMatrix R).a*(lowerInitialWordMatrix R).d -
      (lowerInitialWordMatrix R).b*(lowerInitialWordMatrix R).c = 1 := by
    have h := (lower_initial_word_fraction R lowerTau sp_tau_pos).2.2
    rw [neg_one_pow_eq_pow_mod_two,heR,pow_zero] at h
    exact h
  exact stage_point_box lower_initial_word_fraction lower_initial_matrix_bottom
    L R hdetL hdetR hDL hDR hl0 hl1 hr0 hr1 hq

end M7StageOverlap

open Freiman

theorem solution
    (hseams : lowerInitialSeams) (n : ℕ) :
    (lowerInitialStage n ∩ lowerInitialStage (n+1)).Nonempty := by
  exact M7StageOverlap.stage_overlap_from_point M7StageOverlap.stage_point_for_all hseams n

#print axioms solution
