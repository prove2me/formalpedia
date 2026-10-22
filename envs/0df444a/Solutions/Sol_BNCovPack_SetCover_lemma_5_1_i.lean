-- Prove2me | solution 1 for BNCovPack.SetCover.lemma_5_1_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:59:33.266986+00:00
-- url     : https://prove2.me/submissions/53c65242-8d7f-4372-be29-8201a7024679

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_BNCovPack_SetCover_Potential

set_option autoImplicit false
open OnlinePrimalDual.OnlineSetCover BNCovPack.SetCover

lemma bns_r_pos : 0 < rConst := by
  unfold rConst
  have he : (1:ℝ) < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  have hpos : 0 < Real.exp 1 - 1 := by linarith
  apply mul_pos (Real.exp_pos 1)
  apply Real.log_pos
  rw [one_lt_div hpos]; linarith

lemma bns_one_sub_ge (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.exp (-1)) :
    Real.exp (-(rConst * x)) ≤ 1 - x := by
  have he : (1:ℝ) < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hxe : Real.exp 1 * x ≤ 1 := by
    calc Real.exp 1 * x ≤ Real.exp 1 * Real.exp (-1) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hinv : (Real.exp 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ he
  have hy : (1 - (Real.exp 1)⁻¹) ∈ Set.Ioi (0:ℝ) := by
    simp only [Set.mem_Ioi]; linarith
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 one_pos) hy
    (show 0 ≤ 1 - Real.exp 1 * x by linarith) (show 0 ≤ Real.exp 1 * x by positivity)
    (show (1 - Real.exp 1 * x) + Real.exp 1 * x = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
  have h1 : (1 - Real.exp 1 * x) * 1 + Real.exp 1 * x * (1 - (Real.exp 1)⁻¹) = 1 - x := by
    field_simp; ring
  rw [h1] at hconc
  have h2 : Real.log (1 - (Real.exp 1)⁻¹) = -Real.log (Real.exp 1 / (Real.exp 1 - 1)) := by
    rw [← Real.log_inv]
    congr 1
    have : Real.exp 1 - 1 ≠ 0 := by linarith
    field_simp
  have hx_lt : 0 < 1 - x := by
    have : x < 1 := by
      calc x ≤ Real.exp (-1) := hx1
        _ < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  rw [h2] at hconc
  calc Real.exp (-(rConst * x)) ≤ Real.exp (Real.log (1 - x)) := by
        apply Real.exp_le_exp.2
        unfold rConst
        linarith
    _ = 1 - x := Real.exp_log hx_lt

lemma bns_init_bound (n OPT : ℕ) (hOPT : 1 ≤ OPT) :
    Real.exp (-(OPT : ℝ)) ≤ (1 - Real.exp (-(alphaParam n OPT))) ^ n := by
  have hr := bns_r_pos
  have hα1 : 1 ≤ alphaParam n OPT := le_max_left _ _
  have hx1 : Real.exp (-(alphaParam n OPT)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have hx0 : 0 ≤ Real.exp (-(alphaParam n OPT)) := (Real.exp_pos _).le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]
    exact Real.exp_le_one_iff.2 (by simp)
  · have hOPTpos : (0:ℝ) < OPT := by exact_mod_cast hOPT
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hrn : 0 < rConst * (n:ℝ) / (OPT:ℝ) := by positivity
    have hlog : Real.log (rConst * (n:ℝ) / (OPT:ℝ)) ≤ alphaParam n OPT := le_max_right _ _
    have hx : Real.exp (-(alphaParam n OPT)) ≤ (OPT:ℝ) / (rConst * (n:ℝ)) := by
      calc Real.exp (-(alphaParam n OPT)) ≤ Real.exp (-Real.log (rConst * (n:ℝ) / (OPT:ℝ))) :=
            Real.exp_le_exp.2 (by linarith)
        _ = (OPT:ℝ) / (rConst * (n:ℝ)) := by
            rw [Real.exp_neg, Real.exp_log hrn]; field_simp
    have hrnx : rConst * (n:ℝ) * Real.exp (-(alphaParam n OPT)) ≤ OPT := by
      have := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ rConst * (n:ℝ))
      calc _ ≤ rConst * (n:ℝ) * ((OPT:ℝ) / (rConst * (n:ℝ))) := this
        _ = OPT := by field_simp
    have hb := bns_one_sub_ge _ hx0 hx1
    calc Real.exp (-(OPT:ℝ)) ≤ Real.exp (-(rConst * Real.exp (-(alphaParam n OPT)))) ^ n := by
          rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.2
          nlinarith
      _ ≤ _ := by gcongr

theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (OPT : ℕ) (hOPT : 1 ≤ OPT) :
    potential inst (alphaParam (Fintype.card E) OPT) OPT (fun _ => 0) ∅ ≤ 1 ∧
    ∀ (α : ℝ) (w : T → ℝ) (C : Finset T), 0 < potential inst α OPT w C := by
  classical
  constructor
  · have hb := bns_init_bound (Fintype.card E) OPT hOPT
    have hα1 : 1 ≤ alphaParam (Fintype.card E) OPT := le_max_left _ _
    have hf : ∀ e : E, fval inst (alphaParam (Fintype.card E) OPT) (fun _ => 0) e
        = Real.exp (-(alphaParam (Fintype.card E) OPT)) := by
      intro e
      unfold fval elementWeight
      simp only [Finset.sum_const_zero, mul_zero, add_zero]
      exact min_eq_right (Real.exp_le_one_iff.2 (by linarith))
    have hfilt : (Finset.univ.filter (fun e : E => ¬ coveredBy inst ∅ e)) = Finset.univ := by
      ext e; simp [coveredBy]
    unfold potential potential1 potential2
    rw [hfilt]
    simp only [hf, Finset.prod_const, Finset.card_univ]
    simp only [Finset.notMem_empty, if_false, mul_zero, sub_zero, Finset.sum_const_zero, zero_sub]
    linarith
  · intro α w C
    unfold potential potential1 potential2
    have h2 := Real.exp_pos (∑ s, (Real.log 2 * (if s ∈ C then (1 : ℝ) else 0) - α * w s) - (OPT : ℝ))
    have h1 : 0 ≤ 1 - ∏ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e), (1 - fval inst α w e) := by
      have : ∏ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e), (1 - fval inst α w e) ≤ 1 := by
        apply Finset.prod_le_one
        · intro e _
          have : fval inst α w e ≤ 1 := min_le_left _ _
          linarith
        · intro e _
          have : 0 < fval inst α w e := lt_min one_pos (Real.exp_pos _)
          linarith
      linarith
    linarith
