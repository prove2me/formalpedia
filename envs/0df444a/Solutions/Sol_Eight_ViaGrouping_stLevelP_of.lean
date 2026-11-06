-- Prove2me | solution 1 for Eight.ViaGrouping.stLevelP_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:39.505197+00:00
-- url     : https://prove2.me/submissions/779e12b7-edd3-42c9-9dc6-2ec2a90ee507

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Definitions.Def_Eight_Level_Arith
import Definitions.Def_Eight_Level_Min
import Definitions.Def_StepMachines_Prog_GridLoop
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Level
import Theorems.Thm_Eight_Level_eqExpansion_words
import Theorems.Thm_Eight_Level_level_size
import Theorems.Thm_Eight_Level_level_time
import Theorems.Thm_Eight_Level_stMin
import Theorems.Thm_Eight_ViaGrouping_Correct_absorb
import Theorems.Thm_Eight_ViaGrouping_U_levelNetP
import Theorems.Thm_Eight_ViaGrouping_levelNetP_isNetworkP_of
import Theorems.Thm_Eight_ViaGrouping_value_levelNetP
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_abs_value_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_bind_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_natAbs_sum_le
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
import Theorems.Thm_Groundwork_Stepped_sumRange_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_P2M_Eight_Level_netOf__sized_t_6d348568ee7d
import Theorems.Thm_P2M_Eight_Level_value_netOf__39744228d791
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_SingleBitPieces_Level_level_size
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (hPr : StPresents) : StLevelP := by
  intro K g e psiR psiC NA hK hg h0 hΨr hΨc h
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha1, ha⟩ := levelNetP_isNetworkP_of hPr g hg1
  obtain ⟨A, hA⟩ := h.absorb
  obtain ⟨A1, hA1⟩ := level_time g K a A hK hg h0 (nRect g)
  obtain ⟨A2, hA2⟩ := level_size g a A (nRect g)
  refine ⟨A1 + A2, fun C _ lam R c B t S Rm hl ht hR => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = lam c := ⟨_, rfl⟩
  rw [← hn] at hl hR ⊢
  obtain ⟨M, hM⟩ : ∃ M, M = (tOf n + 1) * nRect g := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = g ^ 3 * n := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' = g * B + g ^ 2 * tOf n := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t', t' = a * (B + n) ^ a * t := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S', S' = S + a * (size c + B + n) ^ a := ⟨_, rfl⟩
  obtain ⟨Zt, hZt⟩ : ∃ Zt : ℕ → ℤ, Zt = fun y => Zι (gridR0 g g n Rm) (Level.patOf g n y) := ⟨_, rfl⟩
  have htn : tOf n ≤ n := by unfold tOf; omega
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.mul_pos (pow_pos hg1 3) hl
  have ht'1 : 1 ≤ t' := by
    rw [ht']
    exact Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos (by omega) a)) ht
  have hNp : (tOf n + 1) ^ nRect g ≤ 2 ^ M := by
    rw [hM, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hBd : BoundedInst n B Rm := fun v θ h1 h2 => (hR v θ h1 h2).2
  -- the two networks of ι: «Both networks satisfy Definition 2 …», «the value is Z_ι», the totals
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℕ → Net g, Nr = fun y => levelNetP g false n y Rm := ⟨_, rfl⟩
  obtain ⟨Nc, hNc⟩ : ∃ Nc : ℕ → Net g, Nc = fun y => levelNetP g true n y Rm := ⟨_, rfl⟩
  have hnet : ∀ y < (tOf n + 1) ^ nRect g,
      (IsNetworkP (levelProcs g false psiR lam R) (c, y) (Nr y) P (B' + 1) t' (S' + 2) ∧ (Nr y).value = Zt y ∧ (Nr y).U = totalG eightF g g false 0 n y) ∧
      (IsNetworkP (levelProcs g true psiC lam R) (c, y) (Nc y) P (B' + 1) t' (S' + 2) ∧ (Nc y).value = Zt y ∧ (Nc y).U = totalG eightF g g true 0 n y) := by
    intro y hy
    rw [hNr, hNc]
    refine ⟨⟨?_, ?_, U_levelNetP g false n y Rm⟩, ⟨?_, ?_, U_levelNetP g true n y Rm⟩⟩
    · have h1 := ha false psiR hΨr C lam R c B t S Rm y (hn ▸ hl) ht (hn ▸ hy) (hn ▸ hR)
      rw [← hn] at h1
      rw [hP, hB', ht', hS']
      exact h1
    · rw [hZt]; exact value_levelNetP hl g false y Rm
    · have h1 := ha true psiC hΨc C lam R c B t S Rm y (hn ▸ hl) ht (hn ▸ hy) (hn ▸ hR)
      rw [← hn] at h1
      rw [hP, hB', ht', hS']
      exact h1
    · rw [hZt]; exact value_levelNetP hl g true y Rm
  obtain ⟨Ub, hUb⟩ : ∃ Ub : ℝ, Ub = rho * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 3 * n + 2 * (g : ℝ) ^ 4 := ⟨_, rfl⟩
  -- one ι
  have key : ∀ y : ℕ, ∃ τ : ℕ, y < (tOf n + 1) ^ nRect g →
      (Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R))).Runs (c, y) τ
        (S' + A * (size c + (M + 1) + P + B') ^ A + 1) (Zt y) ∧
      (τ : ℝ) + 1 ≤ ((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' := by
    intro y
    by_cases hy : y < (tOf n + 1) ^ nRect g
    swap
    · exact ⟨0, fun h => absurd h hy⟩
    obtain ⟨⟨hpr, hvr, hur⟩, ⟨hpc, hvc, huc⟩⟩ := hnet y hy
    have hsz : size (c, y) ≤ size c + (M + 1) := by
      have := Nat.size_le.2 (hy.trans_le hNp)
      simp only [size_prod, size_nat]
      omega
    have hmonoS : S' + A * (size (c, y) + P + B') ^ A ≤ S' + A * (size c + (M + 1) + P + B') ^ A :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) _
    have hmin := stMin g n y hl
    have tail : ∀ U τ : ℕ, U ≤ min (totalG eightF g g false 0 n y) (totalG eightF g g true 0 n y) →
        (τ : ℝ) ≤ A * (2 : ℝ) ^ (e * (U : ℝ) + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' →
        (τ : ℝ) + 1 ≤ ((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' := by
      intro U τ hU hτ
      have hU' : (U : ℝ) ≤ Ub := by
        have : (U : ℝ) ≤ ((min (totalG eightF g g false 0 n y) (totalG eightF g g true 0 n y) : ℕ) : ℝ) := by exact_mod_cast hU
        rw [hUb]
        linarith
      have hUb0 : 0 ≤ Ub := le_trans (Nat.cast_nonneg U) hU'
      have hX : (1 : ℝ) ≤ (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) :=
        Real.one_le_rpow (by norm_num)
          (add_nonneg (mul_nonneg h0 hUb0) (div_nonneg (mul_nonneg (by linarith) (by positivity)) (Nat.cast_nonneg _)))
      have hY : (1 : ℝ) ≤ ((P : ℝ) + B') ^ A := by
        refine one_le_pow₀ ?_
        have h5 : (1 : ℝ) ≤ P := by exact_mod_cast hP1
        have h6 : (0 : ℝ) ≤ (B' : ℝ) := Nat.cast_nonneg _
        linarith
      have htr : (1 : ℝ) ≤ t' := by exact_mod_cast ht'1
      have h3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hY) htr
      have h4 : (τ : ℝ) ≤ A * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' := by
        refine hτ.trans ?_
        gcongr
        norm_num
      calc _ ≤ _ := add_le_add h4 h3
        _ = _ := by ring
    by_cases hu : totalG eightF g g false 0 n y ≤ totalG eightF g g true 0 n y
    · obtain ⟨τ, hτ1, hτ2⟩ := hA _ (levelProcs g false psiR lam R) (c, y) (Nr y) P B' t' S' hpr
      rw [hvr] at hτ1
      have hdec : useRowP g lam (c, y) = true := by
        show decide (totalG eightF g g false 0 (lam c) y ≤ totalG eightF g g true 0 (lam c) y) = true
        rw [← hn]
        exact decide_eq_true hu
      exact ⟨τ, fun _ => ⟨ite_runs_true hdec (hτ1.mono le_rfl hmonoS), tail _ _ (by rw [min_eq_left hu, hur]) hτ2⟩⟩
    · obtain ⟨τ, hτ1, hτ2⟩ := hA _ (levelProcs g true psiC lam R) (c, y) (Nc y) P B' t' S' hpc
      rw [hvc] at hτ1
      have hdec : useRowP g lam (c, y) = false := by
        show decide (totalG eightF g g false 0 (lam c) y ≤ totalG eightF g g true 0 (lam c) y) = false
        rw [← hn]
        exact decide_eq_false hu
      exact ⟨τ, fun _ => ⟨ite_runs_false hdec (hτ1.mono le_rfl hmonoS), tail _ _ (by rw [min_eq_right (not_le.1 hu).le, huc]) hτ2⟩⟩
  choose τ hτ using key
  -- the loop
  obtain ⟨v, hv⟩ : ∃ v, v = g * (P + B') + g * g * B' := ⟨_, rfl⟩
  have hN : numPat8 g lam c = (tOf n + 1) ^ nRect g := by rw [hn]; rfl
  have habs : ∀ y < (tOf n + 1) ^ nRect g, (Zt y).natAbs ≤ 2 ^ v := fun y hy => by
    have h0 : Network.value (J := Fin g) (netOfι g false n y Rm) = Zt y := by rw [hZt]; exact value_netOfι hl g false y Rm
    have h1 := abs_value_le (J := Fin g) (netOfι g false n y Rm) (netOfι_sized_t hl g false y hBd)
    rw [h0, Int.abs_eq_natAbs, Fintype.card_fin, ← hP, ← hB', ← hv] at h1
    exact_mod_cast h1
  have hrun := sumRange_runs (N := numPat8 g lam) (a := c)
    (M := Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R)))
    τ Zt (2 ^ v) (S' + A * (size c + (M + 1) + P + B') ^ A + 1)
    (fun y hy => (hτ y (hN ▸ hy)).1) (fun y hy => habs y (hN ▸ hy))
  rw [hN] at hrun
  -- the division
  have hZ : ((2 : ℤ) ^ tOf n) ^ nRect g * Inst.ZW n [] Rm = ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y := by
    rw [hZt, ← pow_mul]
    exact eqExpansion_words hl Rm
  have hdiv : (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) / ((2 ^ (tOf (lam c) * nRect g) : ℕ) : ℤ) = Inst.ZW n [] Rm := by
    rw [← hZ, ← hn, ← pow_mul]
    push_cast
    exact Int.mul_ediv_cancel_left _ (by positivity)
  have hfin := ofFun_runs (fun p : C × ℤ => p.2 / ((2 ^ (tOf (lam p.1) * nRect g) : ℕ) : ℤ)) (c, ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y)
  simp only [hdiv] at hfin
  have hall := bind_runs hrun hfin
  refine ⟨_, hall.mono le_rfl ?_, ?_⟩
  · -- sizes
    have h2 := hA2 (size c) B n M P B' hl
      (by
        rw [hM]
        calc (tOf n + 1) * nRect g ≤ 2 * n * nRect g := Nat.mul_le_mul_right _ (by omega)
          _ = 2 * nRect g * n := by ring)
      hP.le
      (by
        have e : (g + 2 * g ^ 2) * (B + n) = g * B + g ^ 2 * n + (g * n + 2 * g ^ 2 * B + g ^ 2 * n) := by ring
        have e2 : g ^ 2 * tOf n ≤ g ^ 2 * n := Nat.mul_le_mul_left _ htn
        omega)
    have h3 : A2 * (size c + B + n) ^ A2 ≤ (A1 + A2) * (size c + B + n) ^ (A1 + A2) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    have s1 : size ((tOf n + 1) ^ nRect g) ≤ M + 2 := by
      rw [size_nat]
      have := Nat.size_le_size hNp
      rw [Nat.size_pow] at this
      omega
    have hNV : (tOf n + 1) ^ nRect g * 2 ^ v ≤ 2 ^ (M + v) := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ hNp
    have s2 : size ((tOf n + 1) ^ nRect g * 2 ^ v) ≤ M + v + 2 := by
      rw [size_nat]
      have := Nat.size_le_size hNV
      rw [Nat.size_pow] at this
      omega
    have hSum : (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y).natAbs ≤ 2 ^ (M + v) := by
      refine (Int.natAbs_sum_le _ _).trans (le_trans ?_ hNV)
      calc ∑ y ∈ range ((tOf n + 1) ^ nRect g), (Zt y).natAbs ≤ ∑ _y ∈ range ((tOf n + 1) ^ nRect g), 2 ^ v :=
            Finset.sum_le_sum fun y hy => habs y (Finset.mem_range.1 hy)
        _ = (tOf n + 1) ^ nRect g * 2 ^ v := by rw [Finset.sum_const, card_range, smul_eq_mul]
    have s3 : size (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) ≤ M + v + 2 := by
      rw [size_int]
      have := Nat.size_le_size hSum
      rw [Nat.size_pow] at this
      omega
    have hZle : (Inst.ZW n [] Rm).natAbs ≤ 2 ^ (M + v) := by
      refine le_trans ?_ hSum
      rw [← hZ, Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.2 (by positivity))
    have s4 : size (Inst.ZW n [] Rm) ≤ M + v + 2 := by
      rw [size_int]
      have := Nat.size_le_size hZle
      rw [Nat.size_pow] at this
      omega
    simp only [size_prod]
    rw [hS']
    omega
  · -- steps
    have hsum : ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) : ℕ) : ℝ) ≤ (((tOf n + 1) ^ nRect g : ℕ) : ℝ) *
        (((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t') := by
      rw [Nat.cast_sum]
      calc _ ≤ ∑ _y ∈ range ((tOf n + 1) ^ nRect g),
            (((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t') :=
            Finset.sum_le_sum fun y hy => by
              have := (hτ y (Finset.mem_range.1 hy)).2
              push_cast
              exact this
        _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    have h4 := hA1 B n t hl ht
    rw [← hP, ← hB', ← ht', ← hUb] at h4
    have h5 : ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) + 1 + 1 : ℕ) : ℝ) =
        ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) : ℕ) : ℝ) + 2 := by push_cast; ring
    rw [h5]
    refine le_trans (by linarith) (h4.trans ?_)
    have hBl : (1 : ℝ) ≤ (B : ℝ) + n := by
      have h5 : (1 : ℝ) ≤ n := by exact_mod_cast hl
      have h6 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
      linarith
    gcongr
    · exact_mod_cast Nat.le_add_right A1 A2
    · exact Nat.le_add_right A1 A2
end Eight.ViaGrouping
