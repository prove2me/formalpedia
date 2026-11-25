-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.count_block0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:53.828794+00:00
-- url     : https://prove2.me/submissions/aa4429b7-d365-4b24-b76b-714939d789c2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneSubTwoCpowLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ZeroCountFirst
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_dyadic_block_count
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_dyadic_index_le_log
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_first_small_condition
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_off_diagonal_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_rpow_neg_exponent_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_rpow_pos_exponent_bound
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_one_le_log_of_three_le__619f5b1cd3f0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (M : ℕ) (T σ c : ℝ) (S : Finset (DirichletCharacter ℂ 1 × ℂ)) (N U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 512 ≤ qd M T) (hc0 : 0 < c)
    (hc : 87880000 / c ^ 2 * Real.log (qd M T) ^ 7 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
      ‖blkD (pYd M T) N U (fun n => p.1 (n : ZMod 1)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) *
      ((50 * Real.log ((M : ℝ) * T) * (2 * Real.log ((M : ℝ) * T))) ^ 2 / c ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (512 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le' (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le' (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := dyadic_index_le_log q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) + 1 := by positivity
  have hl0 : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
  have hl : 1 + Real.log (2 * (U : ℝ)) ≤ 13 * Real.log q := by
    have h1 : (2 * (U : ℝ)) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU2
    have h2 : Real.log (2 * (U : ℝ)) ≤ Real.log ((q : ℝ) ^ 12) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hG : 9 + 8 * Real.log (2 * T + 1) ≤ 17 * Real.log x := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    linarith
  have hG0 : 0 ≤ 9 + 8 * Real.log (2 * T + 1) := by
    have : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    linarith
  have hK0 : 0 ≤ 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * q := by
    have : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * x := by
      rw [hx]; push_cast; nlinarith
    linarith
  have hθ : (0 : ℝ) < c / (((pJd M T : ℝ) + 1) * Real.log q) := by positivity
  have hsmall := first_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T)) ((pJd M T : ℝ) + 1) q (Real.sqrt q) (Real.log q) c
    (by linarith) (Real.sqrt_pos.2 (by linarith)) hc0 (rpow_neg_exponent_bound q U σ (by omega) hσ hU1)
    (by linarith) hl hK0 hK hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod 1)) (fun p => p.2) (pYd M T) N U σ
    (c / (((pJd M T : ℝ) + 1) * Real.log q)) (9 + 8 * Real.log (2 * T + 1))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound 1 S σ T U hU hT (by linarith) hS (fun p hp p' hp' hne _ => hsp p hp p' hp' hne))
    hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (c / (((pJd M T : ℝ) + 1) * Real.log q)) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * ((((pJd M T : ℝ) + 1) * Real.log q) ^ 2 / c ^ 2) := by
    have hLq0 : Real.log q ≠ 0 := by linarith
    field_simp
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) + 1 ≤ 50 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  have hLq00 : 0 ≤ Real.log q := by linarith
  gcongr
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
