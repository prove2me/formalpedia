-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.pairs_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:26.90319+00:00
-- url     : https://prove2.me/submissions/b8b21030-b0d7-4f14-a795-a386ffa93088

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_diff
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_primePowerSum_eq_sum_Icc
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_RR_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_aW_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_gW_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_aW_self
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_gW_eq_of_tPart_eq_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_dbl_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Pairs
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
  set P := (Icc 1 N).filter Nat.Prime with hPdef
  have hpt : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, (if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
      ∑ p ∈ P, aW c p n * aW c p n' + gW c m₀ n * gW c m₀ n' := by
    intro n hnN n' _
    have h0 : 0 ≤ ∑ p ∈ P, aW c p n * aW c p n' :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _))
    have h0' : 0 ≤ gW c m₀ n * gW c m₀ n' := mul_nonneg (gW_nonneg hc _ _) (gW_nonneg hc _ _)
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    have p1 := Nat.minFac_prime hn.ne_one
    by_cases he : n.minFac = n'.minFac
    · have hmem : n.minFac ∈ P := by
        rw [hPdef, Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hnN
        exact ⟨⟨p1.one_lt.le, le_trans (Nat.minFac_le (by omega)) hnN.2⟩, p1⟩
      have hsingle := Finset.single_le_sum (f := fun p => aW c p n * aW c p n')
        (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _)) hmem
      have ha : aW c n.minFac n = c n := aW_self hn
      have hb : aW c n.minFac n' = c n' := by rw [he]; exact aW_self hn'
      simp only [ha, hb] at hsingle
      linarith
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      have t1 : tPart m₀ n = 1 := Nat.eq_one_of_mul_eq_one_right hd.symm
      have t2 : tPart m₀ n' = 1 := Nat.eq_one_of_mul_eq_one_left hd.symm
      rw [gW_eq_of_tPart_eq_one hn t1, gW_eq_of_tPart_eq_one hn' t2]
      linarith
  have e : ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, aW c p n * aW c p n' = ∑ p ∈ P, sP c N p ^ 2 := by
    calc _ = ∑ n ∈ Icc 1 N, ∑ p ∈ P, ∑ n' ∈ Icc 1 N, aW c p n * aW c p n' :=
          Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
      _ = ∑ p ∈ P, ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, aW c p n * aW c p n' := Finset.sum_comm
      _ = ∑ p ∈ P, sP c N p ^ 2 := Finset.sum_congr rfl (fun p _ => by rw [dbl_sum, ← primePowerSum_eq_sum_Icc, sq])
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = 1 then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, (∑ p ∈ P, aW c p n * aW c p n' + gW c m₀ n * gW c m₀ n') :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun n' hn' => hpt n hn n' hn'))
    _ = ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, aW c p n * aW c p n' +
          ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, gW c m₀ n * gW c m₀ n' := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => Finset.sum_add_distrib)
    _ = (∑ p ∈ P, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
        rw [e, dbl_sum, ← RR_eq, sq]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
