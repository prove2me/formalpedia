-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.initial_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:39.589575+00:00
-- url     : https://prove2.me/submissions/49d9cc87-adde-4419-a3da-0f1a827282d0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FactorialProductRearrangement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma triangular_number_succ (j : ℕ) : (j + 1 + 1) * (j + 1) / 2 = (j + 1) * j / 2 + (j + 1) := by
  have h : (j + 1 + 1) * (j + 1) = (j + 1) * j + (j + 1) * 2 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
private lemma factorial_product_rearrangement (f k j : ℕ) (a s : ℝ) (hs : s ≠ 0) (Lval : ℕ → ℝ) :
    (∏ M ∈ Ico (k + 1) (k + j + 1), ((((M - 1).factorial : ℕ) : ℝ) * a ^ M) ^ f / s * Lval M)
        * (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f * s ^ j
      = (∏ M ∈ Ico (k + 1) (k + j + 1), Lval M) * (a ^ (j * k + (j + 1) * j / 2)) ^ f
        * (∏ i ∈ range (k + j), ((i.factorial : ℕ) : ℝ)) ^ f := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hT : k + j + 1 - 1 = k + j := by omega
    rw [show k + (j + 1) + 1 = k + j + 1 + 1 by omega,
      Finset.prod_Ico_succ_top (by omega : k + 1 ≤ k + j + 1),
      Finset.prod_Ico_succ_top (by omega : k + 1 ≤ k + j + 1),
      show k + (j + 1) = k + j + 1 by omega, Finset.prod_range_succ, hT]
    have e1 : (j + 1) * k + (j + 1 + 1) * (j + 1) / 2 = (j * k + (j + 1) * j / 2) + (k + j + 1) := by
      rw [triangular_number_succ]
      ring
    rw [e1]
    have hsx : ∀ X Y : ℝ, X / s * Y * s = X * Y := fun X Y => by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hs]
    calc _ = (∏ M ∈ Ico (k + 1) (k + j + 1), ((((M - 1).factorial : ℕ) : ℝ) * a ^ M) ^ f / s * Lval M)
            * (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f * s ^ j
            * (((((k + j).factorial : ℕ) : ℝ) * a ^ (k + j + 1)) ^ f / s * Lval (k + j + 1) * s) := by
          ring
      _ = (∏ M ∈ Ico (k + 1) (k + j + 1), Lval M) * (a ^ (j * k + (j + 1) * j / 2)) ^ f
            * (∏ i ∈ range (k + j), ((i.factorial : ℕ) : ℝ)) ^ f
            * (((((k + j).factorial : ℕ) : ℝ) * a ^ (k + j + 1)) ^ f / s * Lval (k + j + 1) * s) := by
          rw [ih]
      _ = _ := by
          rw [hsx]
          ring
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : InitialSumIdentity := by
  intro f m k vE g₁ g₂ u Dstar dstar massk massr Isig Ipi Lval dsig hm hk hv hg1 hg2 hmk hIpi
    hvand hmass hD hd
  rw [inv_div]
  have hpi := Real.pi_pos
  have hc : 0 < vE / Real.pi := div_pos hv hpi
  have h2v : 0 < 2 * vE := by positivity
  set S := Real.sqrt ((2 * vE) ^ f) with hSdef
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hbound : k - 1 + m = k + (m - 1) := by omega
  have hexp : (m - 1) * k + m * (m - 1) / 2 = (m - 1) * k + (m - 1 + 1) * (m - 1) / 2 := by
    rw [Nat.sub_add_cancel hm]
  have key := factorial_product_rearrangement f k (m - 1) (vE / Real.pi) S hS.ne' Lval
  rw [← hbound, ← hexp] at key
  set P := ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
    ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / S * Lval M with hP
  have hV : 0 < ∏ ρ ∈ range f, vandN (u ρ) k :=
    Finset.prod_pos (fun ρ hρ => hvand ρ (Finset.mem_range.mp hρ))
  have hFk : 0 < ∏ i ∈ range k, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos (fun i _ => by positivity)
  have hdim : ∏ ρ ∈ range f, dimVN (u ρ) k =
      (∏ ρ ∈ range f, vandN (u ρ) k) / (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f := by
    simp only [dimVN, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hS' : S = (2 * vE) ^ ((f : ℝ) / 2) := by
    rw [hSdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2v.le]
    congr 1
    ring
  have hT : ((2 * vE) ^ (-(((m : ℝ) - 1) / 2))) ^ f * S ^ (m - 1) = 1 := by
    rw [hS', ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h2v.le,
      ← Real.rpow_mul h2v.le, ← Real.rpow_add h2v]
    convert Real.rpow_zero (2 * vE) using 2
    rw [Nat.cast_sub hm]
    push_cast
    ring
  have hT' : ((2 * vE) ^ (-(((m : ℝ) - 1) / 2))) ^ f = (S ^ (m - 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left hT
  have hP' : P = (∏ M ∈ Ico (k + 1) (k - 1 + m + 1), Lval M) *
      ((vE / Real.pi) ^ ((m - 1) * k + m * (m - 1) / 2)) ^ f *
      (∏ i ∈ range (k - 1 + m), ((i.factorial : ℕ) : ℝ)) ^ f /
      ((∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f * S ^ (m - 1)) := by
    rw [eq_div_iff (by positivity), ← key]
    ring
  rw [hD, hd, hdim, hmass, hP']
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  rw [hT', pow_mul' (g₁ * g₂) f (k * m + m * (m - 1) / 2)]
  have h1 := hmk.ne'
  have h2 := hIpi.ne'
  have h3 := hV.ne'
  have h4 := hFk.ne'
  have h5 := hS.ne'
  have h6 : g₁ * g₂ ≠ 0 := (mul_pos hg1 hg2).ne'
  have h7 := hc.ne'
  field_simp
end Formalism.HermitianLattices.GenusMassVolumes
