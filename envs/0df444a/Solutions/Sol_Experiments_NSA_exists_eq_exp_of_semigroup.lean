-- Prove2me | solution 1 for Experiments.NSA.exists_eq_exp_of_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:44:44.332453+00:00
-- url     : https://prove2.me/submissions/1ebe2159-6f53-4a0d-b581-63e66775dffd

import Definitions.Def_Experiments_NonstandardSemigroup
import Definitions.Def_Experiments_Ultrapower
import Definitions.Def_Experiments_UltrapowerSemigroup
import Theorems.Thm_Experiments_NSA_Approx_mul_std
import Theorems.Thm_Experiments_NSA_Approx_sub_std
import Theorems.Thm_Experiments_NSA_Approx_symm
import Theorems.Thm_Experiments_NSA_Approx_trans
import Theorems.Thm_Experiments_NSA_approx_div_omega
import Theorems.Thm_Experiments_NSA_approx_ext_of_continuousWithinAt
import Theorems.Thm_Experiments_NSA_approx_iff_sub
import Theorems.Thm_Experiments_NSA_approx_of_le_of_le
import Theorems.Thm_Experiments_NSA_approx_refl
import Theorems.Thm_Experiments_NSA_approx_slope_of_hasDerivAt
import Theorems.Thm_Experiments_NSA_approx_zero_of_norm_le
import Theorems.Thm_Experiments_NSA_eq_of_std_approx
import Theorems.Thm_Experiments_NSA_exists_std
import Theorems.Thm_Experiments_NSA_ext_comp
import Theorems.Thm_Experiments_NSA_ext_const
import Theorems.Thm_Experiments_NSA_ext_id
import Theorems.Thm_Experiments_NSA_ext_mul
import Theorems.Thm_Experiments_NSA_ext_sub
import Theorems.Thm_Experiments_NSA_imem_univ
import Theorems.Thm_Experiments_NSA_transfer_eq
import Theorems.Thm_Experiments_NSA_transfer_le
import Theorems.Thm_Experiments_NSA_transfer_mem
import Theorems.Thm_Experiments_norm_replace_steps_le


set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
namespace Experiments.NSA
theorem _root_.solution [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  -- A positive infinitesimal step `ε = 1 / (ω + 1)`.
  let e : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let ε : Hyp ℝ := ext e ω
  have hεpos : IMem ε (Ioi 0) :=
    transfer_mem (fun (n : ℕ) _ => show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity) (imem_univ ω)
  have hε : ε ≈ₕ std 0 := approx_div_omega 1
  -- The scale `η = ε + ‖*M ε - 1‖` is a positive infinitesimal, because `*M ε ≈ M 0`.
  let η : ℝ → ℝ := fun h => h + ‖M h - 1‖
  have hηh : ∀ h, 0 < h → 0 < η h := fun h hh => add_pos_of_pos_of_nonneg hh (norm_nonneg _)
  have hηpos : IMem (ext η ε) (Ioi 0) := transfer_mem (f := η) hηh hεpos
  have hη : ext η ε ≈ₕ std 0 := by
    have hc : ContinuousWithinAt η (Ioi 0) 0 :=
      (continuousWithinAt_id.add ((hcont 0 (by simp)).sub continuousWithinAt_const).norm).mono
        Ioi_subset_Ici_self
    have h := approx_ext_of_continuousWithinAt hc hεpos hε
    rwa [show η 0 = 0 by simp [η, h0]] at h
  -- On that scale the change `q` is finite, so it has a standard part `B`, and the time is
  -- infinitely close to `a = 1 - ‖B‖`.
  let q : ℝ → A := fun h => (η h)⁻¹ • (M h - 1)
  have hsum : ∀ h, 0 < h → h / η h = 1 - ‖q h‖ := fun h hh => by
    have := (hηh h hh).ne'
    simp only [q, norm_smul, norm_inv, Real.norm_of_nonneg (hηh h hh).le]
    field_simp
    simp only [η]
    ring
  have hq : ext norm (ext q ε) ≤ std 1 := by
    rw [ext_comp, ← ext_const ε (1 : ℝ)]
    exact transfer_le (fun h hh => by
      linarith [hsum h hh, div_nonneg (le_of_lt hh) (hηh h hh).le]) hεpos
  obtain ⟨B, hB1, hB⟩ := exists_std hq
  let a : ℝ := 1 - ‖B‖
  have ha : ext (fun h => h / η h) ε ≈ₕ std a := by
    have h1 : ext (fun h => h / η h) ε = std 1 - ext norm (ext q ε) := by
      rw [ext_comp norm q ε, ← ext_const ε (1 : ℝ), ← ext_sub]
      exact transfer_eq hsum hεpos
    rw [h1]
    exact (approx_refl _).sub_std
      (approx_ext_of_continuousWithinAt continuous_norm.continuousWithinAt (imem_univ _) hB)
  -- The exponential `E u = exp (u B)` takes the same step on that scale, to first order.
  let E : ℝ → A := fun u => exp (u • B)
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun u =>
    (hasDerivAt_exp_smul_const B u).continuousAt
  have hEadd : ∀ u v, E (u + v) = E u * E v := fun u v => by
    simp only [E, add_smul]
    exact exp_add_of_commute (((Commute.refl B).smul_left u).smul_right v)
  have hE0 : E 0 = 1 := by simp [E]
  let slope : ℝ → A := fun k => k⁻¹ • (E (0 + k) - E 0)
  have hslope : ext slope (ext η ε) ≈ₕ std B := by
    have h : ext slope (ext η ε) ≈ₕ std (B * E 0) :=
      approx_slope_of_hasDerivAt (hasDerivAt_exp_smul_const' B 0) hηpos hη
    rwa [hE0, mul_one] at h
  let g : ℝ → A := fun h => (η h)⁻¹ • (M h - E (η h))
  have hg : ext g ε ≈ₕ std 0 := by
    have hsplit : ext g ε = ext q ε - ext slope (ext η ε) := by
      rw [ext_comp slope η ε, ← ext_sub]
      refine transfer_eq (fun h _ => ?_) (imem_univ ε)
      simp only [g, q, slope, zero_add, hE0, smul_sub]
      abel
    have h := hB.sub_std hslope
    rwa [sub_self, ← hsplit] at h
  -- Euler's step: `M (s a) = E s` for standard `s ≥ 0`.
  have hmain : ∀ s, 0 ≤ s → M (s * a) = E s := fun s hs => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hcont.mono (Icc_subset_Ici_self : Icc 0 s ⊆ Ici 0))
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hE.continuousOn (s := Icc 0 s))
    -- Take `N = ⌊s / η⌋` steps. `M` arrives at the time `T = N ε` and `E` at `K = N η`.
    let K : ℝ → ℝ := fun k => (⌊s / k⌋₊ : ℝ) * k
    let T : ℝ → ℝ := fun h => (⌊s / η h⌋₊ : ℝ) * h
    have hKs : ∀ k, 0 < k → K k ≤ s := fun k hk =>
      (le_div_iff₀ hk).mp (Nat.floor_le (div_nonneg hs (le_of_lt hk)))
    -- The times: `K ≈ s` and `T ≈ s a`.
    have hK : ext K (ext η ε) ≈ₕ std s := by
      refine approx_of_le_of_le (lo := ext (fun k => s - k) (ext η ε))
        (hi := ext (fun _ => s) (ext η ε))
        (transfer_le (fun k hk => ?_) hηpos) (transfer_le hKs hηpos) ?_ ?_
      · have := Nat.lt_floor_add_one (s / k)
        rw [div_lt_iff₀ hk, add_one_mul] at this
        simp only [K]
        linarith
      · have h := (approx_refl (std s)).sub_std hη
        rw [sub_zero] at h
        rwa [ext_sub (fun _ => s) (fun k => k) (ext η ε), ext_const, ext_id]
      · rw [ext_const]
        exact approx_refl _
    have hT : ext T ε ≈ₕ std (s * a) := by
      have h1 : ext T ε = ext K (ext η ε) * ext (fun h => h / η h) ε := by
        rw [ext_comp K η ε, ← ext_mul]
        refine transfer_eq (fun h hh => ?_) hεpos
        have := (hηh h hh).ne'
        simp only [T, K]
        field_simp
      rw [h1]
      exact hK.mul_std ha
    have hMT : ext M (ext T ε) ≈ₕ std (M (s * a)) :=
      approx_ext_of_continuousWithinAt
        (hcont _ (mul_nonneg hs (sub_nonneg.mpr hB1)))
        (transfer_mem (f := T) (fun h hh =>
          mem_Ici.mpr (mul_nonneg (Nat.cast_nonneg _) (mem_Ioi.mp hh).le)) hεpos) hT
    have hEK : ext E (ext K (ext η ε)) ≈ₕ std (E s) :=
      approx_ext_of_continuousWithinAt hE.continuousAt.continuousWithinAt (imem_univ _) hK
    -- Replacing the steps of `M` by those of `E` changes the result by `K` times an
    -- infinitesimal.
    have hrepl : ext M (ext T ε) ≈ₕ ext E (ext K (ext η ε)) := by
      rw [approx_iff_sub, ext_comp M T ε, ext_comp K η ε, ext_comp E _ ε, ← ext_sub]
      have hk : ext K (ext η ε) * std (C * D) ≈ₕ std (s * (C * D)) :=
        hK.mul_std (approx_refl _)
      refine approx_zero_of_norm_le hk ?_ hg
      rw [ext_comp norm (fun h => M (T h) - E (K (η h))) ε, ext_comp norm g ε, ext_comp K η ε,
        ← ext_const ε (C * D), ← ext_mul, ← ext_mul]
      refine transfer_le (fun h hh => ?_) hεpos
      have hη0 := hηh h hh
      have h := norm_replace_steps_le M E h0 hadd (fun u v _ _ => hEadd u v) hC hD
        (le_of_lt hh) hη0.le ⌊s / η h⌋₊ le_rfl
        ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
          (Nat.cast_nonneg _)).trans (hKs _ hη0)) (by simpa using hKs _ hη0)
      simp only [hE0, mul_one, add_zero] at h
      have := hη0.ne'
      simp only [g, K, T, norm_smul, norm_inv, Real.norm_of_nonneg hη0.le]
      refine h.trans_eq ?_
      field_simp
    exact eq_of_std_approx ((hMT.symm.trans hrepl).trans hEK)
  -- The semigroup is not infinitely fast: `a = 0` would give `E s = 1`, so `B = 0`.
  have ha0 : a ≠ 0 := fun h => by
    have hz : ext slope (ext η ε) = std 0 := by
      rw [← ext_const (ext η ε) (0 : A)]
      refine transfer_eq (fun k hk => ?_) hηpos
      simp only [slope, zero_add, hE0, ← hmain k (le_of_lt hk), h, mul_zero, h0, sub_self,
        smul_zero]
    have hB0 : B = 0 := (eq_of_std_approx (hz ▸ hslope)).symm
    simp [a, hB0] at h
  have hapos : 0 < a := lt_of_le_of_ne (sub_nonneg.mpr hB1) (Ne.symm ha0)
  refine ⟨a⁻¹ • B, fun t ht => ?_⟩
  have h := hmain (t / a) (div_nonneg ht hapos.le)
  rw [div_mul_cancel₀ t ha0] at h
  rw [h, smul_smul, div_eq_mul_inv]
end Experiments.NSA
