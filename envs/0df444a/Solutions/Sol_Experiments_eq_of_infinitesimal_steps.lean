-- Prove2me | solution 1 for Experiments.eq_of_infinitesimal_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:38.659799+00:00
-- url     : https://prove2.me/submissions/2074ed77-a5ae-474e-b0d7-050a41d54cbd

import Mathlib
import Definitions.Def_Experiments_NonstandardSemigroup
import Theorems.Thm_Experiments_norm_replace_steps_le

set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A]
namespace Experiments
theorem _root_.solution (M E : ℝ → A)
    (hM : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (hE : ContinuousOn E (Ici 0)) (hE0 : E 0 = 1)
    (hEadd : ∀ s t, 0 ≤ s → 0 ≤ t → E (s + t) = E s * E t)
    {ι : Type*} {l : Filter ι} [l.NeBot] (δ η : ι → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδη : ∀ n, δ n ≤ η n) (hη : ∀ n, 0 < η n) (hz : Tendsto η l (𝓝 0)) {a : ℝ}
    (ha : Tendsto (fun n => δ n / η n) l (𝓝 a))
    (hstep : Tendsto (fun n => (η n)⁻¹ • (M (δ n) - E (η n))) l (𝓝 0)) {s : ℝ} (hs : 0 ≤ s) :
    M (s * a) = E s := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hM.mono (Icc_subset_Ici_self : Icc 0 s ⊆ Ici 0))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hE.mono (Icc_subset_Ici_self : Icc 0 s ⊆ Ici 0))
  -- Take `N = ⌊s / η⌋` steps. The times: `N η ≈ s` and `N δ ≈ s a`.
  let N : ι → ℕ := fun n => ⌊s / η n⌋₊
  have hNs : ∀ n, (N n : ℝ) * η n ≤ s := fun n =>
    (le_div_iff₀ (hη n)).mp (Nat.floor_le (div_nonneg hs (hη n).le))
  have hNη : Tendsto (fun n => (N n : ℝ) * η n) l (𝓝 s) := by
    have hlo : ∀ n, s - η n ≤ (N n : ℝ) * η n := fun n => by
      have := Nat.lt_floor_add_one (s / η n)
      rw [div_lt_iff₀ (hη n), add_one_mul] at this
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hz) tendsto_const_nhds hlo hNs
  have hNδ : Tendsto (fun n => (N n : ℝ) * δ n) l (𝓝 (s * a)) :=
    (hNη.mul ha).congr fun n => by
      have := (hη n).ne'
      field_simp
  have ha0 : 0 ≤ a := ge_of_tendsto' ha fun n => div_nonneg (hδ n) (hη n).le
  have hMlim : Tendsto (fun n => M (N n * δ n)) l (𝓝 (M (s * a))) :=
    (hM _ (mul_nonneg hs ha0)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hNδ, Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (hδ n)⟩)
  have hElim : Tendsto (fun n => E (N n * η n)) l (𝓝 (E s)) :=
    (hE s hs).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hNη, Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (hη n).le⟩)
  -- Replacing the steps of `M` by those of `E` changes the result by `N η` times an
  -- infinitesimal.
  have hrepl : ∀ n, ‖M (N n * δ n) - E (N n * η n)‖ ≤
      N n * η n * (C * D * ‖(η n)⁻¹ • (M (δ n) - E (η n))‖) := fun n => by
    have h := norm_replace_steps_le M E h0 hadd hEadd hC hD (hδ n) (hη n).le (N n) le_rfl
      ((mul_le_mul_of_nonneg_left (hδη n) (Nat.cast_nonneg _)).trans (hNs n))
      (by simpa using hNs n)
    simp only [hE0, mul_one, add_zero] at h
    have := (hη n).ne'
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (hη n).le]
    refine h.trans_eq ?_
    field_simp
  have hzero : Tendsto (fun n => M (N n * δ n) - E (N n * η n)) l (𝓝 0) :=
    squeeze_zero_norm hrepl (by simpa using hNη.mul (hstep.norm.const_mul (C * D)))
  exact sub_eq_zero.mp (tendsto_nhds_unique (hMlim.sub hElim) hzero)
end Experiments
