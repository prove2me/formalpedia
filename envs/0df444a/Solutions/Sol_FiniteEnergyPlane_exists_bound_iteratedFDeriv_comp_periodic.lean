-- Prove2me | solution 1 for FiniteEnergyPlane.exists_bound_iteratedFDeriv_comp_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T14:59:32.354461+00:00
-- url     : https://prove2.me/submissions/df14adb7-ed81-4f87-8663-08949d08095a

import Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_of_periodic



namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem exists_bound_iteratedFDeriv_comp_periodic_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v)) (m : ℕ) (B : ℝ) :
    ∃ M : ℝ, ∀ (b : ℝ) (V : ℝ × ℝ → E) (Ω : Set (ℝ × ℝ)) (p : ℝ × ℝ), IsOpen Ω → p ∈ Ω →
      ContDiffOn ℝ ∞ V Ω → (∀ q ∈ Ω, ‖V q‖ ≤ r / 2) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i V p‖ ≤ B) →
      ‖iteratedFDeriv ℝ m (fun q : ℝ × ℝ => Φ (a * q.2 + b, V q)) p‖ ≤ M := by
  choose Cd hCd using fun i => exists_bound_iteratedFDeriv_of_periodic Φ T r hT hr hΦ hper i
  set ℓ₀ : ℝ × ℝ → ℝ := fun q => a * q.2 with hℓ₀def
  have hℓ₀ : ContDiff ℝ ∞ ℓ₀ := contDiff_const.mul contDiff_snd
  set C := ∑ i ∈ Finset.range (m + 1), |Cd i| with hC
  set Mℓ := ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i ℓ₀ 0‖ with hMℓ
  set D := max 1 (max Mℓ B) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  refine ⟨(m.factorial : ℝ) * C * D ^ m, fun b V Ω p hΩo hpΩ hVs hVr hVB => ?_⟩
  have hUo : IsOpen ((Set.univ : Set ℝ) ×ˢ ball (0 : E) r) := isOpen_univ.prod isOpen_ball
  set ℓ : ℝ × ℝ → ℝ := fun q => a * q.2 + b with hℓdef
  have hℓ : ContDiff ℝ ∞ ℓ := (contDiff_const.mul contDiff_snd).add contDiff_const
  -- derivatives of the affine part do not depend on the point or on `b`
  have hℓc : ∀ i : ℕ, i ≠ 0 → iteratedFDeriv ℝ i ℓ p = iteratedFDeriv ℝ i ℓ₀ 0 := by
    intro i hi
    have e : (fun z => ℓ (z + p)) = ℓ₀ + fun _ => a * p.2 + b := by
      funext z
      simp only [hℓdef, hℓ₀def, Prod.snd_add, Pi.add_apply]
      ring
    have h1 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := ℓ) i p 0
    rw [zero_add, e, iteratedFDeriv_add_apply (hℓ₀.contDiffAt.of_le (by exact_mod_cast le_top))
      contDiffAt_const, iteratedFDeriv_const_of_ne hi] at h1
    simpa using h1.symm
  set g : ℝ × ℝ → ℝ × E := fun q => (ℓ q, V q) with hgdef
  have hg : ContDiffOn ℝ ∞ g Ω := hℓ.contDiffOn.prodMk hVs
  have hmaps : Set.MapsTo g Ω (Set.univ ×ˢ ball (0 : E) r) := fun q hq =>
    ⟨trivial, mem_ball_zero_iff.2 (by linarith [hVr q hq])⟩
  have key := norm_iteratedFDerivWithin_comp_le hΦ hg (n := m)
    (by exact_mod_cast le_top) hUo.uniqueDiffOn hΩo.uniqueDiffOn hmaps hpΩ (C := C) (D := D)
    (by
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i hUo (hmaps hpΩ)]
      refine ((hCd i _ _ (hVr _ hpΩ)).trans (le_abs_self _)).trans ?_
      exact Finset.single_le_sum (f := fun j => |Cd j|) (fun j _ => abs_nonneg (Cd j))
        (Finset.mem_range.2 (by omega)))
    (by
      intro i hi1 him
      rw [iteratedFDerivWithin_of_isOpen i hΩo hpΩ]
      have hVat : ContDiffAt ℝ ∞ V p := hVs.contDiffAt (hΩo.mem_nhds hpΩ)
      rw [iteratedFDeriv_prodMk hℓ.contDiffAt hVat (by exact_mod_cast le_top),
        ContinuousMultilinearMap.opNorm_prod]
      have hDi : D ≤ D ^ i := le_self_pow₀ hD1 (by omega)
      refine max_le ?_ ?_
      · rw [hℓc i (by omega)]
        refine le_trans ?_ ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hDi)
        exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j ℓ₀ 0‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
      · exact (hVB i him).trans ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hDi))
  rw [iteratedFDerivWithin_of_isOpen m hΩo hpΩ] at key
  exact key

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v)) (m : ℕ) (B : ℝ) :
    ∃ M : ℝ, ∀ (b : ℝ) (V : ℝ × ℝ → E) (Ω : Set (ℝ × ℝ)) (p : ℝ × ℝ), IsOpen Ω → p ∈ Ω →
      ContDiffOn ℝ ∞ V Ω → (∀ q ∈ Ω, ‖V q‖ ≤ r / 2) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i V p‖ ≤ B) →
      ‖iteratedFDeriv ℝ m (fun q : ℝ × ℝ => Φ (a * q.2 + b, V q)) p‖ ≤ M :=
  exists_bound_iteratedFDeriv_comp_periodic_aux Φ T r a hT hr hΦ hper m B
