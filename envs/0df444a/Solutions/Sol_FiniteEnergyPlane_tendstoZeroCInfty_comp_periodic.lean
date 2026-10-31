-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoZeroCInfty_comp_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T10:33:12.253507+00:00
-- url     : https://prove2.me/submissions/97ed117d-ec47-44d8-ab5e-bf2f2817265f

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd
import Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_of_periodic



namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem tendstoZeroCInfty_comp_periodic_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a b : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0)
    (v : ℝ × ℝ → E) (hv : TendstoZeroCInfty v) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => Φ (a * p.2 + b, v p)) := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_le_mul_norm_of_periodic Φ T r hT hr
    (hΦ.of_le (by exact_mod_cast le_top)) hper h0
  obtain ⟨⟨s₀, hvs⟩, hvl⟩ := hv
  have hvl0 : ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖v (s, t)‖ ≤ ε := by
    intro ε hε
    obtain ⟨s₁, h⟩ := hvl 0 ε hε
    exact ⟨s₁, fun s hs t => by simpa [norm_iteratedFDeriv_zero] using h s hs t⟩
  obtain ⟨s₂, hs₂⟩ := hvl0 (r / 2) (half_pos hr)
  set S := max s₀ s₂ with hS
  set Ω : Set (ℝ × ℝ) := Set.Ioi S ×ˢ Set.univ with hΩ
  have hΩo : IsOpen Ω := isOpen_Ioi.prod (isOpen_univ (X := ℝ))
  have hUo : IsOpen ((Set.univ : Set ℝ) ×ˢ ball (0 : E) r) := isOpen_univ.prod isOpen_ball
  have hΩsub : Ω ⊆ Set.Ioi s₀ ×ˢ Set.univ := by
    rintro ⟨s, t⟩ ⟨hs, -⟩
    exact ⟨show s₀ < s from lt_of_le_of_lt (le_max_left s₀ s₂) hs, trivial⟩
  have hvS : ∀ p ∈ Ω, ‖v p‖ ≤ r / 2 := by
    rintro ⟨s, t⟩ ⟨hs, -⟩
    exact hs₂ s (le_trans (le_max_right _ _) (le_of_lt hs)) t
  set ℓ : ℝ × ℝ → ℝ := fun p => a * p.2 + b with hℓdef
  have hℓ : ContDiff ℝ ∞ ℓ := (contDiff_const.mul contDiff_snd).add contDiff_const
  set g : ℝ × ℝ → ℝ × E := fun p => (ℓ p, v p) with hgdef
  have hg : ContDiffOn ℝ ∞ g Ω := hℓ.contDiffOn.prodMk (hvs.mono hΩsub)
  have hmaps : Set.MapsTo g Ω (Set.univ ×ˢ ball (0 : E) r) := fun p hp =>
    ⟨trivial, mem_ball_zero_iff.2 (by linarith [hvS p hp])⟩
  have hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Φ (a * p.2 + b, v p)) Ω := hΦ.comp hg hmaps
  -- derivatives of the affine part do not depend on the point
  have hℓc : ∀ i : ℕ, i ≠ 0 → ∀ p, iteratedFDeriv ℝ i ℓ p = iteratedFDeriv ℝ i ℓ 0 := by
    intro i hi p
    have e : (fun z => ℓ (z + p)) = ℓ + fun _ => a * p.2 := by
      funext z
      simp only [hℓdef, Prod.snd_add, Pi.add_apply]
      ring
    have h1 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := ℓ) i p 0
    rw [zero_add, e, iteratedFDeriv_add_apply (hℓ.contDiffAt.of_le (by exact_mod_cast le_top))
      contDiffAt_const, iteratedFDeriv_const_of_ne hi] at h1
    simpa using h1.symm
  refine tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd _ S hf ?_ ?_
  · intro ε hε
    have hL1 : 0 < L + 1 := by linarith
    obtain ⟨s₃, hs₃⟩ := hvl0 (min (r / 2) (ε / (L + 1))) (lt_min (half_pos hr) (by positivity))
    refine ⟨s₃, fun s hs t => ?_⟩
    show ‖Φ (a * t + b, v (s, t))‖ ≤ ε
    have h1 := hs₃ s hs t
    have h2 := hL (a * t + b) (v (s, t)) (h1.trans (min_le_left _ _))
    have h3 : L * ‖v (s, t)‖ ≤ L * (ε / (L + 1)) :=
      mul_le_mul_of_nonneg_left (h1.trans (min_le_right _ _)) hL0
    have h4 : L * (ε / (L + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hL1]
      nlinarith
    linarith
  · intro m
    choose Cd hCd using fun i => exists_bound_iteratedFDeriv_of_periodic Φ T r hT hr hΦ hper i
    choose sv hsv using fun i => hvl i 1 one_pos
    set C := ∑ i ∈ Finset.range (m + 1), |Cd i| with hC
    set Mℓ := ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i ℓ 0‖ with hMℓ
    set D := max 1 Mℓ with hD
    have hD1 : 1 ≤ D := le_max_left _ _
    set s₁ := max (S + 1) (∑ i ∈ Finset.range (m + 1), |sv i|) with hs₁
    refine ⟨(m.factorial : ℝ) * C * D ^ m, s₁, fun s hs t => ?_⟩
    have hsS : S < s := by linarith [le_of_max_le_left hs]
    have hpΩ : ((s, t) : ℝ × ℝ) ∈ Ω := ⟨hsS, trivial⟩
    have hsv_le : ∀ i ≤ m, sv i ≤ s := fun i hi =>
      (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (sv j))
        (Finset.mem_range.2 (by omega))).trans (le_of_max_le_right hs))
    have key := norm_iteratedFDerivWithin_comp_le hΦ hg (n := m)
      (by exact_mod_cast le_top) hUo.uniqueDiffOn hΩo.uniqueDiffOn hmaps hpΩ (C := C) (D := D)
      (by
        intro i hi
        rw [iteratedFDerivWithin_of_isOpen i hUo (hmaps hpΩ)]
        refine ((hCd i _ _ (hvS _ hpΩ)).trans (le_abs_self _)).trans ?_
        exact Finset.single_le_sum (f := fun j => |Cd j|) (fun j _ => abs_nonneg (Cd j))
          (Finset.mem_range.2 (by omega)))
      (by
        intro i hi1 him
        rw [iteratedFDerivWithin_of_isOpen i hΩo hpΩ]
        have hvat : ContDiffAt ℝ ∞ v (s, t) :=
          hvs.contDiffAt ((isOpen_Ioi.prod (isOpen_univ (X := ℝ))).mem_nhds (hΩsub hpΩ))
        rw [iteratedFDeriv_prodMk hℓ.contDiffAt hvat (by exact_mod_cast le_top),
          ContinuousMultilinearMap.opNorm_prod]
        have hDi : D ≤ D ^ i := le_self_pow₀ hD1 (by omega)
        refine max_le ?_ ?_
        · rw [hℓc i (by omega)]
          refine le_trans ?_ ((le_max_right _ _).trans hDi)
          exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j ℓ 0‖)
            (fun j _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
        · exact (hsv i s (hsv_le i him) t).trans (hD1.trans hDi))
    rw [iteratedFDerivWithin_of_isOpen m hΩo hpΩ] at key
    exact key

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a b : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0)
    (v : ℝ × ℝ → E) (hv : TendstoZeroCInfty v) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => Φ (a * p.2 + b, v p)) :=
  tendstoZeroCInfty_comp_periodic_aux Φ T r a b hT hr hΦ hper h0 v hv
