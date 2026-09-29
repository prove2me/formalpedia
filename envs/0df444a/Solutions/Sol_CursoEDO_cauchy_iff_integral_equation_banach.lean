-- Prove2me | solution 1 for CursoEDO.cauchy_iff_integral_equation_banach
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T15:15:20.738988+00:00
-- url     : https://prove2.me/submissions/620c0b86-481d-4b84-8dd8-4a832254ebfc

import Mathlib
import Definitions.Def_CursoEDO_Defs

open Set MeasureTheory CursoEDO

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (U : Set (ℝ × E)) (t₀ : ℝ) (x₀ : E) (α : ℝ) (φ : ℝ → E)
    (hα : 0 < α)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) U)
    (hφ : ContinuousOn φ (Set.Icc (t₀ - α) (t₀ + α)))
    (hgraph : ∀ t ∈ Set.Icc (t₀ - α) (t₀ + α), (t, φ t) ∈ U) :
    IsCauchySolutionOn f U t₀ x₀ (Set.Icc (t₀ - α) (t₀ + α)) φ ↔
      ∀ t ∈ Set.Icc (t₀ - α) (t₀ + α), φ t = x₀ + ∫ s in t₀..t, f s (φ s) := by
  set J : Set ℝ := Set.Icc (t₀ - α) (t₀ + α) with hJ
  have hle : t₀ - α ≤ t₀ + α := by linarith
  have ht₀J : t₀ ∈ J := ⟨by linarith, by linarith⟩
  have hJconv : Convex ℝ J := convex_Icc _ _
  -- the integrand along the curve
  set g : ℝ → E := fun s => f s (φ s) with hgdef
  have hgcont : ContinuousOn g J := by
    have hpair : ContinuousOn (fun s : ℝ => (s, φ s)) J := continuousOn_id.prodMk hφ
    exact hcont.comp hpair (fun t ht => hgraph t ht)
  -- a continuous extension of `g` to the whole line, obtained by clamping the time
  set c : ℝ → ℝ := fun s => max (t₀ - α) (min (t₀ + α) s) with hcdef
  have hccont : Continuous c := by fun_prop
  have hcmem : ∀ s, c s ∈ J := fun s =>
    ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩
  have hceq : ∀ s ∈ J, c s = s := by
    rintro s ⟨h1, h2⟩
    rw [hcdef]
    simp [min_eq_right h2, max_eq_right h1]
  set G : ℝ → E := fun s => g (c s) with hGdef
  have hGcont : Continuous G := hgcont.comp_continuous hccont hcmem
  have hGg : ∀ s ∈ J, G s = g s := fun s hs => by rw [hGdef]; simp [hceq s hs]
  -- the two integrals agree on `J`
  have hsub : ∀ t ∈ J, Set.uIcc t₀ t ⊆ J := by
    intro t ht
    rw [hJ, ← Set.uIcc_of_le hle]
    exact Set.uIcc_subset_uIcc (by rw [Set.uIcc_of_le hle]; exact ht₀J)
      (by rw [Set.uIcc_of_le hle]; exact ht)
  have hintegral : ∀ t ∈ J, (∫ s in t₀..t, G s) = ∫ s in t₀..t, g s := fun t ht =>
    intervalIntegral.integral_congr fun s hs => hGg s (hsub t ht hs)
  -- the primitive of the extended integrand
  set ψ : ℝ → E := fun t => x₀ + ∫ s in t₀..t, G s with hψdef
  have hψderiv : ∀ t : ℝ, HasDerivAt ψ (G t) t := fun t =>
    (intervalIntegral.integral_hasDerivAt_right (hGcont.intervalIntegrable _ _)
      (hGcont.stronglyMeasurableAtFilter _ _) hGcont.continuousAt).const_add x₀
  have hψt₀ : ψ t₀ = x₀ := by simp [hψdef]
  have hψeq : ∀ t ∈ J, ψ t = x₀ + ∫ s in t₀..t, g s := fun t ht =>
    congrArg (fun y => x₀ + y) (hintegral t ht)
  constructor
  · rintro ⟨-, hφ₀, -, hderiv⟩ t ht
    -- `φ - ψ` has vanishing derivative on the interval, hence is constant there
    have hzero : ∀ x ∈ J, HasDerivWithinAt (fun u => φ u - ψ u) 0 J x := by
      intro x hx
      have h := (hderiv x hx).sub ((hψderiv x).hasDerivWithinAt (s := J))
      rwa [hGg x hx, sub_self] at h
    have hbound := hJconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => φ u - ψ u) (f' := fun _ => (0 : E)) (C := 0) hzero
      (fun x _ => by simp) ht₀J ht
    have hcst : φ t - ψ t = φ t₀ - ψ t₀ := by
      have : ‖(φ t - ψ t) - (φ t₀ - ψ t₀)‖ ≤ 0 := by simpa using hbound
      have := le_antisymm this (norm_nonneg _)
      rwa [norm_eq_zero, sub_eq_zero] at this
    rw [hφ₀, hψt₀, sub_self, sub_eq_zero] at hcst
    rw [hcst, hψeq t ht]
  · intro hint
    have hφψ : ∀ t ∈ J, φ t = ψ t := by
      intro t ht
      rw [hint t ht, hψeq t ht]
    refine ⟨ht₀J, ?_, fun t ht => hgraph t ht, fun t ht => ?_⟩
    · rw [hφψ t₀ ht₀J, hψt₀]
    · have h := ((hψderiv t).hasDerivWithinAt (s := J)).congr
        (fun x hx => hφψ x hx) (hφψ t ht)
      rwa [hGg t ht] at h
