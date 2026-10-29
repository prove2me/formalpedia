-- Prove2me | solution 1 for AvramDividend.Classical.levy_linear_drift_shift_exists_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:26:54.789596+00:00
-- url     : https://prove2.me/submissions/538364de-8987-4cc5-a0ad-e6be17d93d45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      (∀ (t : ℝ≥0) (ω : Ω),
        Y.X t ω = X.X t ω - C * (t : ℝ)) ∧
      (∀ θ : ℝ, Y.ψ θ = X.ψ θ - C * θ) := by
  have hpsi : ∀ θ : ℝ, laplaceExponent (X.c - C) X.σ X.ν θ = laplaceExponent X.c X.σ X.ν θ - C * θ := by
    intro θ; unfold laplaceExponent; ring
  have hcont : Continuous (fun s : ℝ≥0 => C * (s : ℝ)) := continuous_const.mul NNReal.continuous_coe
  refine ⟨{  X := fun t ω => X.X t ω - C * (t : ℝ)
             c := X.c - C
             σ := X.σ
             ν := X.ν
             isProbability := X.isProbability
             σ_nonneg := X.σ_nonneg
             ν_Ici := X.ν_Ici
             ν_integrable := X.ν_integrable
             X_zero := fun ω => by simp [X.X_zero ω]
             rightCont := fun ω t => (X.rightCont ω t).sub hcont.continuousWithinAt
             leftLim := fun ω t ht => by
               obtain ⟨l, hl⟩ := X.leftLim ω t ht
               exact ⟨l - C * (t : ℝ), hl.sub ((hcont.tendsto t).mono_left nhdsWithin_le_nhds)⟩
             noPosJumps := fun ω t l ht hl => by
               have h2 : Tendsto (fun s => X.X s ω) (𝓝[<] t) (𝓝 (l + C * (t : ℝ))) := by
                 have := hl.add ((hcont.tendsto t).mono_left nhdsWithin_le_nhds)
                 simpa using this
               have := X.noPosJumps ω t _ ht h2
               linarith
             adapted := fun t => (X.adapted t).sub measurable_const
             indepIncrements := fun s t hst => by
               refine indep_of_indep_of_le_left (X.indepIncrements s t hst) ?_
               have hm : Measurable[MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance]
                   (fun ω => (X.X t ω - X.X s ω) - C * ((t : ℝ) - s)) :=
                 (comap_measurable _).sub_const _
               have he : (fun ω => (X.X t ω - C * (t : ℝ)) - (X.X s ω - C * (s : ℝ))) =
                   (fun ω => (X.X t ω - X.X s ω) - C * ((t : ℝ) - s)) := by funext ω; ring
               rw [he]
               exact hm.comap_le
             stationaryIncrements := fun s t hst => by
               have h := (X.stationaryIncrements s t hst).comp (measurable_id.sub_const (C * ((t : ℝ) - s)))
               have e1 : (fun ω => (X.X t ω - C * (t : ℝ)) - (X.X s ω - C * (s : ℝ))) =
                   (fun x => id x - C * ((t : ℝ) - s)) ∘ (fun ω => X.X t ω - X.X s ω) := by
                 funext ω; simp only [Function.comp, id]; ring
               have e2 : (fun ω => X.X (t - s) ω - C * ((t - s : ℝ≥0) : ℝ)) =
                   (fun x => id x - C * ((t : ℝ) - s)) ∘ (X.X (t - s)) := by
                 funext ω; simp only [Function.comp, id, NNReal.coe_sub hst]
               rw [e1, e2]; exact h
             laplace := fun t θ hθ => by
               obtain ⟨hi, he⟩ := X.laplace t θ hθ
               have hf : (fun ω => Real.exp (θ * (X.X t ω - C * (t : ℝ)))) =
                   fun ω => Real.exp (θ * X.X t ω) * Real.exp (-(θ * C * t)) := by
                 funext ω; rw [← Real.exp_add]; ring_nf
               rw [hf]
               refine ⟨hi.mul_const _, ?_⟩
               rw [integral_mul_const, he, ← Real.exp_add, hpsi]
               ring_nf }, fun t ω => rfl, fun θ => ?_⟩
  show laplaceExponent (X.c - C) X.σ X.ν θ = laplaceExponent X.c X.σ X.ν θ - C * θ
  exact hpsi θ
