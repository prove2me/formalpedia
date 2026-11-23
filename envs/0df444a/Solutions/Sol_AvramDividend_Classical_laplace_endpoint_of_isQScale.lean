-- Prove2me | solution 1 for AvramDividend.Classical.laplace_endpoint_of_isQScale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:25:13.249372+00:00
-- url     : https://prove2.me/submissions/2e3ffca9-f066-44f3-aaac-444e5f342554

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_laplace_scaled_integral_tendsto
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open Kyprianou.Ch08.StageB

private theorem endpoint_impl
    (ψ W : ℝ → ℝ) (β₀ L : ℝ)
    (hβ₀ : 0 < β₀) (hroot : Kyprianou.Ch08.Phi ψ 0 < β₀) (hL : L ≠ 0)
    (hs : Kyprianou.Ch08.IsQScale ψ 0 W)
    (hlim : Tendsto (fun β : ℝ => β * (ψ β)⁻¹) atTop (𝓝 L)) :
    W 0 = L := by
  classical
  let s : ℝ → ℝ := W
  have hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ s x := by
    intro x hx
    simpa [s] using hs.2.2.1 x
  have hcont : ContinuousOn s (Ici (0 : ℝ)) := hs.2.2.2.1
  have hmono : MonotoneOn s (Ici (0 : ℝ)) := hs.2.2.2.2.1
  have hlap : ∀ β : ℝ, 0 ≤ β → Kyprianou.Ch08.Phi ψ 0 < β →
      IntegrableOn (fun x : ℝ => Real.exp (-β * x) * s x) (Ioi 0) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * s x ∂volume) = (ψ β)⁻¹ := by
    intro β hβ hΦβ
    simpa [s] using hs.2.2.2.2.2 β hβ hΦβ
  have endpoint : s 0 = L := by
    let βstar : ℝ := max β₀ (Kyprianou.Ch08.Phi ψ 0) + 1
    have hLpos : 0 < βstar := by
      dsimp [βstar]
      have := le_max_left β₀ (Kyprianou.Ch08.Phi ψ 0)
      linarith
    have hLmax : Kyprianou.Ch08.Phi ψ 0 < βstar := by
      dsimp [βstar]
      linarith [le_max_right β₀ (Kyprianou.Ch08.Phi ψ 0)]
    have hIL := hlap βstar hLpos.le hLmax
    have hDCT := AvramDividend.Classical.laplace_scaled_integral_tendsto
      s βstar hLpos hnonneg hcont hmono hIL.1
    have hscale : ∀ β : ℝ, 0 < β →
        β * (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x)) * s x) =
          ∫ u in Ioi (0 : ℝ), Real.exp (-u) * s (u / β) := by
      intro β hβ
      have hcv := MeasureTheory.integral_comp_mul_left_Ioi
        (g := fun u : ℝ => Real.exp (-u) * s (u / β)) (0 : ℝ) hβ
      have hcv' : (∫ u in Ioi (0 : ℝ), Real.exp (-(β * u)) * s u) =
          β⁻¹ * (∫ u in Ioi (0 : ℝ), Real.exp (-u) * s (u / β)) := by
        calc
          (∫ u in Ioi (0 : ℝ), Real.exp (-(β * u)) * s u)
              = ∫ u in Ioi (0 : ℝ), Real.exp (-(β * u)) * s (β * u / β) := by
                  apply setIntegral_congr_fun measurableSet_Ioi
                  intro u hu
                  have hu_eq : β * u / β = u := by field_simp [hβ.ne']
                  change Real.exp (-(β * u)) * s u = Real.exp (-(β * u)) * s (β * u / β)
                  simpa [hu_eq]
          _ = β⁻¹ • ∫ u in Ioi (β * 0), Real.exp (-u) * s (u / β) := hcv
          _ = β⁻¹ * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * s (u / β) := by
              simp [smul_eq_mul]
      rw [hcv']
      field_simp [hβ.ne']
    have hA0 : Tendsto (fun β : ℝ => β * (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x)) * s x))
        atTop (𝓝 (s 0)) := by
      have heq : (fun β : ℝ => ∫ u in Ioi (0 : ℝ), Real.exp (-u) * s (u / β)) =ᶠ[atTop]
          (fun β : ℝ => β * (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x)) * s x)) := by
        filter_upwards [eventually_ge_atTop βstar] with β hβ
        exact (hscale β (hLpos.trans_le hβ)).symm
      exact Tendsto.congr' heq hDCT
    have hψeq : (fun β : ℝ => β * (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x)) * s x)) =ᶠ[atTop]
        (fun β : ℝ => β * (ψ β)⁻¹) := by
      filter_upwards [eventually_ge_atTop βstar] with β hβ
      have hβpos : 0 < β := hLpos.trans_le hβ
      have hβΦ : Kyprianou.Ch08.Phi ψ 0 < β := lt_of_lt_of_le hLmax hβ
      have hint : (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x)) * s x) = (ψ β)⁻¹ := by
        simpa [neg_mul] using (hlap β hβpos.le hβΦ).2
      rw [hint]
    have hAψ : Tendsto (fun β : ℝ => β * (ψ β)⁻¹) atTop (𝓝 (s 0)) :=
      Tendsto.congr' hψeq hA0
    exact tendsto_nhds_unique hAψ hlim
  simpa [s] using endpoint

theorem solution
    (ψ W : ℝ → ℝ) (β₀ L : ℝ)
    (hβ₀ : 0 < β₀) (hroot : Kyprianou.Ch08.Phi ψ 0 < β₀) (hL : L ≠ 0)
    (hs : Kyprianou.Ch08.IsQScale ψ 0 W)
    (hlim : Tendsto (fun β : ℝ => β * (ψ β)⁻¹) atTop (𝓝 L)) :
    W 0 = L := by
  exact endpoint_impl ψ W β₀ L hβ₀ hroot hL hs hlim
