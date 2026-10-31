-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_le_mul_norm_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T09:35:05.436581+00:00
-- url     : https://prove2.me/submissions/2de0b76a-0f1d-4c6c-859d-c4442772c1db

import Mathlib



namespace FiniteEnergyPlane

open Metric

theorem exists_norm_le_mul_norm_of_periodic_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (φ : ℝ) (v : E), ‖v‖ ≤ r / 2 → ‖Φ (φ, v)‖ ≤ L * ‖v‖ := by
  have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ ball (0 : E) r) := isOpen_univ.prod isOpen_ball
  have hcont : ContinuousOn (fderiv ℝ Φ) (Set.univ ×ˢ ball (0 : E) r) :=
    hΦ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hK : IsCompact (Set.Icc 0 T ×ˢ closedBall (0 : E) (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKU : Set.Icc 0 T ×ˢ closedBall (0 : E) (r / 2) ⊆ Set.univ ×ˢ ball (0 : E) r :=
    Set.prod_mono (Set.subset_univ _) (closedBall_subset_ball (by linarith))
  obtain ⟨L₀, hL₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  refine ⟨max L₀ 0, le_max_right _ _, fun φ v hv => ?_⟩
  have hvr : ‖v‖ < r := by linarith
  have hpf : Function.Periodic (fun ψ => Φ (ψ, v)) T := fun ψ => hper ψ v hvr
  obtain ⟨φ', hφ', hfφ⟩ := hpf.exists_mem_Ico₀ hT φ
  rw [show Φ (φ, v) = Φ (φ', v) from hfφ]
  set s := ({φ'} : Set ℝ) ×ˢ closedBall (0 : E) (r / 2) with hs
  have hsK : s ⊆ Set.Icc 0 T ×ˢ closedBall (0 : E) (r / 2) :=
    Set.prod_mono (Set.singleton_subset_iff.2 (Set.Ico_subset_Icc_self hφ')) le_rfl
  have hdiff : ∀ q ∈ s, DifferentiableAt ℝ Φ q := fun q hq =>
    ((hΦ.differentiableOn (by simp)) q (hKU (hsK hq))).differentiableAt
      (hU.mem_nhds (hKU (hsK hq)))
  have hbound : ∀ q ∈ s, ‖fderiv ℝ Φ q‖ ≤ max L₀ 0 := fun q hq =>
    (hL₀ q (hsK hq)).trans (le_max_left _ _)
  have hconv : Convex ℝ s := (convex_singleton _).prod (convex_closedBall _ _)
  have hx : ((φ', (0 : E)) : ℝ × E) ∈ s := ⟨rfl, by simp; linarith⟩
  have hy : ((φ', v) : ℝ × E) ∈ s := ⟨rfl, by simpa using hv⟩
  have key := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hx hy
  rw [h0, sub_zero] at key
  have hn : ‖((φ', v) : ℝ × E) - (φ', 0)‖ = ‖v‖ := by simp [Prod.norm_def]
  rwa [hn] at key

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (φ : ℝ) (v : E), ‖v‖ ≤ r / 2 → ‖Φ (φ, v)‖ ≤ L * ‖v‖ :=
  exists_norm_le_mul_norm_of_periodic_aux Φ T r hT hr hΦ hper h0
