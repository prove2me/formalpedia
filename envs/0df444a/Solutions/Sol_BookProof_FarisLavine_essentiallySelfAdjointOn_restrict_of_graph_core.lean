-- Prove2me | solution 1 for BookProof.FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:48:40.877372+00:00
-- url     : https://prove2.me/submissions/c349e194-b973-487f-94f3-07413d640795

-- Generated from ChapterFarisLavineCore.lean — solution of BookProof.FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution
    {C : Submodule ℂ F} (hCD : C ≤ D) (H : D →ₗ[ℂ] F)
    (hcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖H y - H x‖ < ε)
    (hdef : EssentiallySelfAdjointOn D H) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by

  have main : ∀ σ : ℂ, DeficiencyTrivialAt D H σ →
      DeficiencyTrivialAt C (H.comp (Submodule.inclusion hCD)) σ := by
    intro σ hσ w hw
    refine hσ w fun x => ?_
    have hzero : ∀ ε : ℝ, 0 < ε →
        ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
      intro ε hε
      obtain ⟨y, hyC, hy1, hy2⟩ := hcore x ε hε
      have hwy := hw ⟨(y : F), hyC⟩
      have hHy : (H.comp (Submodule.inclusion hCD)) ⟨(y : F), hyC⟩ = H y := by
        simp only [LinearMap.comp_apply]
        congr 1
      rw [hHy] at hwy
      have hsplit : (inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w
          = (inner ℂ (H x - H y) w : ℂ) + σ * inner ℂ ((y : F) - (x : F)) w := by
        rw [inner_sub_left, inner_sub_left, hwy]
        push_cast
        ring
      calc ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖
          ≤ ‖(inner ℂ (H x - H y) w : ℂ)‖ + ‖σ * (inner ℂ ((y : F) - (x : F)) w : ℂ)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖H x - H y‖ * ‖w‖ + ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) := by
            gcongr
            · exact norm_inner_le_norm _ _
            · rw [norm_mul]
              gcongr
              exact norm_inner_le_norm _ _
        _ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
            have h1 : ‖H x - H y‖ ≤ ε := by
              rw [← norm_neg]; simpa [neg_sub] using hy2.le
            have h2 : ‖(y : F) - (x : F)‖ ≤ ε := hy1.le
            have hA : ‖H x - H y‖ * ‖w‖ ≤ ε * ‖w‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
            have hB : ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) ≤ ‖σ‖ * (ε * ‖w‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg w))
                (norm_nonneg σ)
            have hsum : ε * ‖w‖ + ‖σ‖ * (ε * ‖w‖) = ε * (1 + ‖σ‖) * ‖w‖ := by ring
            linarith
    have hnn : ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hpos : 0 < δ / ((1 + ‖σ‖) * (1 + ‖w‖)) := by positivity
      have := hzero _ hpos
      have hbound : δ / ((1 + ‖σ‖) * (1 + ‖w‖)) * (1 + ‖σ‖) * ‖w‖ ≤ δ := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg w, norm_nonneg σ, hδ.le]
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hnn)
  exact ⟨main _ hdef.1, main _ hdef.2⟩
