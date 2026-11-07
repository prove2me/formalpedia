-- Prove2me | solution 1 for DuffieHedge.Optimal.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:00:46.507787+00:00
-- url     : https://prove2.me/submissions/a03ca180-4793-498f-b9e9-b19342a68d79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic
import Theorems.Thm_DuffieHedge_Optimal_mean_ZG
import Theorems.Thm_DuffieHedge_Optimal_mean_GstarG
import Theorems.Thm_DuffieHedge_Optimal_mean_G
import Theorems.Thm_DuffieHedge_Optimal_F_pos

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : DuffieHedge.Optimal.Market Ω)
    (hM : M.Standing)
    (k L : ℝ) (Gs : ℝ≥0 → Ω → ℝ) (hGs : M.SolvesEq10 k L Gs)
    (θ G : ℝ≥0 → Ω → ℝ) (hθ : M.IsTradingStrategy θ) (hG : M.IsGain θ G)
    (H : ℝ≥0 → ℝ) (hH : ∀ t, H t = ∫ ω, (L - M.Z k t ω - Gs t ω) * G t ω ∂M.P) :
    (∀ t ≤ M.T, Integrable (fun ω => (L - M.Z k t ω - Gs t ω) * G t ω) M.P) ∧
    IntegrableOn (fun s : ℝ => M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal)
      (Set.Icc (0 : ℝ) M.T) ∧
    ∀ t ≤ M.T, H t = H 0 - ∫ s in Set.Icc (0 : ℝ) t,
        M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal := by
  obtain ⟨Gb, hGb⟩ : ∃ Gb : ℝ≥0 → ℝ, ∀ t, Gb t = ∫ ω, G t ω ∂M.P := ⟨_, fun _ => rfl⟩
  obtain ⟨Xb, hXb⟩ : ∃ Xb : ℝ≥0 → ℝ, ∀ t, Xb t = ∫ ω, M.Z k t ω * G t ω ∂M.P :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Yb, hYb⟩ : ∃ Yb : ℝ≥0 → ℝ, ∀ t, Yb t = ∫ ω, Gs t ω * G t ω ∂M.P :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hG1, hG2, hG3, hG4⟩ := DuffieHedge.Optimal.mean_G M hM θ G hθ hG Gb hGb
  obtain ⟨hX1, hX2, hX3, hX4⟩ := DuffieHedge.Optimal.mean_ZG M hM k θ G hθ hG Xb hXb
  obtain ⟨hY1, hY2, hY3, hY4⟩ :=
    DuffieHedge.Optimal.mean_GstarG M hM k L Gs hGs θ G hθ hG Yb hYb
  have hFpos := DuffieHedge.Optimal.F_pos M hM
  obtain ⟨_, hT0', _, _, _, _, _, _, ⟨δ, hδ, hδv⟩, _⟩ := hM
  have hT0 : (0 : ℝ) ≤ M.T := M.T.2
  -- Part 1
  have hint : ∀ t ≤ M.T, Integrable (fun ω => (L - M.Z k t ω - Gs t ω) * G t ω) M.P := by
    intro t ht
    have := (((hG1 t ht).const_mul L).sub (hX1 t ht)).sub (hY1 t ht)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]; ring
  have hHdec : ∀ t ≤ M.T, H t = L * Gb t - Xb t - Yb t := by
    intro t ht
    have e : (fun ω => (L - M.Z k t ω - Gs t ω) * G t ω)
        = fun ω => (L * G t ω - M.Z k t ω * G t ω) - Gs t ω * G t ω := by
      funext ω; ring
    have i1 : Integrable (fun ω => L * G t ω) M.P := (hG1 t ht).const_mul L
    have i2 : Integrable (fun ω => L * G t ω - M.Z k t ω * G t ω) M.P := i1.sub (hX1 t ht)
    rw [hH, e, integral_sub i2 (hY1 t ht), integral_sub i1 (hX1 t ht), integral_const_mul,
      hGb, hXb, hYb]
  -- the combined drift
  set D : ℝ → ℝ := fun s =>
    L * (M.m s.toNNReal * ∫ ω, θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P)
    - ((M.γ s.toNNReal + M.μ s.toNNReal) * Xb s.toNNReal
        + M.m s.toNNReal *
            ∫ ω, M.Z k s.toNNReal ω * θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P
        + M.σ s.toNNReal * M.v s.toNNReal * M.ρ s.toNNReal *
            ∫ ω, M.Z k s.toNNReal ω * θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P)
    - (M.m s.toNNReal * ∫ ω, M.feedback k L Gs s.toNNReal ω * M.F s.toNNReal ω
          * G s.toNNReal ω ∂M.P
        + M.m s.toNNReal * ∫ ω, θ s.toNNReal ω * M.F s.toNNReal ω * Gs s.toNNReal ω ∂M.P
        + M.v s.toNNReal ^ 2 * ∫ ω, M.feedback k L Gs s.toNNReal ω * θ s.toNNReal ω
          * M.F s.toNNReal ω ^ 2 ∂M.P) with hD
  have hDint : IntegrableOn D (Icc (0 : ℝ) M.T) := ((hG3.const_mul L).sub hX3).sub hY3
  have hDeq : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) M.T)),
      D s = -(M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hG2, hX2, hY2] with s hs hg hx hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    set τ := s.toNNReal with hτ
    have hτT : τ ≤ M.T := by rw [hτ, Real.toNNReal_le_iff_le_coe]; exact hs.2
    have hv : M.v τ ≠ 0 := by
      intro h0; have := hδv τ hτT; rw [h0, abs_zero] at this; linarith
    set A : ℝ := M.m τ / M.v τ ^ 2 with hA
    set Bc : ℝ := M.σ τ * M.ρ τ / M.v τ with hBc
    -- r
    have hr : ∫ ω, M.feedback k L Gs τ ω * θ τ ω * M.F τ ω ^ 2 ∂M.P
        = A * (L * (∫ ω, θ τ ω * M.F τ ω ∂M.P)
            - (∫ ω, M.Z k τ ω * θ τ ω * M.F τ ω ∂M.P)
            - (∫ ω, θ τ ω * M.F τ ω * Gs τ ω ∂M.P))
          - Bc * ∫ ω, M.Z k τ ω * θ τ ω * M.F τ ω ∂M.P := by
      have hpt : (fun ω => M.feedback k L Gs τ ω * θ τ ω * M.F τ ω ^ 2)
          = fun ω => A * (L * (θ τ ω * M.F τ ω) - M.Z k τ ω * θ τ ω * M.F τ ω
              - θ τ ω * M.F τ ω * Gs τ ω) - Bc * (M.Z k τ ω * θ τ ω * M.F τ ω) := by
        funext ω
        simp only [DuffieHedge.Optimal.Market.feedback, DuffieHedge.Optimal.Market.Φ, hA, hBc]
        by_cases hF : M.F τ ω = 0
        · simp [hF]
        · field_simp
      rw [hpt, integral_sub, integral_const_mul, integral_const_mul, integral_sub, integral_sub,
        integral_const_mul]
      · exact hg.const_mul L
      · exact hx
      · exact (hg.const_mul L).sub hx
      · exact hy2
      · exact (((hg.const_mul L).sub hx).sub hy2).const_mul A
      · exact hx.const_mul Bc
    -- p
    have hp : ∫ ω, M.feedback k L Gs τ ω * M.F τ ω * G τ ω ∂M.P
        = A * (L * Gb τ - Xb τ - Yb τ) - Bc * Xb τ := by
      have hpt : (fun ω => M.feedback k L Gs τ ω * M.F τ ω * G τ ω)
          =ᵐ[M.P] fun ω => A * (L * G τ ω - M.Z k τ ω * G τ ω - Gs τ ω * G τ ω)
              - Bc * (M.Z k τ ω * G τ ω) := by
        filter_upwards [hFpos τ hτT] with ω hF
        simp only [DuffieHedge.Optimal.Market.feedback, DuffieHedge.Optimal.Market.Φ, hA, hBc]
        field_simp
      rw [integral_congr_ae hpt, integral_sub, integral_const_mul, integral_const_mul,
        integral_sub, integral_sub, integral_const_mul, hGb, hXb, hYb]
      · exact (hG1 τ hτT).const_mul L
      · exact hX1 τ hτT
      · exact ((hG1 τ hτT).const_mul L).sub (hX1 τ hτT)
      · exact hY1 τ hτT
      · exact ((((hG1 τ hτT).const_mul L).sub (hX1 τ hτT)).sub (hY1 τ hτT)).const_mul A
      · exact (hX1 τ hτT).const_mul Bc
    simp only [hD]
    rw [← hτ, hr, hp, hHdec τ hτT]
    simp only [DuffieHedge.Optimal.Market.γ, hA, hBc]
    field_simp
    ring
  have hcHint : IntegrableOn (fun s : ℝ => M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal)
      (Icc (0 : ℝ) M.T) := by
    have := hDint.neg
    refine this.congr_fun_ae ?_
    filter_upwards [hDeq] with s hs
    simp [hs]
  refine ⟨hint, hcHint, ?_⟩
  intro t ht
  have htT : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) M.T := Icc_subset_Icc_right (by exact_mod_cast ht)
  have hDeq' : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) t)),
      D s = -(M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal) :=
    ae_restrict_of_ae_restrict_of_subset htT hDeq
  have hIntD : ∫ s in Icc (0 : ℝ) t, D s
      = -∫ s in Icc (0 : ℝ) t, M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal := by
    rw [← integral_neg]; exact integral_congr_ae hDeq'
  have hsplit : ∫ s in Icc (0 : ℝ) t, D s
      = L * (Gb t - Gb 0) - (Xb t - Xb 0) - (Yb t - Yb 0) := by
    rw [hG4 t ht, hX4 t ht, hY4 t ht]
    simp only [hD, add_sub_cancel_left]
    rw [integral_sub, integral_sub, integral_const_mul]
    · exact (hG3.mono_set htT).const_mul L
    · exact hX3.mono_set htT
    · exact ((hG3.mono_set htT).const_mul L).sub (hX3.mono_set htT)
    · exact hY3.mono_set htT
  rw [hHdec t ht, hHdec 0 (by simp)]
  linarith [hIntD, hsplit]
