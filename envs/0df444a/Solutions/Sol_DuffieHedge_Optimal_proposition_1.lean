-- Prove2me | solution 1 for DuffieHedge.Optimal.proposition_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:51:55.562255+00:00
-- url     : https://prove2.me/submissions/640bda22-4616-48b8-87a4-a45e68335be1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic
import Theorems.Thm_DuffieHedge_Optimal_lemma_1
import Theorems.Thm_DuffieHedge_Optimal_lemma_2
import Theorems.Thm_DuffieHedge_Optimal_ode_13_solution

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open DuffieHedge.Optimal in
/-- A futures gain starts at zero almost surely. -/
theorem DuffieProp1_gain_zero_ae {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (θ G : ℝ≥0 → Ω → ℝ) (hG : M.IsGain θ G) : G 0 =ᵐ[M.P] 0 := by
  obtain ⟨_, _, J, hJ, hx⟩ := hG
  have hJ0 : ∀ i j, J i j 0 =ᵐ[M.P] 0 := by
    intro i j
    obtain ⟨_, hadapt, Hs, _, hlim⟩ := hJ i j
    have h0 := hlim 0 (by simp)
    have hconst : ∀ m, (∫⁻ ω, ‖(Hs m).integral (fun s ω => M.BE s ω j) 0 ω - J i j 0 ω‖ₑ ^ 2
        ∂M.P) = ∫⁻ ω, ‖J i j 0 ω‖ₑ ^ 2 ∂M.P := by
      intro m
      congr 1
      funext ω
      simp [Peng1990.SMP.SimpleIntegrand.integral]
    simp only [hconst, tendsto_const_nhds_iff] at h0
    have hmeas : StronglyMeasurable (J i j 0) := (hadapt 0).mono (M.filt.le 0)
    have := (lintegral_eq_zero_iff' (hmeas.measurable.enorm.pow_const 2).aemeasurable).1 h0
    filter_upwards [this] with ω hω
    simpa using hω
  have hall : ∀ᵐ ω ∂M.P, ∀ i j, J i j 0 ω = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact hJ0 i j
  filter_upwards [hx 0 (by simp), hall] with ω hω hJω
  have h := hω.2 ()
  simp only [Pi.zero_apply]
  rw [h]
  simp [hJω]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : DuffieHedge.Optimal.Market Ω)
    (hM : M.Standing)
    (k L : ℝ) (Gs : ℝ≥0 → Ω → ℝ) (hGs : M.SolvesEq10 k L Gs) :
    M.SolvesP3 k L (M.feedback k L Gs) := by
  rw [DuffieHedge.Optimal.lemma_1 M hM k L (M.feedback k L Gs) Gs hGs.1 hGs.2]
  intro θ hθ G hG
  set H : ℝ≥0 → ℝ := fun t => ∫ ω, (L - M.Z k t ω - Gs t ω) * G t ω ∂M.P with hHdef
  obtain ⟨hint, hintH, hode⟩ :=
    DuffieHedge.Optimal.lemma_2 M hM k L Gs hGs θ G hθ hG H (fun t => rfl)
  obtain ⟨_, _, _, _, hmm, hvm, _, hbd, hv0, _⟩ := hM
  have hbd' : ∃ K : ℝ, ∀ t ≤ M.T, |M.m t| ≤ K ∧ |M.v t| ≤ K := by
    obtain ⟨K, hK⟩ := hbd
    exact ⟨K, fun t ht => ⟨(hK t ht).2.2.1, (hK t ht).2.2.2.1⟩⟩
  have hsol := DuffieHedge.Optimal.ode_13_solution M.T M.m M.v hmm hvm hbd' hv0 H hintH hode
  have hH0 : H 0 = 0 := by
    simp only [hHdef]
    have := DuffieProp1_gain_zero_ae M θ G hG
    rw [integral_congr_ae (g := fun _ => (0:ℝ))]
    · simp
    · filter_upwards [this] with ω hω
      simp [hω]
  have hHT : H M.T = 0 := by
    rw [hsol M.T le_rfl, hH0, zero_mul]
  have hZT : ∀ ω, M.Z k M.T ω = k * M.S M.T ω := by
    intro ω
    simp [DuffieHedge.Optimal.Market.Z]
  have hfun : (fun ω => (L - k * M.S M.T ω - Gs M.T ω) * G M.T ω)
      = (fun ω => (L - M.Z k M.T ω - Gs M.T ω) * G M.T ω) := by
    funext ω; rw [hZT]
  rw [hfun]
  exact ⟨hint M.T le_rfl, hHT⟩
