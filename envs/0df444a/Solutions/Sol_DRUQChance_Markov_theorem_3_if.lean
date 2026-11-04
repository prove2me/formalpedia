-- Prove2me | solution 1 for DRUQChance.Markov.theorem_3_if
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:58:17.975782+00:00
-- url     : https://prove2.me/submissions/5e512a3c-20e5-4331-a1ee-e4e9acd5df92

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

open MeasureTheory Matrix DRConvexOpt.Reform DRUQChance.Markov

theorem solution {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0)) (S : Matrix (Fin nJ) (Fin nP) ℝ) (t : Fin nJ → ℝ)
    (γ : Fin nK → ℝ) (lam kap : ℝ) (φ : Fin (amb.L 0) → ℝ) (τ : Fin nJ → ℝ)
    (ψ : Fin nJ → Fin (amb.L 0) → ℝ) (hfeas : UQFeasible amb S t γ lam kap φ τ ψ)
    (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) (hμ : μ ∈ paperAmbiguitySet amb) :
    uqObjective amb γ lam kap ≤ μ.real {ω | S *ᵥ ω.1 ≤ t} := by
  obtain ⟨hlam, hkap, hφ, h2, h4, h5, hL⟩ := hfeas
  set β := lam - kap with hβ
  obtain ⟨hP, hint, hmean, hconf⟩ := hμ
  have hC1 : μ.real (amb.conf 0) = 1 := by
    have := hconf 0
    rw [hM.1, hM.2] at this
    exact le_antisymm this.2 this.1
  -- measurability
  have hcont : Continuous (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
      amb.c 0 - (amb.C 0 *ᵥ ω.1 + amb.D 0 *ᵥ ω.2)) := by
    apply Continuous.sub continuous_const
    apply Continuous.add
    · exact (Continuous.matrix_mulVec continuous_const continuous_fst)
    · exact (Continuous.matrix_mulVec continuous_const continuous_snd)
  have hCclosed : IsClosed (amb.conf 0) := hK.1.preimage hcont
  have hCmeas : MeasurableSet (amb.conf 0) := hCclosed.measurableSet
  have hEclosed : IsClosed {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | S *ᵥ ω.1 ≤ t} :=
    isClosed_le (Continuous.matrix_mulVec continuous_const continuous_fst) continuous_const
  have hEmeas := hEclosed.measurableSet
  have hCc : μ (amb.conf 0)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hCmeas, ← ofReal_measureReal (measure_ne_top _ _), hC1,
      ENNReal.ofReal_one]
  have hae : ∀ᵐ ω ∂μ, ω ∈ amb.conf 0 := mem_ae_iff.mpr hCc
  -- the linear functional
  set L : (Fin nK → ℝ) →L[ℝ] ℝ := ∑ i, γ i • ContinuousLinearMap.proj i with hLdef
  have hLapply : ∀ v, L v = γ ⬝ᵥ v := by
    intro v; simp [hLdef, dotProduct]
  set g : (Fin nP → ℝ) × (Fin nQ → ℝ) → (Fin nK → ℝ) := fun ω => amb.A *ᵥ ω.1 + amb.B *ᵥ ω.2
  set F : (Fin nP → ℝ) × (Fin nQ → ℝ) → ℝ := fun ω => γ ⬝ᵥ g ω + β with hF
  have hFint : Integrable F μ := by
    have : Integrable (fun ω => L (g ω)) μ := L.integrable_comp hint
    simp only [hLapply] at this
    exact this.add (integrable_const β)
  have hFintegral : ∫ ω, F ω ∂μ = β + amb.b ⬝ᵥ γ := by
    rw [hF, integral_add _ (integrable_const β)]
    · have : ∫ ω, γ ⬝ᵥ g ω ∂μ = γ ⬝ᵥ ∫ ω, g ω ∂μ := by
        simp only [← hLapply]; exact L.integral_comp_comm hint
      rw [this, hmean]; simp [dotProduct_comm]; ring
    · have : Integrable (fun ω => L (g ω)) μ := L.integrable_comp hint
      simpa only [hLapply] using this
  -- key pointwise identity
  have key : ∀ (θ : Fin (amb.L 0) → ℝ) (w : Fin nP → ℝ),
      amb.Aᵀ *ᵥ γ + w = (amb.C 0)ᵀ *ᵥ θ → amb.Bᵀ *ᵥ γ = (amb.D 0)ᵀ *ᵥ θ →
      ∀ ω : (Fin nP → ℝ) × (Fin nQ → ℝ),
        γ ⬝ᵥ g ω + w ⬝ᵥ ω.1 = θ ⬝ᵥ (amb.C 0 *ᵥ ω.1 + amb.D 0 *ᵥ ω.2) := by
    intro θ w hA hB ω
    simp only [g, dotProduct_add, dotProduct_mulVec]
    rw [← mulVec_transpose, ← mulVec_transpose, ← mulVec_transpose, ← mulVec_transpose, ← hB,
      ← hA, add_dotProduct]
    ring
  have bound : ∀ θ ∈ dualCone (amb.K 0), ∀ ω ∈ amb.conf 0,
      θ ⬝ᵥ (amb.C 0 *ᵥ ω.1 + amb.D 0 *ᵥ ω.2) ≤ amb.c 0 ⬝ᵥ θ := by
    intro θ hθ ω hω
    have := hθ _ hω
    rw [sub_dotProduct] at this
    rw [dotProduct_comm θ]; linarith
  have hφpt : ∀ ω ∈ amb.conf 0, F ω ≤ 1 := by
    intro ω hω
    have e := key φ 0 (by simpa using h4) h5 ω
    have := bound φ hφ ω hω
    rw [zero_dotProduct, add_zero] at e
    simp only [hF]; linarith
  have hviol : ∀ ω ∈ amb.conf 0, ∀ j, t j < S j ⬝ᵥ ω.1 → F ω ≤ 0 := by
    intro ω hω j hj
    have hjL : j ∈ violIdx amb S t := by
      simp only [violIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ω, hω, hj⟩
    obtain ⟨hτj, hψj, h3, h6, h7⟩ := hL j hjL
    have e := key (ψ j) (τ j • S j) h6 h7 ω
    have := bound (ψ j) hψj ω hω
    rw [smul_dotProduct, smul_eq_mul] at e
    have : τ j * (t j - S j ⬝ᵥ ω.1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hτj (by linarith)
    simp only [hF]; nlinarith
  set E := {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | S *ᵥ ω.1 ≤ t} with hE
  have hmono : ∫ ω, F ω ∂μ ≤ ∫ ω, E.indicator (fun _ => (1:ℝ)) ω ∂μ := by
    apply integral_mono_ae hFint ((integrable_const (1:ℝ)).indicator hEmeas)
    filter_upwards [hae] with ω hω
    by_cases hωE : ω ∈ E
    · rw [Set.indicator_of_mem hωE]; exact hφpt ω hω
    · rw [Set.indicator_of_notMem hωE]
      simp only [hE, Set.mem_ofPred_eq, Pi.le_def, not_forall, not_le] at hωE
      obtain ⟨j, hj⟩ := hωE
      exact hviol ω hω j (by simpa [mulVec, dotProduct] using hj)
  rw [hFintegral, integral_indicator_const _ hEmeas] at hmono
  simp only [smul_eq_mul, mul_one] at hmono
  simp only [uqObjective, hM.1, hM.2, one_mul]
  linarith
