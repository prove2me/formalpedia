-- Prove2me | solution 1 for DRUQChance.Markov.theorem_7_if
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:57:26.028465+00:00
-- url     : https://prove2.me/submissions/7e2d844f-13a3-4416-ba70-f12f6873a5df

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

open MeasureTheory Matrix DRConvexOpt.Reform DRUQChance.Markov

theorem solution {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0)) (s : Fin nP → ℝ) (t ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (β : ℝ) (γ : Fin nK → ℝ) (φ ψ : Fin (amb.L 0) → ℝ) (τ : ℝ)
    (h26 : System26 amb s t ε β γ φ ψ τ) :
    ∀ μ ∈ paperAmbiguitySet amb, 1 - ε ≤ μ.real {ω | s ⬝ᵥ ω.1 ≤ t} := by
  intro μ hμ
  obtain ⟨hφ, hψ, hτ, h1, h2, h3, h4, h5, h6, h7⟩ := h26
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
  have hEclosed : IsClosed {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | s ⬝ᵥ ω.1 ≤ t} :=
    isClosed_le (Continuous.dotProduct continuous_const continuous_fst) continuous_const
  have hEmeas := hEclosed.measurableSet
  have hCc : μ (amb.conf 0)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hCmeas, ← ofReal_measureReal (measure_ne_top _ _), hC1,
      ENNReal.ofReal_one]
  have hae : ∀ᵐ ω ∂μ, ω ∈ amb.conf 0 := mem_ae_iff.mpr hCc
  -- the linear functional
  set L : (Fin nK → ℝ) →L[ℝ] ℝ := ∑ i, γ i • ContinuousLinearMap.proj i with hL
  have hLapply : ∀ v, L v = γ ⬝ᵥ v := by
    intro v; simp [hL, dotProduct]
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
  have hφpt : ∀ ω ∈ amb.conf 0, F ω ≤ τ := by
    intro ω hω
    have e := key φ 0 (by simpa using h4) h5 ω
    have := bound φ hφ ω hω
    rw [zero_dotProduct, add_zero] at e
    simp only [hF]; linarith
  have hψpt : ∀ ω ∈ amb.conf 0, F ω + s ⬝ᵥ ω.1 ≤ t := by
    intro ω hω
    have e := key ψ s h6 h7 ω
    have := bound ψ hψ ω hω
    simp only [hF]; linarith
  set E := {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | s ⬝ᵥ ω.1 ≤ t} with hE
  rcases hτ.lt_or_eq with hτpos | hτ0
  · -- τ > 0
    have hmono : ∫ ω, F ω ∂μ ≤ ∫ ω, E.indicator (fun _ => τ) ω ∂μ := by
      apply integral_mono_ae hFint ((integrable_const τ).indicator hEmeas)
      filter_upwards [hae] with ω hω
      by_cases hωE : ω ∈ E
      · rw [Set.indicator_of_mem hωE]; exact hφpt ω hω
      · rw [Set.indicator_of_notMem hωE]
        have := hψpt ω hω
        simp only [hE, Set.mem_ofPred_eq, not_le] at hωE
        linarith
    rw [hFintegral, integral_indicator_const _ hEmeas] at hmono
    simp only [smul_eq_mul] at hmono
    have : (1 - ε) * τ ≤ μ.real E * τ := le_trans h1 hmono
    exact le_of_mul_le_mul_right this hτpos
  · -- τ = 0
    subst hτ0
    have hnonpos : ∀ᵐ ω ∂μ, F ω ≤ 0 := by
      filter_upwards [hae] with ω hω; exact hφpt ω hω
    have hI0 : ∫ ω, F ω ∂μ = 0 := le_antisymm (integral_nonpos_of_ae hnonpos)
      (by rw [hFintegral]; linarith)
    have hz : (fun ω => -F ω) =ᵐ[μ] 0 := by
      have h' : ∫ ω, -F ω ∂μ = 0 := by rw [integral_neg, hI0, neg_zero]
      exact (integral_eq_zero_iff_of_nonneg_ae
        (by filter_upwards [hnonpos] with ω hω; simp; linarith) hFint.neg).mp h'
    have hEc : μ Eᶜ = 0 := by
      have : ∀ᵐ ω ∂μ, ω ∈ E := by
        filter_upwards [hae, hz] with ω hω hzω
        simp only [Pi.zero_apply, neg_eq_zero] at hzω
        have := hψpt ω hω
        simp only [hE, Set.mem_ofPred_eq]; linarith
      exact mem_ae_iff.mp this
    have : μ.real E = 1 := by
      rw [measureReal_def, prob_compl_eq_zero_iff hEmeas |>.mp hEc]; simp
    rw [this]; linarith
