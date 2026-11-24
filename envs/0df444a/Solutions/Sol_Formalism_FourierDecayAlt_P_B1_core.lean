-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:30:18.465649+00:00
-- url     : https://prove2.me/submissions/49c02d4e-bca7-4e87-84e7-f0c2c311c362

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution (hsemi : SeminormIneq) (hpol : Polarisation) : FormCoreC := by
  intro V _ _ W β βi hβ hβi hnn hle hW
  refine hpol V W β βi hβ hβi ?_
  intro x hx
  obtain ⟨Φ, c, t₀, _h0, hc0, hcc, hlim, U, hU, hae⟩ := hW x hx
  have hsq : ∀ t, (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2 ≤
      (βi (Φ t - x) (Φ t - x)).re :=
    fun t => (hsemi V β hβ hnn (Φ t) x).trans (hle _)
  have hT1 : Tendsto (fun t => (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2)
      (𝓝 t₀) (𝓝 0) :=
    squeeze_zero (fun t => sq_nonneg _) hsq hlim
  have hT2 : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re) (𝓝 t₀)
      (𝓝 (Real.sqrt (β x x).re)) := by
    have h' : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) (𝓝 t₀)
        (𝓝 0) := by
      have h2 := hT1.sqrt
      rw [Real.sqrt_zero] at h2
      simp only [Real.sqrt_sq_eq_abs] at h2
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h2
    simpa using h'.add_const (Real.sqrt (β x x).re)
  have e : ∀ t, Real.sqrt (β (Φ t) (Φ t)).re ^ 2 = (β (Φ t) (Φ t)).re :=
    fun t => Real.sq_sqrt (hnn _).2
  have hT3 : Tendsto (fun t => (β (Φ t) (Φ t)).re) (𝓝 t₀) (𝓝 (β x x).re) := by
    simpa only [e, Real.sq_sqrt (hnn x).2] using hT2.pow 2
  have hNe : (ae (volume.restrict U) ⊓ 𝓝 t₀).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s₁ hs₁ s₂ hs₂
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hO : t₀ ∈ interior (s₂ ∩ U) := mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ hU)
    have hpos : 0 < volume (interior (s₂ ∩ U)) := isOpen_interior.measure_pos volume ⟨t₀, hO⟩
    have hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ := by
      intro t ht hts
      have hmem : t ∈ s₁ ∩ s₂ := ⟨hts, (interior_subset ht).1⟩
      rw [hemp] at hmem
      exact hmem
    have h0' : volume.restrict U s₁ᶜ = 0 := mem_ae_iff.mp hs₁
    have hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ := measure_mono hsub
    rw [h0', Measure.restrict_apply isOpen_interior.measurableSet,
      Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)] at hle2
    exact lt_irrefl _ (hpos.trans_le hle2)
  have hcL : Tendsto c (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x)) := by
    rw [← hc0]
    exact hcc.tendsto.mono_left inf_le_right
  have hbL : Tendsto (fun t => β (Φ t) (Φ t)) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x)) :=
    hcL.congr' ((Filter.Eventually.filter_mono inf_le_left hae).mono fun t ht => ht.symm)
  have hre : (β x x).re = (βi x x).re :=
    tendsto_nhds_unique (hT3.mono_left inf_le_right) ((Complex.continuous_re.tendsto _).comp hbL)
  have him : (0 : ℝ) = (βi x x).im := by
    have e2 : (fun t => (β (Φ t) (Φ t)).im) = fun _ => (0 : ℝ) := funext fun t => (hnn (Φ t)).1
    have h1 : Tendsto (fun t => (β (Φ t) (Φ t)).im) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 0) := by
      rw [e2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 ((Complex.continuous_im.tendsto _).comp hbL)
  exact Complex.ext hre (by rw [(hnn x).1, ← him])
end Formalism.FourierDecayAlt.P.B1
