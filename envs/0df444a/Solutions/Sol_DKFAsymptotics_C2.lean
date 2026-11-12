-- Prove2me | solution 1 for DKFAsymptotics.C2
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-15T20:58:55.469982+00:00
-- url     : https://prove2.me/submissions/cc93a3ce-bd9b-40b3-9871-2b81d582beec

/- Standalone direct proof of DKFAsymptotics.C2.
All helper proofs are included; no mission theorem is imported. -/
import Definitions.Def_DKFAsymptotics_Assumptions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option autoImplicit false
noncomputable section

-- Solutions.DensityTools
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

variable {d : ℕ}

theorem isPDF_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    IsPDF f ↔ IsPDF g := by
  unfold IsPDF
  constructor
  · rintro ⟨hp, hi, hn⟩
    exact ⟨by filter_upwards [hp, h] with z hz he; exact he ▸ hz, hi.congr h, (integral_congr_ae h).symm.trans hn⟩
  · rintro ⟨hp, hi, hn⟩
    exact ⟨by filter_upwards [hp, h] with z hz he; exact he.symm ▸ hz, hi.congr h.symm, (integral_congr_ae h).trans hn⟩

theorem densityMeasure_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    densityMeasure f = densityMeasure g := by
  apply withDensity_congr_ae
  filter_upwards [h] with z hz using congrArg ENNReal.ofReal hz

theorem l1Norm_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    l1Norm f = l1Norm g := by
  apply lintegral_congr_ae
  filter_upwards [h] with z hz using congrArg (fun r => ENNReal.ofReal |r|) hz

theorem weakly_congr {f g : ℕ+ → Density d} {P : Measure (State d)}
    (h : ∀ n, f n =ᵐ[volume] g n) : Weakly f P ↔ Weakly g P := by
  have he : ∀ n, densityMeasure (f n) = densityMeasure (g n) :=
    fun n => densityMeasure_congr (h n)
  simp only [Weakly, he]

theorem predictDensity_congr (M : Model d) {s s' : Density d}
    (hs : s =ᵐ[volume] s') : predictDensity M s = predictDensity M s' := by
  funext z
  apply integral_congr_ae
  filter_upwards [hs] with y hy using congrArg (transition M y z * ·) hy

theorem updateWeight_congr (M : Model d) {s s' u u' : Density d}
    (hs : s =ᵐ[volume] s') (hu : u =ᵐ[volume] u') :
    updateWeight M s u =ᵐ[volume] updateWeight M s' u' := by
  have hp := predictDensity_congr M hs
  filter_upwards [hu] with z hz
  simp only [updateWeight, hz, hp]

theorem updateDefined_congr (M : Model d) {s s' u u' : Density d}
    (hs : s =ᵐ[volume] s') (hu : u =ᵐ[volume] u') :
    UpdateDefined M s u ↔ UpdateDefined M s' u' := by
  have he := updateWeight_congr M hs hu
  have hn := l1Norm_congr he
  unfold UpdateDefined
  rw [hn]
  exact and_congr_left (fun _ => ⟨fun h => h.congr he, fun h => h.congr he.symm⟩)

theorem updateDensity_congr (M : Model d) {s s' u u' : Density d}
    (hs : s =ᵐ[volume] s') (hu : u =ᵐ[volume] u') :
    updateDensity M s u =ᵐ[volume] updateDensity M s' u' := by
  have he := updateWeight_congr M hs hu
  have hn := l1Norm_congr he
  filter_upwards [he] with z hz
  simp only [updateDensity, hz, hn]

theorem isGaussianPDF_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    IsGaussianPDF f ↔ IsGaussianPDF g := by
  constructor
  · rintro ⟨hf, m, C, hC, he⟩
    exact ⟨(isPDF_congr h).mp hf, m, C, hC, h.symm.trans he⟩
  · rintro ⟨hg, m, C, hC, he⟩
    exact ⟨(isPDF_congr h).mpr hg, m, C, hC, h.trans he⟩

theorem isProbabilityMeasure_densityMeasure {f : Density d} (hf : IsPDF f) :
    IsProbabilityMeasure (densityMeasure f) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf.2.1 hf.1, hf.2.2, ENNReal.ofReal_one]

def densityProbabilityMeasure {f : Density d} (hf : IsPDF f) :
    ProbabilityMeasure (State d) := ⟨densityMeasure f, isProbabilityMeasure_densityMeasure hf⟩

theorem weakly_iff_tendsto {f : ℕ+ → Density d} (hf : ∀ n, IsPDF (f n))
    (P : ProbabilityMeasure (State d)) :
    Weakly f P ↔ Tendsto (fun n => densityProbabilityMeasure (hf n)) atTop (𝓝 P) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  rfl

theorem integral_densityMeasure {f : Density d} (hf : IsPDF f)
    (g : State d → ℝ) :
    (∫ z, g z ∂densityMeasure f) = ∫ z, f z * g z ∂volume := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hf.2.1.aemeasurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hf.1] with z hz
  simp [ENNReal.toReal_ofReal hz]

theorem l1Norm_toReal {f : Density d} (hf : AEStronglyMeasurable f volume) :
    (l1Norm f).toReal = ∫ z, ‖f z‖ ∂volume := by
  rw [integral_norm_eq_lintegral_enorm hf]
  simp only [l1Norm, ← ofReal_norm, Real.norm_eq_abs]

theorem bounded_test_integrable {f : Density d} (hf : Integrable f volume)
    (g : BoundedContinuousFunction (State d) ℝ) :
    Integrable (fun z => f z * g z) volume :=
  hf.mul_bdd g.continuous.aestronglyMeasurable (ae_of_all _ g.norm_coe_le_norm)

/-- The estimate used in the first two sentences of the proof of Theorem 2. -/
theorem integral_density_difference_le {f f' : Density d}
    (hf : IsPDF f) (hf' : IsPDF f')
    (g : BoundedContinuousFunction (State d) ℝ) :
    ‖(∫ z, g z ∂densityMeasure f) - (∫ z, g z ∂densityMeasure f')‖ ≤
      ‖g‖ * (l1Distance f f').toReal := by
  rw [integral_densityMeasure hf, integral_densityMeasure hf',
    ← integral_sub (bounded_test_integrable hf.2.1 g)
      (bounded_test_integrable hf'.2.1 g)]
  calc
    _ ≤ ∫ z, ‖g‖ * ‖f z - f' z‖ ∂volume := by
      apply norm_integral_le_of_norm_le ((hf.2.1.sub hf'.2.1).norm.const_mul ‖g‖)
      filter_upwards [] with z
      rw [← sub_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm z) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = ‖g‖ * (l1Distance f f').toReal := by
      rw [integral_const_mul, l1Distance, l1Norm_toReal (hf.2.1.sub hf'.2.1).1]
      rfl

theorem weakly_of_l1Distance {f f' : ℕ+ → Density d} {P : Measure (State d)}
    (hf : ∀ n, IsPDF (f n)) (hf' : ∀ n, IsPDF (f' n))
    (hw : Weakly f P)
    (hl1 : Tendsto (fun n => l1Distance (f n) (f' n)) atTop (𝓝 0)) :
    Weakly f' P := by
  intro g
  have hreal : Tendsto (fun n => (l1Distance (f n) (f' n)).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hl1
  have hdiff : Tendsto (fun n => (∫ z, g z ∂densityMeasure (f n)) -
      (∫ z, g z ∂densityMeasure (f' n))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => integral_density_difference_le (hf n) (hf' n) g)
      (by simpa using hreal.const_mul ‖g‖)
  simpa only [sub_sub_cancel, sub_zero] using (hw g).sub hdiff

end DKFAsymptotics.Proof
end

-- Solutions.C1C2
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

theorem C1 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) : Weakly D.s' D.P :=
  weakly_of_l1Distance D.s_pdf (fun n => (D.s'_gaussian n).1) h.A1 h.A2

theorem C2 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) : Weakly D.u' (Measure.dirac D.b) :=
  weakly_of_l1Distance D.u_pdf (fun n => (D.u'_gaussian n).1) h.A3 h.A4

end DKFAsymptotics.Proof
end

open MeasureTheory Filter Matrix DKFAsymptotics
open scoped Topology ENNReal

theorem solution {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) :
    Weakly D.u' (Measure.dirac D.b) := by
  exact DKFAsymptotics.Proof.C2 M D h
