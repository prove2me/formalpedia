-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.ae_add_eq_of_integral_mul_fderiv_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:15.080693+00:00
-- url     : https://prove2.me/submissions/fbeef502-6423-4f83-97db-fcbd121b3bc9

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_integral_mul_sub_translate_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_locallyIntegrable_comp_add_right_readable

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Change of variables `y = x + v` for Haar measure. -/
theorem FunctionalInequalities.Energy.Euclidean.integral_mul_comp_add_right (h φ : V → ℝ) (v : V) :
    ∫ x, φ x * h (x + v) ∂m = ∫ x, φ (x - v) * h x ∂m := by
  simpa [add_sub_cancel_right] using
    (integral_add_right_eq_self (μ := m)
      (fun y : V => φ (y - v) * h y) v)
/-- Zero weak gradient makes `h` invariant under every translation, up to null sets. -/
theorem solution {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    (v : V) :
    ∀ᵐ x ∂m, h (x + v) = h x := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (μ := m) (f := fun x => h (x + v)) (f' := h)
    (FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right_readable m hh v) hh
  intro g hg hgc
  have hi0 : Integrable (fun x => h x * g x) m := by
    have hi :=
      hh.integrable_smul_right_of_hasCompactSupport
        (g := g) hg.continuous hgc
    simpa [smul_eq_mul] using hi
  have hgv : Continuous (fun x : V => g (x - v)) :=
    hg.continuous.comp (continuous_id.sub continuous_const)
  have hgvc : HasCompactSupport (fun x : V => g (x - v)) :=
    hgc.comp_homeomorph (Homeomorph.subRight v)
  have hi1 : Integrable (fun x => h x * g (x - v)) m := by
    have hi :=
      hh.integrable_smul_right_of_hasCompactSupport
        (g := fun x : V => g (x - v)) hgv hgvc
    simpa [smul_eq_mul] using hi
  have hsub :
      ∫ x, h x * (g x - g (x - v)) ∂m = 0 :=
    FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero_readable m hh h0 hg hgc v
  have hsub' :
      ∫ x, (h x * g x - h x * g (x - v)) ∂m = 0 := by
    calc
      ∫ x, (h x * g x - h x * g (x - v)) ∂m =
          ∫ x, h x * (g x - g (x - v)) ∂m := by
            exact integral_congr_ae
              (Eventually.of_forall fun x => by ring)
      _ = 0 := hsub
  have heq :
      (∫ x, h x * g x ∂m) = ∫ x, h x * g (x - v) ∂m := by
    rw [integral_sub hi0 hi1] at hsub'
    exact sub_eq_zero.mp hsub'
  calc
    ∫ x, g x • h (x + v) ∂m =
        ∫ x, g x * h (x + v) ∂m := by
          exact integral_congr_ae
            (Eventually.of_forall fun x => by simp only [smul_eq_mul])
    _ = ∫ x, g (x - v) * h x ∂m :=
      FunctionalInequalities.Energy.Euclidean.integral_mul_comp_add_right m h g v
    _ = ∫ x, h x * g (x - v) ∂m := by
      exact integral_congr_ae
        (Eventually.of_forall fun x => by ring)
    _ = ∫ x, h x * g x ∂m := heq.symm
    _ = ∫ x, g x • h x ∂m := by
      exact integral_congr_ae
        (Eventually.of_forall fun x => by simp [smul_eq_mul, mul_comm])
