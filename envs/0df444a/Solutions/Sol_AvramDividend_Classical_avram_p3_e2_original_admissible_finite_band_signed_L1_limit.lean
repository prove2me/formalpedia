-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e2_original_admissible_finite_band_signed_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:34:17.918998+00:00
-- url     : https://prove2.me/submissions/1cfbf2cb-a798-4b77-b768-cab7de071bf8

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_admissible_signed_source_budget_no_L1_assumption
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont
(fun ω => (τ ω : WithTop ℝ≥0))) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b L R A : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A) (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
|w u - w v| ≤ L * |u - v|) (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) (E : ℕ → Set (ℝ≥0 × Ω)) (hEm : ∀ n, MeasurableSet[𝓕.rightCont.predictable] (E n))
(hEregion : ∀ n, ∀ p ∈ E n, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(hDeriv : ∀ y ∈ Icc a b, |deriv w y| ≤ A)
(hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
  X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
(hEcap : ∀ n, ∀ p ∈ E n, ENNReal.ofReal (Function.leftLim
  (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) < C)
(Mmesh Bmesh : ℕ → Ω → ℝ)
(hSource : ∀ n,
  let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ =>
    if p.1 ∈ E n ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
       (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    if p ∈ E n then Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1) +
       (∫ z in Iio (0 : ℝ),
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
       q * w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1))
    else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  Mmesh n = M ∧ Bmesh n = B)
(M B DM DB : Ω → ℝ)
(hDM : Integrable DM P) (hDB : Integrable DB P)
(hMDom : ∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω)
(hBDom : ∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω)
(hMLim : ∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
(hBLim : ∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) :
(Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
(Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) := by
  have hSigns (n : ℕ) :
      (Integrable (Mmesh n) P ∧ (∫ ω, Mmesh n ω ∂P) = 0) ∧
      (Integrable (Bmesh n) P ∧ (∫ ω, Bmesh n ω ∂P) ≤ 0) := by
    have hLocal := avram_p3_e2_original_admissible_signed_source_budget_no_L1_assumption
      X hBV T τ hτBound hτ x C D hD w hw_cont hw_neg q hq
      a b L R A ha ha2 hab hL hR hA hLip hWbound
      (E n) (hEm n) (hEregion n) hDeriv hw_gen (hEcap n)
    have hEq := hSource n
    dsimp only at hLocal hEq
    rcases hEq with ⟨hm, hb⟩
    simpa only [hm, hb] using hLocal
  exact avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
    P Mmesh Bmesh M B DM DB
    (fun n => (hSigns n).1.1.aestronglyMeasurable)
    (fun n => (hSigns n).2.1.aestronglyMeasurable)
    hDM hDB hMDom hBDom hMLim hBLim
    (fun n => (hSigns n).1.2)
    (fun n => (hSigns n).2.2)
