-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb80e_original_marked_J_restrict_fullnegative_finite_T
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:25:16.693398+00:00
-- url     : https://prove2.me/submissions/ff97694a-c27f-49a3-b401-fd7a19b496f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapTop : C = ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let A : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)
    ∀ ω : Ω, ∀ n : ℕ,
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) =
      (∫ p, H n ((p.1, ω), p.2) ∂((NX ω).restrict A)) := by
  classical
  intro δ U H NX J V S A ω n
  have hOutside (p : ℝ≥0 × ℝ) (hp : p ∉ A) :
      H n ((p.1, ω), p.2) = 0 := by
    rcases p with ⟨t, z⟩
    by_cases hm :
        0 < t ∧ (t : ℝ) < T - δ n ∧
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C ∧ z < 0
    · have hd : 0 ≤ δ n := by
        change 0 ≤ T / ((n : ℝ) + 2)
        positivity
      have hTime : t ≤ S := by
        have hReal : (t : ℝ) ≤ T := by
          exact (lt_of_lt_of_le hm.2.1 (sub_le_self T hd)).le
        exact_mod_cast hReal
      have hmem : (t, z) ∈ A := by
        change t ∈ Ioc (0 : ℝ≥0) S ∧ z ∈ Iio (0 : ℝ)
        exact ⟨⟨hm.1, hTime⟩, hm.2.2.2.2.2⟩
      exact (hp hmem).elim
    · simp only [H, if_neg hm]
  change (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) =
    (∫ p, H n ((p.1, ω), p.2) ∂((NX ω).restrict A))
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun p : ℝ≥0 × ℝ => H n ((p.1, ω), p.2))
    (s := A) (μ := NX ω) hOutside).symm
