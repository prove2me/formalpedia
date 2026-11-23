-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_simpleFunc_physical_mark_count_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:02:01.649184+00:00
-- url     : https://prove2.me/submissions/0cfc43b8-154e-4bca-ab3f-734d422370fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_simpleFunc_physical_mark_fibre_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_nonzero_jump_strictly_negative
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hSupport :
      ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        J ω = ∑ u ∈ S,
          (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
    (hCountLaw : ∀ (B : Set ℝ), MeasurableSet B →
      B ⊆ Iio (0 : ℝ) →
      (let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 t ×ˢ B)
       ∃ (K : Ω → ℕ) (r : ℝ≥0),
         Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
         (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
         (r : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal))
    (q : ℕ → SimpleFunc ℝ ℝ)
    (hNonpos : ∀ n y, q n y ≤ 0)
    (hPointwise : ∀ y, y < 0 →
      Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) :
    ∃ (f : ℕ → Ω → ℝ) (r : ℕ → ℝ),
      (∀ n, Measurable (f n)) ∧
      (∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (θ * J ω))) ∧
      (∀ n, r n = (t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (q n y) - 1 ∂X.ν)) ∧
      ∀ n : ℕ, ∃ (k : ℕ) (B : Fin k → Set ℝ) (a : Fin k → ℝ),
        (∀ i, MeasurableSet (B i)) ∧
        (∀ i, B i ⊆ Iio (0 : ℝ)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ᵐ ω ∂P, f n ω =
          ∑ i : Fin k, a i *
            (((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal) ∧
        r n = ∑ i : Fin k,
          (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
            (Real.exp (a i) - 1) := by
  classical
  obtain ⟨f, r, hMeas, hNonposF, hFibre, hRate, hCells⟩ :=
    AvramDividend.Classical.avram_a77_original_simpleFunc_physical_mark_fibre_exact
      X hFinite t θ hθ J hJMeas hJEq hSupport hCountLaw q hNonpos
  refine ⟨f, r, hMeas, hNonposF, ?_, hRate, hCells⟩
  filter_upwards [hSupport, hFibre] with ω hS hF
  obtain ⟨S, hSch, hSum⟩ := hS
  let jump : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
  have hEach : ∀ u ∈ S,
      Tendsto (fun n : ℕ => q n (jump u)) atTop
        (𝓝 (θ * jump u)) := by
    intro u hu
    have hu := (hSch u).mp hu
    exact hPointwise (jump u)
      (AvramDividend.Classical.avram_p2_c_borel_original_nonzero_jump_strictly_negative
        X ω u hu.1 hu.2.2)
  have hLimit : Tendsto
      (fun n : ℕ => ∑ u ∈ S, q n (jump u)) atTop
      (𝓝 (∑ u ∈ S, θ * jump u)) :=
    tendsto_finset_sum S hEach
  have hFun :
      (fun n : ℕ => f n ω) =
        (fun n : ℕ => ∑ u ∈ S, q n (jump u)) := by
    funext n
    exact hF n S hSch
  have hEnd : (∑ u ∈ S, θ * jump u) = θ * J ω := by
    rw [← Finset.mul_sum]
    simpa only [jump] using congrArg (fun x : ℝ => θ * x) hSum.symm
  rw [hFun, ← hEnd]
  exact hLimit
