-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw_of_eq_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:43.553006+00:00
-- url     : https://prove2.me/submissions/c3e12947-66cc-45f6-8aab-179ebcb36ff0

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_convexOn_potential_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_readable

section
noncomputable section
open MeasureTheory Set
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_readable hνW hW hconv)
end
end
end

section
noncomputable section
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
omit [InnerProductSpace ℝ E] in
/-- The suspension potential is continuous, including along the crease of its absolute value. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.continuous_potential {V f : E → ℝ} (hV : Continuous V) (hf : Continuous f)
    (beta sigma : ℝ) (N : ℕ) : Continuous (potential V f beta sigma N) := by
  unfold potential
  fun_prop
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Line
/-- **Log-concavity of the joint law under (110)**, given (109). -/
theorem solution {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ)
    {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (heq : FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (volume.tilted fun x => -V x) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N =
      (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).tilted fun p =>
        -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))))
    (h : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (volume.tilted fun x => -V x) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) :
    FunctionalInequalities.KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)) := by
    let L : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n →ₗ[ℝ] ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) :=
      { toFun := fun p =>
          (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))
        map_add' := by
          intro p q
          apply Prod.ext
          · simp
          · funext i
            ext j
            simp
        map_smul' := by
          intro c p
          apply Prod.ext
          · simp
          · funext i
            ext j
            simp }

    have hLcont :
        Continuous (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
          (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      fun_prop

    have hconv :
        ConvexOn ℝ Set.univ
          (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
              (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      simpa [L, Function.comp_def] using
        (FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential_readable hV hf hβ.le hVa hfM N hN).comp_linearMap L

    have hpot :
        Continuous
          (fun q : ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N q) :=
      FunctionalInequalities.KLS.LogConcave.Suspension.continuous_potential hV.continuous hf.continuous β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N

    have hcont :
        Continuous
          (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
              (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      change Continuous
        ((fun q : ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) =>
            FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N q) ∘
          (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n =>
            (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))))
      exact hpot.comp hLcont

    let ν : ProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) :=
      ⟨FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (volume.tilted fun x => -V x) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N, h⟩

    have hν :
        (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)) =
          (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).tilted
            (fun p =>
              -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
                (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      simpa [ν] using heq

    change FunctionalInequalities.KLS.LogConcave ν
    exact
      FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted
        hν hcont hconv
