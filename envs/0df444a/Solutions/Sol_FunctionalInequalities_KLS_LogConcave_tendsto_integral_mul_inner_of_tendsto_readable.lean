-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_inner_of_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:18.151402+00:00
-- url     : https://prove2.me/submissions/ce8cfe97-9f81-4a09-a5f4-fa7632b925f0

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_eq_integral_mul_exp_readable

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
/-- The vector-valued version: `L²(ν; V)` convergence of fields gives convergence of
`∫ ψ ⟪G_n, w⟫ dm` for a continuous compactly supported weight `ψ` and a direction `w`. -/
theorem solution (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) {G : ℕ → V → V} (hG : ∀ n, MemLp (G n) 2 (ν : Measure V))
    {F : Lp V 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 F))
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (w : V) :
    Tendsto (fun n => ∫ x, ψ x * ⟪G n x, w⟫ ∂m) atTop (𝓝 (∫ x, ψ x * ⟪F x, w⟫ ∂m)) := by
  let Z : ℝ := ∫ y, Real.exp (-U y) ∂m
  let W : V → V := fun x => ((Z * Real.exp (U x)) * ψ x) • w

  have hWcont : Continuous W := by
    dsimp [W]
    fun_prop

  have hWsupport : Function.support W ⊆ Function.support ψ := by
    intro x hx
    by_contra h
    have hψx : ψ x = 0 := by
      simpa [Function.mem_support] using h
    have hWx : W x = 0 := by
      simp [W, hψx]
    exact hx hWx

  have hWc : HasCompactSupport W := by
    exact hψc.mono hWsupport

  have hW : MemLp W 2 (ν : Measure V) :=
    hWcont.memLp_of_hasCompactSupport hWc

  have hpair :
      ∀ a : Lp V 2 (ν : Measure V),
        (∫ x, ⟪(a : V → V) x, W x⟫ ∂(ν : Measure V)) =
          ⟪a, hW.toLp W⟫ := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hW] with x hx
    rw [hx]

  have hseq :
      ∀ n, (∫ x, ψ x * ⟪G n x, w⟫ ∂m) =
        ⟪(hG n).toLp (G n), hW.toLp W⟫ := by
    intro n
    calc
      ∫ x, ψ x * ⟪G n x, w⟫ ∂m =
          ∫ x, (Z * Real.exp (U x)) *
            (ψ x * ⟪G n x, w⟫) ∂(ν : Measure V) := by
              simpa [Z] using
                (FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_readable m hνU
                  (fun x => ψ x * ⟪G n x, w⟫))
      _ = ∫ x, ⟪((hG n).toLp (G n) : V → V) x, W x⟫
            ∂(ν : Measure V) := by
              apply integral_congr_ae
              filter_upwards [MemLp.coeFn_toLp (hG n)] with x hx
              dsimp [W]
              rw [hx]
              simp only [inner_smul_right]
              ring
      _ = ⟪(hG n).toLp (G n), hW.toLp W⟫ :=
        hpair ((hG n).toLp (G n))

  have htarget :
      (∫ x, ψ x * ⟪F x, w⟫ ∂m) = ⟪F, hW.toLp W⟫ := by
    calc
      ∫ x, ψ x * ⟪F x, w⟫ ∂m =
          ∫ x, (Z * Real.exp (U x)) *
            (ψ x * ⟪(F : V → V) x, w⟫) ∂(ν : Measure V) := by
              simpa [Z] using
                (FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_readable m hνU
                  (fun x => ψ x * ⟪(F : V → V) x, w⟫))
      _ = ∫ x, ⟪(F : V → V) x, W x⟫ ∂(ν : Measure V) := by
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [W]
            simp only [inner_smul_right]
            ring
      _ = ⟪F, hW.toLp W⟫ := hpair F

  have hinner :
      Tendsto
        (fun n => ⟪(hG n).toLp (G n), hW.toLp W⟫)
        atTop (𝓝 ⟪F, hW.toLp W⟫) :=
    hlim.inner tendsto_const_nhds

  rw [show (fun n => ∫ x, ψ x * ⟪G n x, w⟫ ∂m) =
      (fun n => ⟪(hG n).toLp (G n), hW.toLp W⟫) from funext hseq]
  rw [show (∫ x, ψ x * ⟪F x, w⟫ ∂m) = ⟪F, hW.toLp W⟫ from htarget]
  exact hinner
