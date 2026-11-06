-- Prove2me | solution 1 for GJNSteadyState.Interchange.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:32:15.343263+00:00
-- url     : https://prove2.me/submissions/901618fc-905a-4635-8163-f49bec4ef66f

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Lyapunov
open MeasureTheory ProbabilityTheory

open GJNSteadyState.Interchange in
theorem solution {X : Type*} [MeasurableSpace X] (κ : Kernel X X) [IsMarkovKernel κ]
    (π : Measure X) [IsProbabilityMeasure π] (hπ : κ.Invariant π)
    (Φ : X → NNReal) (hΦ : Measurable Φ) (γ K : ℝ)
    (hgeo : IsGeomLyapunov (kernelExp κ) Φ γ K)
    (hphi : phiSup (kernelExp κ) Φ < ⊤) :
    ∫⁻ x, (Φ x : ENNReal) ∂π ≤
      phiSup (kernelExp κ) Φ * ENNReal.ofReal K / ENNReal.ofReal (1 - γ) := by
  obtain ⟨hγ0, hγ1, hgeo⟩ := hgeo
  set φ := phiSup (kernelExp κ) Φ with hφdef
  set V : X → ENNReal := fun x => (Φ x : ENNReal) with hVdef
  have hVm : Measurable V := by
    simp only [hVdef]; exact measurable_coe_nnreal_ennreal.comp hΦ
  set g : ENNReal := ENNReal.ofReal γ with hg
  set b : ENNReal := φ * ENNReal.ofReal K with hb
  set c : ENNReal := b * (1 - g)⁻¹ with hc
  -- the drift inequality `P V ≤ γ V + b`
  have hdrift : ∀ x, ∫⁻ y, V y ∂(κ x) ≤ g * V x + b := by
    intro x
    have hE : kernelExp κ x (fun y => (Φ y : ENNReal)) = ∫⁻ y, V y ∂(κ x) := rfl
    by_cases hx : K < (Φ x : ℝ)
    · have := hgeo x hx
      rw [hE] at this
      exact le_trans this le_self_add
    · push Not at hx
      have h1 : ((Φ x : ENNReal))⁻¹ * ∫⁻ y, V y ∂(κ x) ≤ φ := by
        rw [hφdef, phiSup]
        exact le_iSup (fun x => ((Φ x : ENNReal))⁻¹ * kernelExp κ x (fun y => (Φ y : ENNReal))) x
      have h2 : ∫⁻ y, V y ∂(κ x) ≤ φ * V x := by
        by_cases h0 : (Φ x : ENNReal) = 0
        · have : ∫⁻ y, V y ∂(κ x) = 0 := by
            by_contra hne
            rw [h0, ENNReal.inv_zero, ENNReal.top_mul hne] at h1
            exact absurd (lt_of_le_of_lt h1 hphi) (lt_irrefl _)
          rw [this]; exact zero_le
        · have hfin : (Φ x : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
          calc ∫⁻ y, V y ∂(κ x)
              = (Φ x : ENNReal) * (((Φ x : ENNReal))⁻¹ * ∫⁻ y, V y ∂(κ x)) := by
                rw [← mul_assoc, ENNReal.mul_inv_cancel h0 hfin, one_mul]
            _ ≤ (Φ x : ENNReal) * φ := by gcongr
            _ = φ * V x := by rw [mul_comm]
      have h3 : V x ≤ ENNReal.ofReal K := by
        simp only [hVdef]
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hx
      calc ∫⁻ y, V y ∂(κ x) ≤ φ * V x := h2
        _ ≤ b := by rw [hb]; gcongr
        _ ≤ g * V x + b := le_add_self
  -- invariance
  have hinv : ∀ f : X → ENNReal, Measurable f → ∫⁻ x, f x ∂π = ∫⁻ x, ∫⁻ y, f y ∂(κ x) ∂π := by
    intro f hf
    conv_lhs => rw [← hπ.def]
    exact Measure.lintegral_bind κ.measurable.aemeasurable hf.aemeasurable
  -- partial geometric sums
  let cn : ℕ → ENNReal := fun n => ∑ i ∈ Finset.range n, g ^ i * b
  have hcn_le : ∀ n, cn n ≤ c := by
    intro n
    have hsum : ∑' i, g ^ i * b = c := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, hc, mul_comm]
    rw [← hsum]
    exact ENNReal.sum_le_tsum _
  -- iterate
  have key : ∀ M : ENNReal, M ≠ ⊤ → ∀ n : ℕ,
      ∫⁻ x, min (V x) M ∂π ≤ ∫⁻ x, min (g ^ n * V x + cn n) M ∂π := by
    intro M hM n
    induction n with
    | zero => simp [cn]
    | succ n ih =>
      refine le_trans ih ?_
      have hmeas : Measurable (fun x => min (g ^ n * V x + cn n) M) := by
        exact ((hVm.const_mul _).add_const _).min measurable_const
      rw [hinv _ hmeas]
      refine lintegral_mono (fun x => ?_)
      have hA : ∫⁻ y, min (g ^ n * V y + cn n) M ∂(κ x) ≤ ∫⁻ y, (g ^ n * V y + cn n) ∂(κ x) :=
        lintegral_mono (fun y => min_le_left _ _)
      have hB : ∫⁻ y, min (g ^ n * V y + cn n) M ∂(κ x) ≤ M := by
        calc ∫⁻ y, min (g ^ n * V y + cn n) M ∂(κ x) ≤ ∫⁻ _y, M ∂(κ x) :=
              lintegral_mono (fun y => min_le_right _ _)
          _ = M := by simp
      have hC : ∫⁻ y, (g ^ n * V y + cn n) ∂(κ x) ≤ g ^ (n + 1) * V x + cn (n + 1) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVm]
        simp only [lintegral_const, measure_univ, mul_one]
        calc g ^ n * ∫⁻ y, V y ∂(κ x) + cn n ≤ g ^ n * (g * V x + b) + cn n := by
              gcongr; exact hdrift x
          _ = g ^ (n + 1) * V x + cn (n + 1) := by
              simp only [cn, Finset.sum_range_succ]
              rw [mul_add, pow_succ, mul_assoc]
              ring
      exact le_min (le_trans hA hC) hB
  -- limit n → ∞
  have hlim : ∀ M : ENNReal, M ≠ ⊤ → ∫⁻ x, min (V x) M ∂π ≤ c := by
    intro M hM
    have hle : ∀ n, ∫⁻ x, min (V x) M ∂π ≤ ∫⁻ x, min (g ^ n * V x + c) M ∂π := by
      intro n
      refine le_trans (key M hM n) (lintegral_mono (fun x => ?_))
      gcongr
      exact hcn_le n
    have hglt : g < 1 := by
      rw [hg]; exact (ENNReal.ofReal_lt_one).2 hγ1
    have htend : Filter.Tendsto (fun n => ∫⁻ x, min (g ^ n * V x + c) M ∂π) Filter.atTop
        (nhds (∫⁻ x, min c M ∂π)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => M) (fun n => ?_) (fun n => ?_)
        ?_ ?_
      · exact (((hVm.const_mul _).add_const _).min measurable_const)
      · exact Filter.Eventually.of_forall (fun x => min_le_right _ _)
      · simp [hM]
      · refine Filter.Eventually.of_forall (fun x => ?_)
        have h0 : Filter.Tendsto (fun n => g ^ n * V x) Filter.atTop (nhds 0) := by
          have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hglt)
            (b := V x) (Or.inr ENNReal.coe_ne_top)
          simpa using this
        have h1 : Filter.Tendsto (fun n => g ^ n * V x + c) Filter.atTop (nhds (0 + c)) :=
          h0.add tendsto_const_nhds
        rw [zero_add] at h1
        exact h1.min tendsto_const_nhds
    have h2 : ∫⁻ x, min (V x) M ∂π ≤ ∫⁻ x, min c M ∂π :=
      ge_of_tendsto' htend hle
    calc ∫⁻ x, min (V x) M ∂π ≤ ∫⁻ x, min c M ∂π := h2
      _ ≤ ∫⁻ _x, c ∂π := lintegral_mono (fun x => min_le_left _ _)
      _ = c := by simp
  -- M → ∞
  have hsup : ∫⁻ x, V x ∂π = ⨆ m : ℕ, ∫⁻ x, min (V x) (m : ENNReal) ∂π := by
    rw [← lintegral_iSup]
    · congr 1
      funext x
      rw [← inf_iSup_eq, ENNReal.iSup_natCast]
      simp
    · intro m; exact hVm.min measurable_const
    · intro m m' hmm' x
      exact min_le_min le_rfl (by exact_mod_cast hmm')
  have hfinal : ∫⁻ x, V x ∂π ≤ c := by
    rw [hsup]
    exact iSup_le (fun m => hlim _ (ENNReal.natCast_ne_top m))
  have hceq : c = φ * ENNReal.ofReal K / ENNReal.ofReal (1 - γ) := by
    rw [hc, hb, div_eq_mul_inv, ENNReal.ofReal_sub _ hγ0.le, ENNReal.ofReal_one]
  rw [← hceq]
  exact hfinal
