-- Prove2me | solution 1 for DedekindZeta.Theta.continuousOn_mixedThetaKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:34.403094+00:00
-- url     : https://prove2.me/submissions/b80a2f0e-56be-4455-a19f-1b3132645976

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_summable_theta
import Theorems.Thm_DedekindZeta_Theta_norm_toMinkowski_sq
import Theorems.Thm_DedekindZeta_Theta_continuous_mixedGaussian

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) :
    ContinuousOn (mixedThetaKernel K I)
      {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  classical
  rcases eq_or_ne I 0 with hI | hI
  · -- `I = 0`: the index set is empty, so the kernel is the constant `0`.
    subst hI
    haveI : IsEmpty {a : K // a ∈ ((0 : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) ∧ a ≠ 0} := by
      refine ⟨?_⟩
      rintro ⟨a, ha, ha0⟩
      rw [FractionalIdeal.coe_zero, Submodule.mem_bot] at ha
      exact ha0 ha
    have hzero : mixedThetaKernel K (0 : FractionalIdeal (𝓞 K)⁰ K) = fun _ => (0 : ℂ) := by
      funext x; rw [mixedThetaKernel, tsum_empty]
    rw [hzero]; exact continuousOn_const
  · -- `I ≠ 0`: prove `ContinuousAt` at each point of the open locus.
    have hopen : IsOpen {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      isOpen_compl_singleton.preimage (mixedEmbedding.continuous_norm K)
    intro x₀ hx₀
    refine ContinuousAt.continuousWithinAt ?_
    -- A closed ball around `x₀` contained in the open locus.
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀
    set B := Metric.closedBall x₀ (ε / 2) with hBdef
    have hBs : B ⊆ {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      (Metric.closedBall_subset_ball (by linarith)).trans hsub
    have hBcpt : IsCompact B := isCompact_closedBall x₀ (ε / 2)
    have hBne : B.Nonempty := ⟨x₀, Metric.mem_closedBall_self (by positivity)⟩
    -- Each `normAtPlace w` is bounded below by a positive constant on `B`.
    have hpos : ∀ w : InfinitePlace K, ∃ d : ℝ, 0 < d ∧ ∀ x ∈ B, d ≤ normAtPlace w x := by
      intro w
      obtain ⟨xm, hxm, hmin⟩ :=
        hBcpt.exists_isMinOn hBne (continuous_normAtPlace w).continuousOn
      refine ⟨normAtPlace w xm, ?_, fun x hx => isMinOn_iff.mp hmin x hx⟩
      exact lt_of_le_of_ne (normAtPlace_nonneg w xm)
        (Ne.symm (mixedEmbedding.norm_ne_zero_iff.mp (hBs hxm) w))
    choose d hd_pos hd_le using hpos
    obtain ⟨δ, hδ_pos, hδ_le⟩ :
        ∃ δ : ℝ, 0 < δ ∧ ∀ (w : InfinitePlace K), ∀ x ∈ B, δ ≤ normAtPlace w x := by
      refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_, ?_⟩
      · exact (Finset.lt_inf'_iff _).mpr (fun w _ => hd_pos w)
      · intro w x hx
        exact le_trans (Finset.inf'_le d (Finset.mem_univ w)) (hd_le w x hx)
    -- Summability of the dominating function (subtype of the lattice theta series).
    have hδ2 : 0 < δ ^ 2 := by positivity
    have hinj : Function.Injective
        (fun a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} =>
          (⟨a.1, a.2.1⟩ : (I : Submodule (𝓞 K) K))) := by
      intro a b h
      apply Subtype.ext
      simpa using congrArg Subtype.val h
    -- The majorant `∑' a, exp(-πδ²‖eEmb a‖²)` is summable: it is the lattice theta
    -- series of `summable_theta` restricted along the injection `incl`.  We align
    -- the result with `(a : K)` via `congrArg` (a *syntactic* congruence on the
    -- `K`-coercion), so unification never descends through `eEmb`/the norm (which
    -- would blow up `whnf` because the two subtype coercions differ).
    have hu : Summable (fun a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} =>
        Real.exp (-Real.pi * δ ^ 2 * ‖eEmb K (a : K)‖ ^ 2)) := by
      refine ((summable_theta K hI hδ2).comp_injective hinj).congr (fun a => ?_)
      exact congrArg (fun z : K => Real.exp (-Real.pi * δ ^ 2 * ‖eEmb K z‖ ^ 2))
        (rfl : ((⟨a.1, a.2.1⟩ : (I : Submodule (𝓞 K) K)) : K) = (a : K))
    -- Each summand is continuous (on `B`).
    have hf_cont : ∀ a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ContinuousOn (fun x => (mixedGaussian K (x * mixedEmbedding K (a : K)) : ℂ)) B := by
      intro a
      refine Continuous.continuousOn ?_
      exact Complex.continuous_ofReal.comp
        ((continuous_mixedGaussian K).comp (continuous_id.mul continuous_const))
    -- The uniform dominating bound on `B`.
    have hbound : ∀ (a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) x, x ∈ B →
        ‖(mixedGaussian K (x * mixedEmbedding K (a : K)) : ℂ)‖
          ≤ Real.exp (-Real.pi * δ ^ 2 * ‖eEmb K (a : K)‖ ^ 2) := by
      intro a x hx
      have hg0 : 0 ≤ mixedGaussian K (x * mixedEmbedding K (a : K)) := by
        rw [mixedGaussian]; positivity
      have hQ : ‖eEmb K (a : K)‖ ^ 2
          = ∑ w : InfinitePlace K,
              (InfinitePlace.mult w : ℝ) * normAtPlace w (mixedEmbedding K (a : K)) ^ 2 := by
        rw [← eEmbℝ_mixedEmbedding K (a : K)]
        exact norm_toMinkowski_sq K (mixedEmbedding K (a : K))
      have key : δ ^ 2 * ‖eEmb K (a : K)‖ ^ 2
          ≤ ∑ w : InfinitePlace K,
              (InfinitePlace.mult w : ℝ) * normAtPlace w (x * mixedEmbedding K (a : K)) ^ 2 := by
        rw [hQ, Finset.mul_sum]
        refine Finset.sum_le_sum (fun w _ => ?_)
        have hδle : δ ≤ normAtPlace w x := hδ_le w x hx
        have hsq : δ ^ 2 ≤ normAtPlace w x ^ 2 := by
          have := normAtPlace_nonneg w x
          nlinarith [hδ_pos.le, hδle, this]
        have hmult : (0 : ℝ) ≤ (InfinitePlace.mult w : ℝ) := by positivity
        have hP : (0 : ℝ) ≤ normAtPlace w (mixedEmbedding K (a : K)) ^ 2 := sq_nonneg _
        rw [map_mul, mul_pow]
        nlinarith [mul_nonneg (mul_nonneg hmult hP) (sub_nonneg.mpr hsq)]
      rw [Complex.norm_real, Real.norm_of_nonneg hg0, mixedGaussian]
      refine Real.exp_le_exp.mpr ?_
      rw [mul_assoc]
      nlinarith [Real.pi_pos, key]
    -- Continuity on `B`, hence `ContinuousAt x₀`.
    have hcontB : ContinuousOn (mixedThetaKernel K I) B :=
      continuousOn_tsum hf_cont hu hbound
    exact hcontB.continuousAt (Metric.closedBall_mem_nhds x₀ (by positivity))
end DedekindZeta.Theta
