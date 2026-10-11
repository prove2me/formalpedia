-- Prove2me | solution 1 for FredholmBanach.finiteDimensional_ker_isClosed_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:46:26.385021+00:00
-- url     : https://prove2.me/submissions/fbae89e2-aecf-422a-8880-f5aad6ee0e8a

import Definitions.Def_FredholmBanach_Setting
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

open Topology Filter

theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (u : E →L[𝕜] F) :
    (FiniteDimensional 𝕜 u.ker ∧ IsClosed (u.range : Set F)) ↔
      ∀ x : ℕ → E, (∃ C, ∀ n, ‖x n‖ ≤ C) →
        ∀ y : F, Filter.Tendsto (fun n => u (x n)) Filter.atTop (𝓝 y) →
          ∃ a : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (𝓝 a) := by
  -- a closed complement `E₀` of the kernel, cut out by a continuous projection `P` onto it
  have key : FiniteDimensional 𝕜 u.ker → ∃ P : E →L[𝕜] u.ker,
      IsClosed (LinearMap.ker (P : E →ₗ[𝕜] u.ker) : Set E) ∧
      (∀ z : E, z - (P z : E) ∈ LinearMap.ker (P : E →ₗ[𝕜] u.ker)) ∧
      (∀ z : E, u (P z : E) = 0) ∧
      Function.Injective (u.comp (LinearMap.ker (P : E →ₗ[𝕜] u.ker)).subtypeL) ∧
      Set.range (u.comp (LinearMap.ker (P : E →ₗ[𝕜] u.ker)).subtypeL) = (u.range : Set F) := by
    intro hk
    obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional u.ker
    have hPP : ∀ z : E, P (P z : E) = P z := fun z => hP (P z)
    have hsub : ∀ z : E, z - (P z : E) ∈ LinearMap.ker (P : E →ₗ[𝕜] u.ker) := by
      intro z
      simp [LinearMap.mem_ker, map_sub, hPP]
    have hu0 : ∀ z : E, u (P z : E) = 0 := fun z => (P z).2
    refine ⟨P, P.isClosed_ker, hsub, hu0, ?_, ?_⟩
    · intro a b hab
      have hab' : u ((a : E) - b) = 0 := by
        simpa [map_sub, sub_eq_zero] using hab
      have h1 : (a : E) - b ∈ u.ker := hab'
      have h2 : P ((a : E) - b) = 0 := by
        have := sub_mem a.2 b.2
        simpa [LinearMap.mem_ker] using this
      have h3 := hP ⟨_, h1⟩
      rw [h2] at h3
      apply Subtype.ext
      have := congrArg Subtype.val h3
      simp only [ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.mp this.symm
    · ext w
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, rfl⟩
      · rintro ⟨z, rfl⟩
        refine ⟨⟨_, hsub z⟩, ?_⟩
        simp [map_sub, hu0]
  constructor
  · rintro ⟨hk, hr⟩ x ⟨C, hC⟩ y hy
    obtain ⟨P, hE₀, hsub, hu0, hinj, hrange⟩ := key hk
    set E₀ := LinearMap.ker (P : E →ₗ[𝕜] u.ker)
    haveI : CompleteSpace E₀ := hE₀.completeSpace_coe
    set u₀ := u.comp E₀.subtypeL
    have hclo : IsClosed (Set.range u₀) := by rw [hrange]; exact hr
    let e := u₀.equivRange hinj hclo
    let b : ℕ → E₀ := fun n => ⟨x n - P (x n), hsub (x n)⟩
    have hub : ∀ n, u₀ (b n) = u (x n) := by
      intro n
      simp [u₀, b, map_sub, hu0]
    have hy' : y ∈ Set.range u₀ := by
      refine hclo.mem_of_tendsto hy (Eventually.of_forall fun n => ?_)
      exact ⟨b n, hub n⟩
    have hmem : ∀ n, u₀ (b n) ∈ u₀.range := fun n => LinearMap.mem_range_self _ _
    have hyr : y ∈ u₀.range := hy'
    have hT : Tendsto (fun n => (⟨u₀ (b n), hmem n⟩ : u₀.range)) atTop (𝓝 ⟨y, hyr⟩) := by
      rw [tendsto_subtype_rng]
      simpa [hub] using hy
    have hb : Tendsto b atTop (𝓝 (e.symm ⟨y, hyr⟩)) := by
      have := (e.symm.continuous.tendsto _).comp hT
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, e]
      exact ContinuousLinearMap.equivRange_symm_apply (f := u₀) hinj hclo (b n)
    haveI := FiniteDimensional.proper_rclike 𝕜 u.ker
    have hPb : ∀ n, P (x n) ∈ Metric.closedBall (0 : u.ker) (‖P‖ * C) := by
      intro n
      rw [mem_closedBall_zero_iff]
      exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))
    obtain ⟨a₀, -, φ, hφ, ha⟩ :=
      tendsto_subseq_of_bounded Metric.isBounded_closedBall hPb
    refine ⟨(a₀ : E) + (e.symm ⟨y, hyr⟩ : E), φ, hφ, ?_⟩
    have h1 : Tendsto (fun n => ((P (x (φ n)) : u.ker) : E)) atTop (𝓝 (a₀ : E)) :=
      (continuous_subtype_val.tendsto _).comp ha
    have h2 : Tendsto (fun n => ((b (φ n) : E₀) : E)) atTop (𝓝 (e.symm ⟨y, hyr⟩ : E)) :=
      (continuous_subtype_val.tendsto _).comp (hb.comp hφ.tendsto_atTop)
    refine (h1.add h2).congr fun n => ?_
    simp [b]
  · intro hS
    -- finite-dimensional kernel: the closed unit ball of the kernel is compact
    have hk : FiniteDimensional 𝕜 u.ker := by
      apply FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one
      rw [isCompact_iff_isSeqCompact]
      intro z hz
      have hz' : ∀ n, ‖(z n : E)‖ ≤ 1 := fun n => by
        simpa [mem_closedBall_zero_iff] using hz n
      have h0 : Tendsto (fun n => u (z n : E)) atTop (𝓝 0) := by
        have : ∀ n, u (z n : E) = 0 := fun n => (z n).2
        simp [this]
      obtain ⟨a, φ, hφ, ha⟩ := hS (fun n => (z n : E)) ⟨1, hz'⟩ 0 h0
      have haK : a ∈ u.ker :=
        u.isClosed_ker.mem_of_tendsto ha (Eventually.of_forall fun n => (z (φ n)).2)
      have hza : Tendsto (z ∘ φ) atTop (𝓝 ⟨a, haK⟩) := by
        rw [tendsto_subtype_rng]
        exact ha
      refine ⟨⟨a, haK⟩, ?_, φ, hφ, hza⟩
      exact Metric.isClosed_closedBall.mem_of_tendsto hza
        (Eventually.of_forall fun n => hz (φ n))
    refine ⟨hk, ?_⟩
    obtain ⟨P, hE₀, hsub, hu0, hinj, hrange⟩ := key hk
    set E₀ := LinearMap.ker (P : E →ₗ[𝕜] u.ker)
    haveI : CompleteSpace E₀ := hE₀.completeSpace_coe
    set u₀ := u.comp E₀.subtypeL
    -- `u₀` is bounded below
    have hbd : ∃ K : ℝ, ∀ b : E₀, ‖b‖ ≤ K * ‖u₀ b‖ := by
      by_contra hcon
      push_neg at hcon
      choose b hb using fun n : ℕ => hcon ((n : ℝ) + 1)
      have hbpos : ∀ n, 0 < ‖b n‖ := fun n =>
        lt_of_le_of_lt (mul_nonneg (by positivity) (norm_nonneg _)) (hb n)
      let z : ℕ → E₀ := fun n => (‖b n‖⁻¹ : 𝕜) • b n
      have hz1 : ∀ n, ‖z n‖ = 1 := fun n => by
        simp only [z, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
        exact inv_mul_cancel₀ (hbpos n).ne'
      have hzu : ∀ n, ‖u₀ (z n)‖ ≤ 1 / ((n : ℝ) + 1) := fun n => by
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        simp only [z, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
        rw [le_div_iff₀ hn, inv_mul_eq_div, div_mul_eq_mul_div, div_le_one (hbpos n), mul_comm]
        exact (hb n).le
      have hz0 : Tendsto (fun n => u ((z n : E))) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        exact squeeze_zero (fun n => norm_nonneg _) hzu tendsto_one_div_add_atTop_nhds_zero_nat
      obtain ⟨a, φ, hφ, ha⟩ := hS (fun n => (z n : E)) ⟨1, fun n => by
        rw [← hz1 n]; rfl⟩ 0 hz0
      have haE : a ∈ E₀ := hE₀.mem_of_tendsto ha (Eventually.of_forall fun n => (z (φ n)).2)
      have hna : ‖a‖ = 1 := by
        have := (continuous_norm.tendsto a).comp ha
        have h1 : (fun n => ‖((z (φ n) : E₀) : E)‖) = fun _ => (1 : ℝ) := by
          funext n; exact hz1 (φ n)
        have : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖a‖) := by
          rw [← h1]; exact this
        exact (tendsto_nhds_unique this tendsto_const_nhds)
      have hua : u a = 0 := by
        have h1 := (u.continuous.tendsto a).comp ha
        have h2 := hz0.comp hφ.tendsto_atTop
        exact tendsto_nhds_unique h1 h2
      have : (⟨a, haE⟩ : E₀) = 0 := hinj (by simpa [u₀] using hua)
      have : a = 0 := congrArg Subtype.val this
      rw [this, norm_zero] at hna
      exact zero_ne_one hna
    obtain ⟨K, hK⟩ := hbd
    have hK' : ∀ b : E₀, ‖b‖ ≤ (K.toNNReal : ℝ) * ‖u₀ b‖ := fun b =>
      (hK b).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (norm_nonneg _))
    have hcl := (u₀.isClosed_range_iff_antilipschitz_of_injective hinj).2
      ⟨_, u₀.antilipschitz_of_bound hK'⟩
    rwa [hrange] at hcl
