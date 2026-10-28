-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_forall_cutoff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:04.060508+00:00
-- url     : https://prove2.me/submissions/e0aa2aad-8779-493d-84a6-016851dfe1d9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Approximation
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_contDiff_readable

section
noncomputable section
open MeasureTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Weak derivatives are unique almost everywhere. -/
theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.ae_eq {f g₁ g₂ : E → ℝ} {v : E} (h₁ : HasWeakDerivAlong f g₁ v)
    (h₂ : HasWeakDerivAlong f g₂ v) : g₁ =ᵐ[(volume : Measure E)] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq h₁.2.1 h₂.2.1
  intro ψ hψ hψc
  have hψ' : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have e₁ := h₁.2.2 ψ hψ' hψc
  have e₂ := h₂.2.2 ψ hψ' hψc
  have e : (∫ x, g₁ x * ψ x ∂(volume : Measure E)) =
      ∫ x, g₂ x * ψ x ∂(volume : Measure E) := by
    linarith
  simpa only [smul_eq_mul, mul_comm] using e
end
universe u
end
end

noncomputable section
open MeasureTheory
open scoped ContDiff
section LN11C2WeakDerivativeGluing
open MeasureTheory Set Filter Metric
open scoped Topology
/-- **Gluing local weak derivatives** (weak Letwin route, generic): if for every `C¹` cutoff `χ` with
compact support the product `χ f` has a weak derivative along `v` that is locally `L²`, then `f` itself has a weak
derivative along `v` that is `L²` on every compact set. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ∀ S : Set E, IsCompact S → MemLp f 2 ((volume : Measure E).restrict S)) (v : E)
    (hloc : ∀ χ : E → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
      ∃ g : E → ℝ, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => χ x * f x) g v ∧ MemLp g 2 (volume : Measure E)) :
    ∃ g : E → ℝ, FunctionalInequalities.Analysis.HasWeakDerivAlong f g v ∧
      ∀ S : Set E, IsCompact S → MemLp g 2 ((volume : Measure E).restrict S) := by
  classical
  have compact_bound : ∀ S : Set E, IsCompact S →
      ∃ n : ℕ, ∀ x ∈ S, ‖x‖ < (n : ℝ) + 1 := by
    intro S hS
    obtain ⟨r, hr⟩ := hS.isBounded.subset_ball (0 : E)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨n, ?_⟩
    intro x hx
    have hxr : ‖x‖ < r := by
      simpa only [mem_ball, dist_zero_right] using hr hx
    exact hxr.trans (hn.trans (lt_add_one _))
  have local_integrability : ∀ u : E → ℝ,
      (∀ S : Set E, IsCompact S → MemLp u 2 ((volume : Measure E).restrict S)) →
      LocallyIntegrable u (volume : Measure E) := by
    intro u hu
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure ((volume : Measure E).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hu S hS).integrable (by norm_num)
  let χ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  have hχ_one : ∀ (n : ℕ) (x : E), ‖x‖ < (n : ℝ) + 1 → χ n x = 1 := by
    intro n x hx
    apply (χ n).one_of_mem_closedBall
    change dist x 0 ≤ (n : ℝ) + 1
    rw [dist_zero_right]
    exact hx.le
  have hχ_deriv : ∀ (n : ℕ) (x : E), ‖x‖ < (n : ℝ) + 1 →
      fderiv ℝ (χ n : E → ℝ) x = 0 := by
    intro n x hx
    have he : (χ n : E → ℝ) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      have hxball : x ∈ ball (0 : E) ((n : ℝ) + 1) := by
        simpa only [mem_ball, dist_zero_right] using hx
      filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
      apply hχ_one n y
      simpa only [mem_ball, dist_zero_right] using hy
    exact he.fderiv_eq.trans
      (congrFun (fderiv_const (𝕜 := ℝ) (E := E) (1 : ℝ)) x)
  have hex : ∀ n : ℕ, ∃ G : E → ℝ,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => χ n x * f x) G v ∧
        MemLp G 2 (volume : Measure E) := by
    intro n
    exact hloc (χ n) (χ n).contDiff (χ n).hasCompactSupport
  choose G hG hGL using hex
  have consistency : ∀ m n : ℕ, ∀ᵐ x ∂(volume : Measure E),
      ‖x‖ < (m : ℝ) + 1 → ‖x‖ < (n : ℝ) + 1 → G m x = G n x := by
    intro m n
    have H := (hG m).mul_contDiff_readable (χ n).contDiff (χ n).hasCompactSupport
    have K := (hG n).mul_contDiff_readable (χ m).contDiff (χ m).hasCompactSupport
    have e : (fun x => χ n x * (χ m x * f x)) =
        (fun x => χ m x * (χ n x * f x)) := by
      funext x
      ring
    rw [e] at H
    have he := H.ae_eq K
    filter_upwards [he] with x hx
    intro hm hn
    simpa only [hχ_one m x hm, hχ_one n x hn,
      hχ_deriv m x hm, hχ_deriv n x hn,
      zero_apply, one_mul, zero_mul, add_zero] using hx
  let g : E → ℝ := fun x => G ⌈‖x‖⌉₊ x
  have agreement : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure E),
      ‖x‖ < (n : ℝ) + 1 → g x = G n x := by
    have hall : ∀ᵐ x ∂(volume : Measure E), ∀ m n : ℕ,
        ‖x‖ < (m : ℝ) + 1 → ‖x‖ < (n : ℝ) + 1 → G m x = G n x :=
      ae_all_iff.mpr (fun m => ae_all_iff.mpr (consistency m))
    intro n
    filter_upwards [hall] with x hx
    intro hxn
    exact hx ⌈‖x‖⌉₊ n
      (lt_of_le_of_lt (Nat.le_ceil ‖x‖) (lt_add_one _)) hxn
  have hgL : ∀ S : Set E, IsCompact S →
      MemLp g 2 ((volume : Measure E).restrict S) := by
    intro S hS
    obtain ⟨n, hn⟩ := compact_bound S hS
    have he : g =ᵐ[(volume : Measure E).restrict S] G n := by
      apply (ae_restrict_iff' hS.measurableSet).mpr
      filter_upwards [agreement n] with x hx
      exact fun hxS => hx (hn x hxS)
    exact (memLp_congr_ae he).mpr ((hGL n).restrict S)
  refine ⟨g, ⟨local_integrability f hf, local_integrability g hgL, ?_⟩, hgL⟩
  intro ψ hψ hψc
  obtain ⟨n, hn⟩ := compact_bound (tsupport ψ) hψc.isCompact
  have hleft : (fun x => f x * fderiv ℝ ψ x v) =
      (fun x => (χ n x * f x) * fderiv ℝ ψ x v) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [hχ_one n x (hn x hx), one_mul]
    · have hz : fderiv ℝ ψ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
      simp only [hz, zero_apply, mul_zero]
  have hright : (fun x => G n x * ψ x) =ᵐ[(volume : Measure E)]
      (fun x => g x * ψ x) := by
    filter_upwards [agreement n] with x hx
    by_cases hs : x ∈ tsupport ψ
    · rw [hx (hn x hs)]
    · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
  calc
    (∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, (χ n x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E) :=
      congrArg (fun u : E → ℝ => ∫ x, u x ∂(volume : Measure E)) hleft
    _ = -∫ x, G n x * ψ x ∂(volume : Measure E) :=
      (hG n).2.2 ψ hψ hψc
    _ = -∫ x, g x * ψ x ∂(volume : Measure E) :=
      congrArg Neg.neg (integral_congr_ae hright)
