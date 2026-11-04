-- Prove2me | solution 1 for ChanceStateCtrl.PDE.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:43:57.904123+00:00
-- url     : https://prove2.me/submissions/032da405-4805-43d9-9f0e-aa3e987fd01a

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model
import Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_9

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise MatrixOrder
open ChanceStateCtrl.PDE

/-- `‖Σ^{1/2}‖ > 0` for a positive definite `Σ` of positive size. -/
private lemma sigmaRoot_norm_pos {m : ℕ} (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.PosDef) : 0 < ‖sigmaRoot Sigma‖ := by
  rw [norm_pos_iff]
  intro h0
  have hnn : 0 ≤ Sigma := hSigma.posSemidef.nonneg
  have hsq : CFC.sqrt Sigma = 0 := by
    have : Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sigma) = Matrix.toEuclideanCLM (𝕜 := ℝ) 0 := by
      rw [map_zero]; exact h0
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)).injective this
  have hS : Sigma = 0 := by
    rw [← CFC.sqrt_mul_sqrt_self Sigma hnn, hsq, zero_mul]
  have := hSigma.2 (x := Finsupp.single ⟨0, hm⟩ (1 : ℝ)) (Finsupp.single_ne_zero.2 one_ne_zero)
  rw [hS] at this
  simp at this

theorem solution {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    (ubar : L2 D) :
    ModerateGrowth (gPDE Ainv f₀ φ α) Sigma ubar := by
  -- global Lipschitz continuity of `g` (Lemma 2.9)
  obtain ⟨-, ⟨C, hLip⟩, -⟩ := lemma_2_9 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α
    (Ω := EuclideanSpace ℝ (Fin m)) id measurable_id
  have hLu : ∀ z u₁ u₂, |gPDE Ainv f₀ φ α u₁ z - gPDE Ainv f₀ φ α u₂ z| ≤ C * ‖u₁ - u₂‖ := by
    intro z u₁ u₂
    have := hLip.dist_le_mul (u₁, z) (u₂, z)
    simp only [Prod.dist_eq, dist_self, Function.uncurry_apply_pair, Real.dist_eq] at this
    rw [max_eq_left dist_nonneg, dist_eq_norm] at this
    exact this
  -- the Clarke derivative of `g(·, z)` is at most `C ‖h‖`
  have hdir : ∀ z u h, clarkeDir (fun u' => gPDE Ainv f₀ φ α u' z) u h ≤ C * ‖h‖ := by
    intro z u h
    have hpos : ∀ᶠ q : L2 D × ℝ in 𝓝 u ×ˢ 𝓝[>] (0 : ℝ), 0 < q.2 :=
      (tendsto_snd (f := 𝓝 u) (g := 𝓝[>] (0 : ℝ))).eventually self_mem_nhdsWithin
    have hb : ∀ᶠ q : L2 D × ℝ in 𝓝 u ×ˢ 𝓝[>] (0 : ℝ),
        |(gPDE Ainv f₀ φ α (q.1 + q.2 • h) z - gPDE Ainv f₀ φ α q.1 z) / q.2| ≤ C * ‖h‖ := by
      filter_upwards [hpos] with q hq
      have := hLu z (q.1 + q.2 • h) q.1
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hq.le] at this
      rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
      linarith
    refine limsup_le_of_le ?_ ?_
    · exact isCoboundedUnder_le_of_eventually_le _ (x := -(C * ‖h‖))
        (by filter_upwards [hb] with q hq; exact (abs_le.1 hq).1)
    · filter_upwards [hb] with q hq; exact (abs_le.1 hq).2
  -- choice of `l`
  set s := ‖sigmaRoot Sigma‖ with hs
  have hspos : 0 < s := sigmaRoot_norm_pos hm Sigma hSigma
  set A : ℝ := (2 * s ^ 2) ^ m * (m.factorial : ℝ) with hAdef
  have hApos : 0 < A := by positivity
  set l : ℝ := max 1 (C * A + 1) with hl
  have hl1 : 1 ≤ l := le_max_left _ _
  have hlCA : C * A + 1 ≤ l := le_max_right _ _
  refine ⟨l, by linarith, ?_⟩
  intro h u _ z hz
  refine (hdir z u h).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
  set r := ‖z‖ with hr
  have hr1 : 1 ≤ r := hl1.trans hz
  have hrpos : 0 < r := by linarith
  -- `exp x ≥ x^m / m!`
  have hexp : (r ^ 2 / (2 * s ^ 2)) ^ m / (m.factorial : ℝ) ≤ Real.exp (r ^ 2 / (2 * s ^ 2)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have hkey : (r ^ 2 / (2 * s ^ 2)) ^ m / (m.factorial : ℝ) = r ^ m * r ^ m / A := by
    rw [hAdef, div_pow, ← pow_mul, mul_comm 2 m, pow_mul', ← mul_pow]
    · field_simp
  rw [hkey] at hexp
  have hzpow : r ^ (-(m : ℤ)) = (r ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [hzpow]
  have hrm : 1 ≤ r ^ m := one_le_pow₀ hr1
  have hrmpos : 0 < r ^ m := by positivity
  calc (C : ℝ) ≤ l / A := by
          rw [le_div_iff₀ hApos]; nlinarith
    _ ≤ l * r ^ m / A := by
          apply div_le_div_of_nonneg_right _ hApos.le
          nlinarith
    _ = l * (r ^ m)⁻¹ * (r ^ m * r ^ m / A) := by
          field_simp
    _ ≤ l * (r ^ m)⁻¹ * Real.exp (r ^ 2 / (2 * s ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
