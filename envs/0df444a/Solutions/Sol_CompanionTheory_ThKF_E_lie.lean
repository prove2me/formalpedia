-- Prove2me | solution 1 for CompanionTheory.ThKF.E.lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:20.626197+00:00
-- url     : https://prove2.me/submissions/74f6d741-6a6b-4f58-83f9-fc5cc620bf6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
import Theorems.Thm_CompanionTheory_ThKF_E_exists_exp
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_continuous
import Theorems.Thm_CompanionTheory_ThKF_E_exists_ne_zero
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_scalar
import Theorems.Thm_CompanionTheory_ThKF_E_sympl_eq
import Theorems.Thm_CompanionTheory_ThKF_E_exists_lift
import Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_exp_apply
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKF CompanionTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKF.E
theorem _root_.solution (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hS : ∀ t, Impl (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlg l, ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by
  have hm : ∃ X : Matrix (l ⊕ l) (l ⊕ l) ℝ, ∀ t, LinearMap.toMatrix' (s t) = NormedSpace.exp (t • X) := by
    letI := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
    haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
    refine exists_exp (fun t => LinearMap.toMatrix' (s t)) ?_ ?_ fun t u => ?_
    · refine continuous_matrix fun a b => ?_
      simp only [LinearMap.toMatrix'_apply]
      exact (continuous_apply a).comp (sc _)
    · rw [show s 0 = LinearMap.id from LinearMap.ext s0, LinearMap.toMatrix'_id]
    · rw [show s (t + u) = s t ∘ₗ s u from LinearMap.ext (sm t u), LinearMap.toMatrix'_comp]
  obtain ⟨X, hX⟩ := hm
  have hs : ∀ t w, s t w = NormedSpace.exp (t • X) *ᵥ w := fun t w => by rw [← hX, LinearMap.toMatrix'_mulVec]
  have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
    refine (mem_skewAdjointMatricesLieSubalgebra _ _).2 ((mem_skewAdjointMatricesSubmodule _ _).2 ?_)
    show Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X)
    ext a b
    have h1 : ∀ t : ℝ, ∑ i, ∑ j, NormedSpace.exp (t • X) i a * (Matrix.J l ℝ i j * NormedSpace.exp (t • X) j b) =
        Matrix.J l ℝ a b := fun t => by
      have := ss t (Pi.single a 1) (Pi.single b 1)
      rw [sympl_eq, sympl_eq, neg_inj, hs, hs] at this
      simpa [dotProduct, mulVec, Finset.mul_sum, Pi.single_apply, mul_add] using this
    have h2 : HasDerivAt (fun t : ℝ => ∑ i, ∑ j, NormedSpace.exp (t • X) i a *
        (Matrix.J l ℝ i j * NormedSpace.exp (t • X) j b)) _ 0 :=
      HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
        (hasDerivAt_exp_apply X i a).fun_mul ((hasDerivAt_exp_apply X j b).const_mul _)
    simp only [h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    simp only [zero_smul, NormedSpace.exp_zero, Finset.sum_add_distrib, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul,
      mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero] at h3
    simp only [Matrix.mul_apply, transpose_apply, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
    linarith
  obtain ⟨U, Q, hQ, U0, Um, Ui, Uc, Ud⟩ := exists_lift hP hsp
  have hc : ∀ t, ∃ c : ℂ, ∀ f, S t f = c • U t f := fun t => by
    have hi : Impl id (S t ∘ₗ (U (-t)).toLinearMap) := ⟨fun f => ((hS t).norm _).trans ((Ui (-t)).norm f), fun w f g hg => by
      have := (hS t).impl _ _ _ ((Ui (-t)).impl w f g hg)
      rw [← hs, ← sm, add_neg_cancel, s0] at this
      exact this⟩
    obtain ⟨c, hc⟩ := hi.scalar fun f => ⟨U t (S (-t) f), by
      show S t (U (-t) (U t _)) = f
      rw [← Um, neg_add_cancel, U0, ← Sm, add_neg_cancel, S0]⟩
    refine ⟨c, fun f => ?_⟩
    rw [← hc]
    show _ = S t (U (-t) (U t f))
    rw [← Um, neg_add_cancel, U0]
  choose c hc using hc
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have hφ0 : φ ≠ 0 := fun h => hφ (by simp [h])
  have hU : ∀ t, U t φ ≠ 0 := fun t h => hφ0 (by rw [← U0 φ, ← neg_add_cancel t, Um, h, map_zero])
  have c0 : c 0 = 1 := by
    have := hc 0 φ
    rw [S0, U0] at this
    exact (smul_left_injective ℂ hφ0 (this.symm.trans (one_smul _ _).symm))
  have cm : ∀ t u, c (t + u) = c t * c u := fun t u => by
    have := Sm t u φ
    rw [hc, hc, hc, map_smul, smul_smul, ← Um] at this
    exact smul_left_injective ℂ (hU _) this
  have cc : Continuous c := continuous_iff_continuousAt.2 fun t₀ => by
    let lam : Sch l →L[ℂ] ℂ := (innerSL ℂ ((U t₀ φ).toLp 2 volume)).comp (schwartzToL2 l)
    have h1 : Continuous fun t => lam (U t φ) := (innerSL ℂ ((U t₀ φ).toLp 2 volume)).continuous.comp (Uc φ)
    have h2 : lam (U t₀ φ) ≠ 0 := fun h => hU t₀ (by
      apply injective_toLp 2 volume
      have : (U t₀ φ).toLp 2 volume = 0 := inner_self_eq_zero.1 h
      exact this.trans (map_zero (schwartzToL2 l)).symm)
    refine ((Sc φ lam).continuousAt.div h1.continuousAt h2).congr ?_
    filter_upwards [h1.continuousAt.eventually_ne h2] with t ht
    simp only [Pi.div_apply, hc, map_smul, smul_eq_mul]
    rw [mul_div_cancel_right₀ _ ht]
  obtain ⟨z, hz⟩ := exists_exp c cc c0 cm
  have hd : HasDerivAt c z 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) z (0 : ℝ)
    simp only [← hz, c0, one_mul] at this
    exact this
  refine ⟨z • 1 + Q, add_mem (Subalgebra.smul_mem _ (one_mem _) _) hQ, fun f lam => ?_⟩
  simp only [hc, map_smul, smul_eq_mul]
  refine (hd.fun_mul (Ud f lam)).congr_deriv ?_
  simp [c0, U0]
end CompanionTheory.ThKF.E
