-- Prove2me | solution 1 for CompanionTheory.ThKF.E.Impl.scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:57.054843+00:00
-- url     : https://prove2.me/submissions/99fecb1c-3abd-490c-9bd6-6ae52d061e7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
import Theorems.Thm_CompanionTheory_ThKF_E_exists_rho
import Theorems.Thm_CompanionTheory_ThKF_E_toLp_rho
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_continuous
import Theorems.Thm_CompanionTheory_ThKF_E_exists_ne_zero
import Theorems.Thm_GlobalTheory_RealWeil_inner_toLp_rho


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
namespace Impl
theorem _root_.solution {S : Sch l →ₗ[ℂ] Sch l} (h : Impl id S) (hs : Function.Surjective S) : ∃ c : ℂ, ∀ f, S f = c • f := by
  have h1 : ∀ (φ f : Sch l) x, (starRingEnd ℂ) (S φ x) * S f x = (starRingEnd ℂ) (φ x) * f x := fun φ f x => by
    have key : ∀ (a b : Sch l) (q : EuclideanSpace ℝ l) (g : Sch l), ⇑g = rhoFun (Sum.elim 0 fun i => -q i) b →
        Inner.inner ℂ (a.toLp 2 volume) (g.toLp 2 volume) = 𝓕 (fun x => (starRingEnd ℂ) (a x) * b x) q := fun a b q g hg => by
      rw [toLp_rho hg, inner_toLp_rho, Real.fourier_eq']
      refine integral_congr_ae (.of_forall fun y => ?_)
      have e1 : pPart (l := l) (Sum.elim 0 fun i => -q i) = 0 := rfl
      have e2 : qPart (l := l) (Sum.elim 0 fun i => -q i) = -q := rfl
      simp only [rhoFun, phase, e1, e2, inner_zero_left, mul_zero, add_zero, inner_neg_left, smul_eq_mul, RCLike.inner_apply,
        real_inner_comm y q]
      push_cast
      ring_nf
    have hi : ∀ a b : Sch l, Integrable (fun x => (starRingEnd ℂ) (a x) * b x) ∧
        Continuous (fun x => (starRingEnd ℂ) (a x) * b x) := fun a b =>
      ⟨b.integrable.bdd_mul (c := SchwartzMap.seminorm ℂ 0 0 a) (continuous_conj.comp a.continuous).aestronglyMeasurable
        (.of_forall fun x => by simpa using a.norm_le_seminorm ℂ x), (continuous_conj.comp a.continuous).mul b.continuous⟩
    set u := fun x => (starRingEnd ℂ) (S φ x) * S f x - (starRingEnd ℂ) (φ x) * f x with hu
    have hz : 𝓕 u = 0 := by
      funext q
      obtain ⟨g, hg⟩ := exists_rho (Sum.elim 0 fun i => -q i) f
      have := h.inner φ g
      rw [key _ _ q _ (h.impl _ _ _ hg), key _ _ q _ hg, Real.fourier_eq', Real.fourier_eq'] at this
      rw [Real.fourier_eq', hu]
      simp only [smul_sub]
      have hb : ∀ a b : Sch l, Integrable fun v => cexp (((-2 * π * ⟪v, q⟫ : ℝ) : ℂ) * I) • ((starRingEnd ℂ) (a v) * b v) :=
        fun a b => (hi a b).1.bdd_mul (c := 1) (by fun_prop) (.of_forall fun v => (norm_exp_ofReal_mul_I _).le)
      rw [integral_sub (hb _ _) (hb _ _), this, sub_self]
      rfl
    have := Continuous.fourierInv_fourier_eq (f := u) ((hi _ _).2.sub (hi _ _).2) ((hi _ _).1.sub (hi _ _).1)
      (by rw [hz]; exact integrable_zero _ _ _)
    rw [hz] at this
    have h3 := congrFun this x
    rw [Real.fourierInv_eq] at h3
    simp only [Pi.zero_apply, smul_zero, integral_zero] at h3
    exact sub_eq_zero.1 h3.symm
  have h2 : ∀ x, ∃ m : ℂ, ∀ f : Sch l, S f x = m * f x := fun x => by
    obtain ⟨φ, hφ⟩ := exists_ne_zero x
    obtain ⟨φ', rfl⟩ := hs φ
    have hn : (starRingEnd ℂ) (S φ' x) ≠ 0 := by simpa using hφ
    refine ⟨(starRingEnd ℂ) (φ' x) / (starRingEnd ℂ) (S φ' x), fun f => ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff hn, mul_comm, h1]
  obtain ⟨m, hm⟩ := h2 0
  refine ⟨m, fun f => SchwartzMap.ext fun x => ?_⟩
  obtain ⟨g, hg⟩ := exists_rho (Sum.elim (fun i => x i) 0) f
  have e1 : pPart (l := l) (Sum.elim (fun i => x i) 0) = x := rfl
  have e2 : qPart (l := l) (Sum.elim (fun i => x i) 0) = 0 := rfl
  have := hm g
  rw [h.impl _ _ _ hg, hg] at this
  simpa [rhoFun, phase, e1, e2] using this
end Impl
end CompanionTheory.ThKF.E
