-- Prove2me | solution 1 for Formalism.L2.Th1.H.cayley_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:42.449801+00:00
-- url     : https://prove2.me/submissions/594625c2-2533-4b9c-b1e8-929ec648ac2c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
import Theorems.Thm_Formalism_L2_Th1_H_symm_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (Ae : V ≃ₗ[ℂ] V)
    (hA : ∀ u v, H (Ae u) v + H u (Ae v) = H (Ae u) (Ae v)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (l : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ (∀ i, Ae (b i) = l i • b i) ∧ ∀ i, 0 < (l i).re := by
  set B : V →ₗ[ℂ] V := (Ae.symm : V ≃ₗ[ℂ] V).toLinearMap with hBdef
  have key : ∀ x y, H (B x) y + H x (B y) = H x y := by
    intro x y
    have h := hA (Ae.symm x) (Ae.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    simpa [hBdef, add_comm] using h
  set T : V →ₗ[ℂ] V := Complex.I • ((2 : ℂ) • B - LinearMap.id) with hTdef
  have hTx : ∀ x, T x = Complex.I • ((2 : ℂ) • B x - x) := by
    intro x; simp [hTdef]
  have hT : ∀ x y, H (T x) y = H x (T y) := by
    intro x y
    rw [hTx, hTx]
    simp only [map_smul, map_sub, map_smulₛₗ, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul,
      Complex.conj_I, RingHom.id_apply, map_ofNat]
    linear_combination (2 * Complex.I) * key x y
  obtain ⟨b, t, hb, hbt⟩ := symm_diag H hH hP T hT
  have hne : ∀ i, (1 - Complex.I * (t i : ℂ)) ≠ 0 := by
    intro i h
    have := congrArg Complex.re h
    simp at this
  refine ⟨b, fun i => 2 / (1 - Complex.I * (t i : ℂ)), hb, ?_, ?_⟩
  · intro i
    have h1 := hbt i
    rw [hTx] at h1
    have hw : B (b i) = ((1 - Complex.I * (t i : ℂ)) / 2) • b i := by
      linear_combination (norm := skip) (-Complex.I / 2) • h1
      match_scalars <;> (ring_nf; simp only [Complex.I_sq]; ring)
    apply Ae.symm.injective
    have hB' : Ae.symm (b i) = B (b i) := rfl
    rw [LinearEquiv.symm_apply_apply, map_smul, hB', hw, smul_smul,
      show 2 / (1 - Complex.I * (t i : ℂ)) * ((1 - Complex.I * (t i : ℂ)) / 2) = 1 by
        field_simp [hne i], one_smul]
  · intro i
    have hre : (1 - Complex.I * (t i : ℂ)).re = 1 := by simp
    have him : (1 - Complex.I * (t i : ℂ)).im = -t i := by simp
    have hns : Complex.normSq (1 - Complex.I * (t i : ℂ)) = 1 + t i ^ 2 := by
      rw [Complex.normSq_apply, hre, him]; ring
    have h2r : (2 : ℂ).re = 2 := by norm_num
    have h2i : (2 : ℂ).im = 0 := by norm_num
    rw [Complex.div_re, hre, him, hns, h2r, h2i, zero_mul, zero_div, add_zero, mul_one]
    positivity
end Formalism.L2.Th1.H
