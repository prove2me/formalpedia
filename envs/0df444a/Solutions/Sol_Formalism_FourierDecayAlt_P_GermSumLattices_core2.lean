-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.core2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.026806+00:00
-- url     : https://prove2.me/submissions/50ad2600-d71c-4b5a-915c-cef2ad6e6f77

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_double_germ
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_root
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_root_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_neg_half_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_tri_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_coef_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_nsK_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_amp_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_back

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
open Classical
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (hMM : MM R) (hun : ∀ x : K, conj (ψ x) = ψ (-x)) (hψR : ∀ r ∈ R, ψ r = 1)
    (hs : IsUnit ((m + 1 : ℕ) : K)) (hγ1 : ∀ a, ‖γ a‖ = 1)
    (hγ2 : ∀ a b : Kˣ, γ (a * b ^ 2) = γ a)
    (h h' : Point K) (t₁ t₂ κ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S Om : Set K)
    (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hSfin : {x | (cr x : K) ∈ S}.Finite)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hG1 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h m t₁ (cr x)) w' =
      germSum R ψ m γ t₁ (cr x) (fun z => Kp R ψ (addBlock h (m + 1) z) w'))
    (hG2 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h' m t₂ (cr x)) w' =
      germSum R ψ m γ t₂ (cr x) (fun z => Kp R ψ (addBlock h' (m + 1) z) w'))
    (hκ : κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m)
    (hT : modK R (t₂ : K) = modK R (t₁ : K))
    (b : Kˣ) (hb : κ * t₂ * t₁⁻¹ = b ^ 2)
    (hmem : ∀ x, (cr x : K) ∈ S → ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * cr x → (z : K) ∈ Om)
    (hμOm : ∀ z ∈ Om, ∀ ζ ∈ μ, (ζ : K) * z ∈ Om)
    (hLCκ : ∀ z : Kˣ, (z : K) ∈ Om → ∀ w', Kp R ψ (addBlock h' (m + 1) (κ * z)) w' =
      Kp R ψ (addBlock h' (m + 1) z) w')
    (d : K) (hphase : ∀ z ∈ Om, ((m + 1 : ℕ) : K) * z * ((t₁⁻¹ : Kˣ) : K) -
      ((m + 1 : ℕ) : K) * ((κ : K) * z) * ((t₂⁻¹ : Kˣ) : K) - z * d ∈ R)
    (hX : ∀ ζ ∈ μ, ζ ≠ 1 → ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ S then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t₁) ^ m * cr x then
          amp R ψ m γ h h' t₁ ζ (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * ((ζ : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) else 0
        else 0) = 0)
    (I : ℂ)
    (hCV : ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ S then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t₁) ^ m * cr x then f1 R ψ m h h' d (z : K) else 0
        else 0) =
      (((modK R (t₁ : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) : ℝ) : ℂ) *
        ((((modK R ((m + 1 : ℕ) : K))⁻¹ : ℝ) : ℂ) * I)) :
    uGram R ψ m cr S h h' t₁ t₂ = I := by
  have hS : 0 < modK R ((m + 1 : ℕ) : K) := by
    obtain ⟨u, hu⟩ := hs
    rw [← hu]
    exact (hMM u u).1
  have hTp : 0 < modK R (t₁ : K) := (hMM t₁ t₁).1
  have h1μ : (1 : Kˣ) ∈ μ := (hμ 1).2 (one_pow _)
  have hNκ : modK R (κ : K) = 1 := by
    apply mm_root hMM κ m
    rw [← mm_pow hMM, ← Units.val_pow_eq_pow_val, hκ, Units.val_pow_eq_pow_val, mm_pow hMM,
      Units.val_mul, (hMM _ _).2, mm_inv hMM, hT, mul_inv_cancel₀ hTp.ne', one_pow]
  rw [double_germ R ψ m γ h h' t₁ t₂ κ cr S μ hμ hSfin hroots hherm hG1 hG2 hκ]
  have hterm : ∀ ζ ∈ μ, ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        germCoef R ψ m γ t₁ z * conj (germCoef R ψ m γ t₂ (ζ * κ * z)) *
          Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * κ * z)) =
      ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        amp R ψ m γ h h' t₁ ζ (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * ((ζ : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) := by
    intro ζ hζ
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro z hz
    have hzOm : (z : K) ∈ Om := hmem x (by simpa using hx) z (by simpa using hz)
    have hNζ : modK R (ζ : K) = 1 := mm_root_one hMM ζ m ((hμ ζ).1 hζ)
    have hN : modK R ((ζ * κ * z : Kˣ) : K) = modK R (z : K) := by
      rw [Units.val_mul, (hMM _ _).2, Units.val_mul, (hMM _ _).2, hNζ, hNκ, one_mul, one_mul]
    rw [coef_mul R ψ m γ hMM hun hs t₁ t₂ z (ζ * κ * z) hN, amp_unit]
    have e1 : γ (ζ * κ * z * t₂) = γ (ζ * z * t₁) := by
      have e : ζ * κ * z * t₂ = ζ * z * t₁ * b ^ 2 := by
        rw [← hb]
        have e' : ζ * z * t₁ * (κ * t₂ * t₁⁻¹) = ζ * κ * z * t₂ * (t₁ * t₁⁻¹) := by ac_rfl
        rw [e', mul_inv_cancel, mul_one]
      rw [e, hγ2]
    have e2 : Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * κ * z)) =
        Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * z)) := by
      rw [hherm, show ζ * κ * z = κ * (ζ * z) by ac_rfl,
        hLCκ (ζ * z) (by rw [Units.val_mul]; exact hμOm _ hzOm ζ hζ), ← hherm]
    rw [e1, e2]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem 1 h1μ (fun ζ hζ hne => by
    rw [← back R m t₁ hSfin hroots]
    exact hX ζ hζ hne)]
  have hdiag : ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        amp R ψ m γ h h' t₁ 1 (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * (((1 : Kˣ) : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) =
      ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        f1 R ψ m h h' d (z : K) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro z hz
    have hzOm : (z : K) ∈ Om := hmem x (by simpa using hx) z (by simpa using hz)
    have hNz : 0 < modK R (z : K) := (hMM z z).1
    rw [amp_unit, one_mul, Units.val_one, one_mul]
    have e1 : γ (z * t₁) * conj (γ (z * t₁)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hγ1]
      simp
    have e2 : ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
        ((m + 1 : ℕ) : K) * ((κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) = ψ ((z : K) * d) := by
      have e := hψR _ (hphase _ hzOm)
      rw [← sub_add_cancel (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
        ((m + 1 : ℕ) : K) * ((κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) ((z : K) * d),
        AddChar.map_add_eq_mul, e, one_mul]
    have e3 : (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) =
        (((modK R ((m + 1 : ℕ) : K))⁻¹ * (modK R (z : K) ^ m)⁻¹ : ℝ) : ℂ) *
          ((modK R (z : K) ^ (m ^ 2 + m) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [pow_add]
      field_simp
    rw [e1, e2, f1, nsK_unit R ψ m hMM, e3]
    ring
  rw [hdiag, ← back R m t₁ hSfin hroots, hCV, (hMM t₁ t₂).2, hT]
  have hP : (modK R (t₁ : K) * modK R (t₁ : K)) ^ (m * (m + 1) / 2) *
      (modK R (t₁ : K) ^ (-((m : ℝ) ^ 2) / 2) * modK R (t₁ : K) ^ (-((m : ℝ) ^ 2) / 2)) *
      ((modK R (t₁ : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K)) * (modK R ((m + 1 : ℕ) : K))⁻¹ = 1 := by
    rw [tri_pow, neg_half_sq _ hTp, pow_add]
    field_simp
  have hP' := congrArg (fun r : ℝ => (r : ℂ)) hP
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at hP' ⊢
  linear_combination I * hP'
end Formalism.FourierDecayAlt.P.GermSumLattices
