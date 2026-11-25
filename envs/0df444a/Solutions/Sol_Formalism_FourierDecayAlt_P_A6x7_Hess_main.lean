-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:11.743075+00:00
-- url     : https://prove2.me/submissions/b3a165d1-4e2e-4a05-bdd3-ad235c51e0a8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_gaussF_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_intK_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_product_bound_of_factor_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_real_rpow_mul_sq_half
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_hessM_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_gaussAdm_scale
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
theorem _root_.solution (hGM : GaussModulus) (hGI : GaussIndep) (hHD : HessDet) (hMM : ModMul)
    (hVS : VolScale) : GaussHess := by
  classical
  intro K _ _ _ R ψ hD hch m
  have hs : IsUnit (((m + 1 : ℕ) : K)) := hch (m + 1) (Nat.succ_ne_zero m)
  have hpos : ∀ x : Kˣ, 0 < modK R (x : K) := fun x => (hMM K R ψ hD x 1).1
  have hmul : ∀ x y : Kˣ, modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K) :=
    fun x y => (hMM K R ψ hD x y).2
  have hone : modK R (1 : K) = 1 := by
    have h1 := hmul 1 1
    have h2 := hpos 1
    simp only [Units.val_one, mul_one] at h1 h2
    have : modK R (1 : K) * (modK R (1 : K) - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2.ne'
    · linarith
  have hpow : ∀ (x : Kˣ) (n : ℕ), modK R ((x : K) ^ n) = modK R (x : K) ^ n := by
    intro x n
    induction n with
    | zero => simpa using hone
    | succ n ih =>
      have := hmul (x ^ n) x
      rw [Units.val_pow_eq_pow_val] at this
      rw [pow_succ, this, ih, pow_succ]
  have hinv : ∀ x : Kˣ, modK R ((x⁻¹ : Kˣ) : K) = (modK R (x : K))⁻¹ := by
    intro x
    have := hmul x x⁻¹
    rw [Units.mul_inv, hone] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hspos : 0 < modK R (((m + 1 : ℕ) : K)) := hpos hs.unit
  have hdetU : ∀ a : Kˣ, IsUnit (hessM m a).det := by
    intro a
    rw [hHD K m a]
    exact hs.mul ((a⁻¹).isUnit.pow m)
  set N : Kˣ → ℝ := fun a =>
    modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (a : K) ^ ((m : ℝ) / 2) with hN
  have hNpos : ∀ a, 0 < N a := fun a =>
    mul_pos (Real.rpow_pos_of_pos hspos _) (Real.rpow_pos_of_pos (hpos a) _)
  have hdetN : ∀ a : Kˣ, modK R (hessM m a).det ^ (-(1 : ℝ) / 2) = N a := by
    intro a
    have h1 := hmul hs.unit ((a⁻¹) ^ m)
    rw [Units.val_pow_eq_pow_val, hpow, hinv] at h1
    rw [hHD K m a]
    have h2 : (hs.unit : K) = ((m + 1 : ℕ) : K) := rfl
    rw [h2] at h1
    rw [h1, product_bound_of_factor_bounds _ _ hspos (hpos a)]
  set P : Kˣ → AddSubgroup K × AddSubgroup K → Prop := fun a p =>
    IsLat p.1 ∧ IsLat p.2 ∧ GaussAdm ψ p.1 (hessM m a) ∧
      LatInvN p.2 (gaussF ψ p.1 (hessM m a)) with hP
  set γ : Kˣ → ℂ := fun a =>
    if h : ∃ p, P a p then
      intK R h.choose.2 m (gaussF ψ h.choose.1 (hessM m a)) / ((N a : ℝ) : ℂ) else 1 with hγ
  have hNC : ∀ a, ((N a : ℝ) : ℂ) ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (hNpos a).ne'
  have key : ∀ (a : Kˣ) (p : AddSubgroup K × AddSubgroup K), P a p →
      intK R p.2 m (gaussF ψ p.1 (hessM m a)) = γ a * ((N a : ℝ) : ℂ) := by
    intro a p hp
    have hex : ∃ p, P a p := ⟨p, hp⟩
    have hc := hex.choose_spec
    have hγa : γ a = intK R hex.choose.2 m (gaussF ψ hex.choose.1 (hessM m a)) / ((N a : ℝ) : ℂ) := by
      simp only [hγ]
      rw [dif_pos hex]
    rw [hγa, div_mul_cancel₀ _ (hNC a)]
    exact hGI K R ψ hD hch m (hessM m a) (hessM_symm m a) (hdetU a) p.1 p.2 hex.choose.1
      hex.choose.2 hp.1 hp.2.1 hc.1 hc.2.1 hp.2.2.1 hp.2.2.2 hc.2.2.1 hc.2.2.2
  have hscale : ∀ (a b : Kˣ) (p : AddSubgroup K × AddSubgroup K), P a p →
      P (a * b ^ 2) (mulLat (b : K) p.1, mulLat (b : K) p.2) ∧
      intK R (mulLat (b : K) p.2) m (gaussF ψ (mulLat (b : K) p.1) (hessM m (a * b ^ 2))) =
        ((modK R (b : K) : ℝ) : ℂ) ^ m * intK R p.2 m (gaussF ψ p.1 (hessM m a)) := by
    intro a b p hp
    have h1 := hVS K R ψ hD b p.1 hp.1
    have h2 := hVS K R ψ hD b p.2 hp.2.1
    have h3 := intK_scale R b p.2 h2.2 (gaussF ψ p.1 (hessM m a))
      (gaussF ψ (mulLat (b : K) p.1) (hessM m (a * b ^ 2)))
      (fun ξ => gaussF_scale ψ p.1 m a b ξ) hp.2.2.2
    exact ⟨⟨h1.1, h2.1, gaussAdm_scale ψ p.1 m a b (hdetU a) hp.2.2.1, h3.1⟩, h3.2⟩
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro a
    by_cases hex : ∃ p, P a p
    · obtain ⟨p, hp⟩ := hex
      have h1 := key a p hp
      have h2 := hGM K R ψ hD hch m (hessM m a) (hessM_symm m a) (hdetU a) p.1 p.2 hp.1 hp.2.1
        hp.2.2.1 hp.2.2.2
      rw [h1, hdetN a, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hNpos a).le] at h2
      exact mul_right_cancel₀ (hNpos a).ne' (h2.trans (one_mul _).symm)
    · simp only [hγ]
      rw [dif_neg hex, norm_one]
  · intro a b
    have hNab : N (a * b ^ 2) = N a * modK R (b : K) ^ m := by
      simp only [hN]
      have : modK R ((a * b ^ 2 : Kˣ) : K) = modK R (a : K) * modK R (b : K) ^ 2 := by
        rw [Units.val_mul, hmul, Units.val_pow_eq_pow_val, hpow]
      rw [this, real_rpow_mul_sq_half _ _ (hpos a) (hpos b), mul_assoc]
    by_cases hex : ∃ p, P a p
    · obtain ⟨p, hp⟩ := hex
      obtain ⟨h1, h2⟩ := hscale a b p hp
      have h3 := key _ _ h1
      have h4 := key a p hp
      simp only at h3
      rw [h2, h4, hNab] at h3
      have hb : ((modK R (b : K) : ℝ) : ℂ) ^ m ≠ 0 :=
        pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hpos b).ne')
      push_cast at h3
      have h5 : γ a * (((N a : ℝ) : ℂ) * ((modK R (b : K) : ℝ) : ℂ) ^ m) =
          γ (a * b ^ 2) * (((N a : ℝ) : ℂ) * ((modK R (b : K) : ℝ) : ℂ) ^ m) := by
        rw [← h3]; ring
      exact (mul_right_cancel₀ (mul_ne_zero (hNC a) hb) h5).symm
    · have hex' : ¬ ∃ p, P (a * b ^ 2) p := by
        rintro ⟨p, hp⟩
        apply hex
        have h1 := (hscale (a * b ^ 2) b⁻¹ p hp).1
        have h2 : a * b ^ 2 * b⁻¹ ^ 2 = a := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
        rw [h2] at h1
        exact ⟨_, h1⟩
      simp only [hγ]
      rw [dif_neg hex, dif_neg hex']
  · intro a L Λ hL hΛ hA hI
    exact key a (L, Λ) ⟨hL, hΛ, hA, hI⟩
end Formalism.FourierDecayAlt.P.A6x7.Hess
