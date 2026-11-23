-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:07.035083+00:00
-- url     : https://prove2.me/submissions/1605cb1a-4df1-4661-9271-39a3ce248b31

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_det_Hm
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_GG_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_isUpUni
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_sUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_shape
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_isUnit_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_supp_Z
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_Phi_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_all
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_pos
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (hm : 1 ≤ m)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c D' : Kˣ)
    (htb : Sm R ϖ b (t : K)) (hDt : (D' : K) = (-1) ^ m * ((c : K) * (t : K) ^ m))
    (hQ : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q)
    (hmain : ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p, y p ∈ L₀) → (HH (t : K) (Fin.cons ρ x : Fin (m + 1) → K) y).det = (D' : K) →
      Sm R ϖ b (ρ - x0 (D' : K) x) ∧
      ∃ r ∈ R, ρ * ((t⁻¹ : Kˣ) : K) = x0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r)
    (N : Pr (m + 1) → K) (hG : pw_Good R ϖ L₀ a ((t : K) • N)) (ξ : Fin m → K) :
    Φ (m + 1) ((Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id) *
        ψ (lastE ξ + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        ((modK R (∏ k, xs ((t : K) • N) k) : ℝ) : ℂ) *
        GG R ψ Φ (D' : K) (xs ((t : K) • N))
          (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K))) := by
  have hsh := pw_shape hm (t : K) (c : K) ξ N
  set n := (t : K) • N with hn
  set x := xs n with hx
  set τ := pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K) with hτ
  set y := ys n τ with hy
  have hZ : (Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id =
      ZZ (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y := by rw [hsh]; rfl
  have hdet : (HH (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y).det = (D' : K) := by
    rw [← hsh, det_Hm _ _ _ _ (pw_isUpUni N), hDt]
  have hxu : ∀ k, IsUnit (x k) := fun k => (hG.1 k).2.1
  rw [hZ]
  by_cases hτL : ∀ j, τ j ∈ L₀
  · have hyL : ∀ p, y p ∈ L₀ := pw_ys_all n τ L₀ hG.2 hτL
    obtain ⟨h1, r, hr, h2⟩ := hmain _ x y hG.1 hyL hdet
    rw [pw_Phi_eq hC Φ hΦ (t : K) (D' : K) _ hQ x y hxu htb h1]
    have ht1 : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
    have hs : ∑ k, x k = (t : K) * ∑ k, N (sd k) := by
      rw [Finset.mul_sum]; rfl
    have e : lastE ξ + sUp (1 + EE N) =
        g0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r := by
      rw [pw_sUp]
      unfold g0
      rw [hs]
      unfold x0 at h2
      linear_combination h2 - (lastE ξ + ∑ k, N (sd k)) * ht1
    rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, psi_R hD hr, mul_one, GG, if_pos hxu]
    obtain ⟨P, hP⟩ := pw_isUnit_prod x hxu
    have hpos : (modK R (∏ k, x k) : ℝ) ≠ 0 := by
      rw [← hP]; exact (modK_pos hC.adic.isOpen hC.adic.isCompact P).ne'
    have hpos' : ((modK R (∏ k, x k) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
    push_cast
    field_simp
  · rw [not_forall] at hτL
    obtain ⟨j, hj⟩ := hτL
    have z1 : Φ (m + 1) (ZZ (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y) = 0 := by
      by_contra h
      have := (pw_supp_Z Φ hΦ _ _ _ h).2 ⟨(0, j.succ), Fin.succ_pos j⟩
      rw [hy, pw_ys_zero] at this
      exact hj this
    have z2 : GG R ψ Φ (D' : K) x y = 0 := by
      by_contra h
      have := (GG_supp hC Φ hΦ D' hQ x y h).2.1 ⟨(0, j.succ), Fin.succ_pos j⟩
      rw [hy, pw_ys_zero] at this
      exact hj this
    rw [z1, z2, zero_mul, mul_zero]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
