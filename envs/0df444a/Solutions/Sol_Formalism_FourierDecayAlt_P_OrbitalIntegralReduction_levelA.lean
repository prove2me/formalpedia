-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.levelA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:39.628975+00:00
-- url     : https://prove2.me/submissions/c1dec384-1fc6-4d8e-b1a0-4809658d09ba

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_det_Hm
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_GG_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_units
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_main
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_isUpUni
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_indep
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_shape
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_det_rev
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_psi_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_mul_finsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_isUnit_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_term_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_supp_Z
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_point
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_neg
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
theorem _root_.solution (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (hL₀ : IsLat L₀) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ M : ℕ, ∀ Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ, PhiHyp R (m + 1) L₀ Λ₀ Q Φ →
    ∀ t c D' : Kˣ, Sm R ϖ M (t : K) → (D' : K) = (-1) ^ m * ((c : K) * (t : K) ^ m) →
    ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) →
    ∀ Λ₁ : AddSubgroup K, IsLat Λ₁ → (∀ x : Fin m → K, BInv Λ₁ (GG R ψ Φ (D' : K) x)) →
    ∀ N : Pr (m + 1) → K,
      ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (1 + EE N)).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        bx R Λ₁ (Fin m) (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)) := by
  obtain ⟨M₁, h₁⟩ := pw_units hC m
  obtain ⟨M₂, h₂⟩ := pw_main hC m hm
  obtain ⟨M₃, h₃⟩ := pw_det hC m
  refine ⟨M₁ + M₂ + M₃ + b, ?_⟩
  intro Φ hΦ t c D' ht hDt hQ Λ₁ hΛ₁ hGinv N
  have hϖ := hC.adic.mem
  have ht1 : Sm R ϖ M₁ (t : K) := ht.mono hϖ (by omega)
  have ht2 : Sm R ϖ M₂ (t : K) := ht.mono hϖ (by omega)
  have ht3 : Sm R ϖ M₃ (t : K) := ht.mono hϖ (by omega)
  have htb : Sm R ϖ b (t : K) := ht.mono hϖ (by omega)
  by_cases hG : pw_Good R ϖ L₀ a ((t : K) • N)
  · have hpt := pw_point hD hC hm Φ hΦ t c D' htb hDt hQ (h₂ t ht2 D' hQ) N hG
    have hsh := pw_shape hm (t : K) (c : K) 0 N
    obtain ⟨hu, hmod⟩ := h₃ (t : K) ht3 ((t : K) * lastE (0 : Fin m → K)) (xs ((t : K) • N))
      (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ 0 + pw_bv (c : K))) hG.1
      (fun p hp => by rw [pw_ys_indep _ _ 0 p hp]; exact hG.2 p hp)
    rw [← hsh] at hu hmod
    have hMx : pw_Mx (t : K) (1 + EE N) =
        (((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ).submatrix Fin.rev id)ᵀ := by
      ext j k
      simp [pw_Mx, Hm]
    have hMu : IsUnit (pw_Mx (t : K) (1 + EE N)).det := by
      rw [hMx, Matrix.det_transpose]
      rcases pw_det_rev ((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ) with e | e
      · rw [e]; exact hu
      · rw [e]; exact hu.neg
    have hMm : modK R (pw_Mx (t : K) (1 + EE N)).det = modK R (∏ k, xs ((t : K) • N) k) := by
      rw [hMx, Matrix.det_transpose]
      rcases pw_det_rev ((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ) with e | e
      · rw [e]; exact hmod
      · rw [e, modK_neg]; exact hmod
    obtain ⟨P, hP⟩ := pw_isUnit_prod (xs ((t : K) • N)) (fun k => (hG.1 k).2.1)
    have hpos : ((modK R (∏ k, xs ((t : K) • N) k) : ℝ) : ℂ) ≠ 0 := by
      have : (modK R (∏ k, xs ((t : K) • N) k) : ℝ) ≠ 0 := by
        rw [← hP]; exact (modK_pos hC.adic.isOpen hC.adic.isCompact P).ne'
      exact_mod_cast this
    have hinv : BInv Λ₁ (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)) := by
      intro τ l hl
      show GG R ψ Φ (D' : K) _ (ys ((t : K) • N) (τ + l)) = _
      rw [pw_ys_add]
      exact hGinv _ _ _ (pw_ys_mem Λ₁ l hl)
    have hs : BSupp L₀ (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)) := by
      intro τ h j
      have := (GG_supp hC Φ hΦ D' hQ _ _ h).2.1 ⟨(0, j.succ), Fin.succ_pos j⟩
      rwa [pw_ys_zero] at this
    have hR : ∀ ξ r : Fin m → K, (∀ i, r i ∈ R) →
        GG R ψ Φ (D' : K) (xs ((t : K) • N))
          (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ (ξ + r) + pw_bv (c : K))) =
        GG R ψ Φ (D' : K) (xs ((t : K) • N))
          (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K))) := by
      intro ξ r hr
      have e1 := hpt (ξ + r)
      rw [pw_term_inv hD Φ hΦ _ _ _ _ ξ r hr, hpt ξ] at e1
      exact (mul_left_cancel₀ (mul_ne_zero (pw_psi_ne ψ _) hpos) e1).symm
    rw [bx_lin hD (pw_Mx (t : K) (1 + EE N)) hMu (pw_bv (c : K)) hΛ₁ hL₀ _ hinv hs hR, hMm,
      ← mul_assoc, ← pw_mul_finsum]
    exact finsum_congr fun q => hpt (outV R q)
  · have hL : ∀ ξ : Fin m → K,
        Φ (m + 1) ((Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id) = 0 := by
      intro ξ
      by_contra h
      apply hG
      have hsh := pw_shape hm (t : K) (c : K) ξ N
      have hdet := det_Hm (t : K) (c : K) ξ (1 + EE N) (pw_isUpUni N)
      rw [← hDt] at hdet
      rw [hsh] at h hdet
      obtain ⟨hd, hy⟩ := pw_supp_Z Φ hΦ _ _ _ h
      have hρ := hd 0
      have hx : ∀ k, xs ((t : K) • N) k ∈ L₀ := fun k => by simpa using hd k.succ
      rw [Fin.cons_zero] at hρ
      have := h₁ (t : K) ht1 D' hQ _ _ _ hρ hx hy hdet
      exact ⟨fun k => ⟨hx k, this k⟩, fun p hp => by rw [pw_ys_indep _ 0 _ p hp]; exact hy p⟩
    have hRz : ∀ τ : Fin m → K,
        GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ) = 0 := by
      intro τ
      by_contra h
      apply hG
      obtain ⟨g1, g2, -⟩ := GG_supp hC Φ hΦ D' hQ _ _ h
      exact ⟨g1, fun p hp => by rw [pw_ys_indep _ 0 τ p hp]; exact g2 p⟩
    simp only [hL, hRz, zero_mul, finsum_zero, bx_zero, mul_zero]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
