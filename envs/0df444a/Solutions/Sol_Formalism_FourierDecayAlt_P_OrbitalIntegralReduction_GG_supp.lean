-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.GG_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:08.907665+00:00
-- url     : https://prove2.me/submissions/969022b1-1ad6-4d4a-b7e6-da12c7853d2e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_ringInverse_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_entry_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_entry_above_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_antidiagonal_hessenberg_reversed_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_inverse_determinant_bounded
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul
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
theorem _root_.solution (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (D' : Kˣ) (hD' : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q)
    (x : Fin m → K) (y : Pr (m + 1) → K) (h : GG R ψ Φ (D' : K) x y ≠ 0) :
    (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) ∧
      (∀ p, y p ∈ L₀) ∧ x0 (D' : K) x ∈ L₀ := by
  classical
  have hϖ := hC.adic.mem
  by_cases hU : ∀ k, IsUnit (x k)
  swap
  · exact absurd (by rw [GG, if_neg hU]) h
  have hΦne : Φ (m + 1) (ZZ 0 (xt (D' : K) x) y) ≠ 0 := by
    intro h0
    apply h
    rw [GG, if_pos hU, h0]
    simp
  have hent := hΦ.2.1 _ hΦne
  have hx : ∀ k, x k ∈ L₀ := by
    intro k
    have := hent (Fin.rev k.succ) k.succ
    rw [antidiagonal_hessenberg_reversed_apply, hessenberg_entry_diagonal] at this
    simpa [xt] using this
  have hx0 : x0 (D' : K) x ∈ L₀ := by
    have := hent (Fin.rev 0) 0
    rw [antidiagonal_hessenberg_reversed_apply, hessenberg_entry_diagonal] at this
    simpa [xt] using this
  have hy : ∀ p, y p ∈ L₀ := by
    intro p
    have := hent (Fin.rev p.1.1) p.1.2
    rwa [antidiagonal_hessenberg_reversed_apply, hessenberg_entry_above_diagonal] at this
  refine ⟨fun k => ⟨hx k, hU k, ?_⟩, hy, hx0⟩
  have hxe : ∀ k, x k * Ring.inverse (x k) = 1 := fun k => Ring.mul_inverse_cancel _ (hU k)
  have hPE : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => hxe k
  have hx0e : x0 (D' : K) x = (D' : K) * ∏ k, Ring.inverse (x k) := by
    unfold x0
    rw [ringInverse_eq hPE]
  have hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1 := by simp
  have hsplit : x k * ∏ j ∈ Finset.univ.erase k, x j = ∏ j, x j :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ k)
  have hinv : x k * (x0 (D' : K) x * (∏ j ∈ Finset.univ.erase k, x j) * ((D'⁻¹ : Kˣ) : K)) = 1 := by
    rw [hx0e]
    linear_combination ((D' : K) * (∏ k, Ring.inverse (x k)) * ((D'⁻¹ : Kˣ) : K)) * hsplit +
      ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hPE + hDD
  rw [ringInverse_eq hinv]
  have h1 : Bd R ϖ ((Finset.univ.erase k).card * a) (∏ j ∈ Finset.univ.erase k, x j) :=
    Bd.prod _ _ fun j _ => hC.L0 _ (hx j)
  have h2 := ((hC.L0 _ hx0).mul h1).mul (inverse_determinant_bounded hC D' hD')
  refine Bd.mono hϖ ?_ h2
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hm : 1 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) k.2)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
