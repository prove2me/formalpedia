-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:59.056503+00:00
-- url     : https://prove2.me/submissions/564b7b62-6447-4e0f-8001-de3d0b4f3922

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_one_add_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_modK_unitR
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_modK_mul_isUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_one_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_isHess_HH
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_diagonal_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_submatrix_tail
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_entry_bounded
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
theorem _root_.solution (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) :
    ∃ M₃ : ℕ, ∀ t : K, Sm R ϖ M₃ t → ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p : Pr (m + 1), p.1.1 ≠ 0 → y p ∈ L₀) →
      IsUnit ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det ∧
      modK R ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det =
        modK R (∏ k, x k) := by
  refine ⟨(1 + m * ((m + 1) * a)) + m * a, ?_⟩
  intro t ht ρ x y hx hy
  have hϖ := hC.adic.mem
  have htb : Bd R ϖ a t := ht.bd hϖ a
  have hent : ∀ i j, Bd R ϖ a
      (((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ) i j) := by
    intro i j
    exact hessenberg_entry_bounded hϖ htb (fun k => hC.L0 _ (hx k).1) i.succ j
      (fun h => hC.L0 _ (hy _ (Fin.succ_ne_zero i)))
  obtain ⟨r, hr, e⟩ := hess_one_bd hϖ _
    (hessenberg_submatrix_tail (isHess_HH t (Fin.cons ρ x : Fin (m + 1) → K) y)) htb hent
  have hdiag : ∏ i, ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ) i i =
      ∏ k, x k := by
    simp only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]
  rw [hdiag] at e
  have hPP : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k).2.1
  have hPi : Bd R ϖ (m * ((m + 1) * a)) (∏ k, Ring.inverse (x k)) := by
    have := Bd.prod Finset.univ (fun k => Ring.inverse (x k)) (fun k _ => (hx k).2.2)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hε : Sm R ϖ 1 (t * r * ∏ k, Ring.inverse (x k)) := (ht.mul_bd hr).mul_bd hPi
  obtain ⟨v, hv, ev, -⟩ := Sm.one_add_inv hC.adic le_rfl hε
  have e2 : ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det =
      (∏ k, x k) * (1 + t * r * ∏ k, Ring.inverse (x k)) := by
    rw [e]; linear_combination (-(t * r)) * hPP
  have hu1 : IsUnit (∏ k, x k) := IsUnit.of_mul_eq_one _ hPP
  have hu2 : IsUnit (1 + t * r * ∏ k, Ring.inverse (x k)) := IsUnit.of_mul_eq_one _ ev
  rw [e2]
  refine ⟨hu1.mul hu2, ?_⟩
  rw [modK_mul_isUnit hC.adic hu1 hu2,
    modK_unitR (R.add_mem R.one_mem (hε.mem hϖ)) hv ev, mul_one]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
