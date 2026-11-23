-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:01.076717+00:00
-- url     : https://prove2.me/submissions/618cc18e-9254-44eb-830b-31cc0457556a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_one_add_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_ringInverse_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_one_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_isHess_HH
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_diagonal_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_determinant_and_inverse_bounded
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
    ∃ M₁ : ℕ, ∀ t : K, Sm R ϖ M₁ t → ∀ D' : Kˣ, ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) →
    ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K), ρ ∈ L₀ → (∀ k, x k ∈ L₀) → (∀ p, y p ∈ L₀) →
      (HH t (Fin.cons ρ x : Fin (m + 1) → K) y).det = (D' : K) →
      ∀ k, IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k)) := by
  refine ⟨(1 + a) + (m + 1) * a, ?_⟩
  intro t ht D' hD' ρ x y hρ hx hy hdet k
  have hϖ := hC.adic.mem
  obtain ⟨hDb, hDi⟩ := determinant_and_inverse_bounded hC D' hD'
  have htb : Bd R ϖ a t := ht.bd hϖ a
  have hd : ∀ i, Bd R ϖ a ((Fin.cons ρ x : Fin (m + 1) → K) i) := by
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa using hC.L0 _ hρ
    · simpa using hC.L0 _ (hx i')
  have hent : ∀ i j, Bd R ϖ a (HH t (Fin.cons ρ x : Fin (m + 1) → K) y i j) := by
    intro i j
    unfold HH
    split_ifs with h1 h2 h3
    · exact hd i
    · exact hC.L0 _ (hy _)
    · exact htb
    · exact Bd.of_mem hϖ R.zero_mem a
  obtain ⟨r, hr, e⟩ := hess_one_bd hϖ _ (isHess_HH t (Fin.cons ρ x : Fin (m + 1) → K) y) htb hent
  have hprod : ∏ i, HH t (Fin.cons ρ x : Fin (m + 1) → K) y i i = ρ * ∏ k, x k := by
    simp only [hessenberg_diagonal_entry, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hdet, hprod] at e
  have hε : Sm R ϖ 1 (-(t * r * ((D'⁻¹ : Kˣ) : K))) := ((ht.mul_bd hr).mul_bd hDi).neg
  obtain ⟨v, hv, ev, -⟩ := Sm.one_add_inv hC.adic le_rfl hε
  have hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1 := by simp
  have key : ρ * (∏ k, x k) * ((D'⁻¹ : Kˣ) : K) * v = 1 := by
    linear_combination ev - ((D'⁻¹ : Kˣ) : K) * v * e + v * hDD
  have hP : x k * ∏ j ∈ Finset.univ.erase k, x j = ∏ j, x j :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ k)
  have hinv : x k * (ρ * (∏ j ∈ Finset.univ.erase k, x j) * ((D'⁻¹ : Kˣ) : K) * v) = 1 := by
    rw [← hP] at key; linear_combination key
  refine ⟨IsUnit.of_mul_eq_one _ hinv, ?_⟩
  rw [ringInverse_eq hinv]
  have hb := (((hC.L0 _ hρ).mul (Bd.prod (Finset.univ.erase k) x
    (fun j _ => hC.L0 _ (hx j)))).mul hDi).mul_mem hv
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin] at hb
  refine Bd.mono hϖ (le_of_eq ?_) hb
  have h1 : (m - 1) + 1 = m := by have := k.2; omega
  calc a + (m - 1) * a + a = ((m - 1) + 1 + 1) * a := by ring
    _ = (m + 1) * a := by rw [h1]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
