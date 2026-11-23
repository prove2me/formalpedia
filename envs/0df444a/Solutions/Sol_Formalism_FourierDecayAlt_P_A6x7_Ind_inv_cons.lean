-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.inv_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:57.921336+00:00
-- url     : https://prove2.me/submissions/7d33a1eb-3407-4fbc-a7ab-833aef0b8564

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_qf_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_psi_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_neg
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Ind
variable {K : Type} [CommRing K] {m : ℕ}
variable {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    {L Λ : AddSubgroup K} (hI : LatInvN Λ (gaussF ψ L M)) (l : Fin m → K) (hl : ∀ i, l i ∈ Λ) :
    (∀ i, l i ∈ L) ∧ ψ (qf M l) = 1 ∧
      ∀ x : Fin m → K, (∀ i, x i ∈ L) → ψ (x ⬝ᵥ (M *ᵥ l)) = 1 := by
  have e0 := hI 0 l hl
  have z0 : gaussF ψ L M (0 : Fin m → K) = 1 := by
    rw [gaussF_pos (ξ := 0) (fun i => L.zero_mem)]; simp [qf]
  rw [zero_add, z0] at e0
  have hlL : ∀ i, l i ∈ L := by
    by_contra hcon
    rw [gaussF_neg hcon] at e0
    exact zero_ne_one e0
  rw [gaussF_pos hlL] at e0
  refine ⟨hlL, e0, fun x hx => ?_⟩
  have e1 := hI x l hl
  rw [gaussF_pos hx, gaussF_pos (ξ := x + l) (fun i => L.add_mem (hx i) (hlL i)), qf_add h2 M hM,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e0, mul_one] at e1
  exact mul_left_cancel₀ (psi_ne_zero ψ (qf M x)) (by rw [e1, mul_one])
end Formalism.FourierDecayAlt.P.A6x7.Ind
