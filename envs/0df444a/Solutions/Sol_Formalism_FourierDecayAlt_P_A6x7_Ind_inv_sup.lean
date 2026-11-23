-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.inv_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:21.635374+00:00
-- url     : https://prove2.me/submissions/c5930b72-2581-4917-8e9a-03326e45a41c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_qf_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_inv_cons
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
    {L Λ L' Λ' : AddSubgroup K} (hI : LatInvN Λ (gaussF ψ L M))
    (hI' : LatInvN Λ' (gaussF ψ L' M)) : LatInvN (Λ ⊓ Λ') (gaussF ψ (L ⊔ L') M) := by
  intro x l hl
  obtain ⟨hlL, hq, hx1⟩ := inv_cons h2 hM hI l (fun i => (hl i).1)
  obtain ⟨-, -, hx2⟩ := inv_cons h2 hM hI' l (fun i => (hl i).2)
  have hlS : ∀ i, l i ∈ L ⊔ L' := fun i => (le_sup_left : L ≤ L ⊔ L') (hlL i)
  by_cases hx : ∀ i, x i ∈ L ⊔ L'
  · choose x₁ h₁ x₂ h₂ h₁₂ using fun i => AddSubgroup.mem_sup.1 (hx i)
    have hxx : x = x₁ + x₂ := by funext i; exact (h₁₂ i).symm
    rw [gaussF_pos hx, gaussF_pos (ξ := x + l) (fun i => (L ⊔ L').add_mem (hx i) (hlS i)), qf_add h2 M hM,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hq, mul_one]
    have : ψ (x ⬝ᵥ (M *ᵥ l)) = 1 := by
      rw [hxx, add_dotProduct, AddChar.map_add_eq_mul, hx1 x₁ h₁, hx2 x₂ h₂, one_mul]
    rw [this, mul_one]
  · rw [gaussF_neg hx, gaussF_neg]
    intro h
    apply hx
    intro i
    have := (L ⊔ L').sub_mem (h i) (hlS i)
    simpa using this
end Formalism.FourierDecayAlt.P.A6x7.Ind
