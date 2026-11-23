-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:25.266006+00:00
-- url     : https://prove2.me/submissions/aafb5214-2589-4600-9f5d-439bf9a29a1c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_single_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_inv_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_inv_sup
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_isLat_inf
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_isLat_sup
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_field_refinement
import Theorems.Thm_Formalism_FourierDecayAlt_P_orthogonal_lattice_properties
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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution : GaussIndep := by
  intro K _ _ _ R ψ hD h0 m M hM hdet L Λ L' Λ' hL hΛ hL' hΛ' hA hI hA' hI'
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : ∀ Λ L : AddSubgroup K, intK R Λ 0 (gaussF ψ L M) = 1 := by
      intro Λ L
      unfold intK
      rw [pow_zero, one_mul, finsum_unique, gaussF_pos (fun i => i.elim0)]
      simp [qf]
    rw [e, e]
  have := hD.t2
  have h2 : IsUnit (2 : K) := by simpa using h0 2 (by norm_num)
  have hΛ₀ : IsLat (Λ ⊓ Λ') := isLat_inf hΛ hΛ'
  have hL₂ : IsLat (L ⊔ L') := isLat_sup hL hL'
  have hle : ∀ {L Λ : AddSubgroup K}, LatInvN Λ (gaussF ψ L M) → Λ ≤ L := by
    intro L Λ hI x hx
    have := (inv_cons h2 hM hI (Pi.single ⟨0, hm⟩ x) (single_mem hx _)).1 ⟨0, hm⟩
    simpa using this
  have hsupp : ∀ L : AddSubgroup K, ∀ x, gaussF ψ L M x ≠ 0 → ∀ i, x i ∈ L := by
    intro L x hx
    by_contra hcon
    exact hx (gaussF_neg hcon)
  have r1 := integral_field_refinement K R ψ hD Λ (Λ ⊓ Λ') L m (gaussF ψ L M) hΛ hΛ₀ hL inf_le_left
    (hsupp L) hI
  have r2 := integral_field_refinement K R ψ hD Λ' (Λ ⊓ Λ') L' m (gaussF ψ L' M) hΛ' hΛ₀ hL' inf_le_right
    (hsupp L') hI'
  have hJ : LatInvN (Λ ⊓ Λ') (gaussF ψ L M) := fun x l hl => hI x l (fun i => (hl i).1)
  have hJ' : LatInvN (Λ ⊓ Λ') (gaussF ψ L' M) := fun x l hl => hI' x l (fun i => (hl i).2)
  have hS := inv_sup h2 hM hI hI'
  rw [← r1, ← r2]
  unfold intK
  congr 1
  rw [← key h2 hM hdet hL hL₂ hΛ₀ le_sup_left (inf_le_left.trans (hle hI))
      (orthogonal_lattice_properties K R ψ hD h0 L hL).2.1 hA hJ hS,
    ← key h2 hM hdet hL' hL₂ hΛ₀ le_sup_right (inf_le_right.trans (hle hI'))
      (orthogonal_lattice_properties K R ψ hD h0 L' hL').2.1 hA' hJ' hS]
end Formalism.FourierDecayAlt.P.A6x7.Ind
