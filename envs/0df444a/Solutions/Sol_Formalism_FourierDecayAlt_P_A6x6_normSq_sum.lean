-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.normSq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:56.700581+00:00
-- url     : https://prove2.me/submissions/5d954676-623e-42f5-9bc7-b914e4607121

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gauss_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_prj_sec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_sec_prj_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_relIndex_eq_card
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_dot_perp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_perp_of_dot
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_symm_dot
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_psi_q_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gaussF_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gaussF_of_not_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_PL_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_b_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_cq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_cb2
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_cb1
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_sec_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_sec_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_sec_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_inv_mem
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
variable {L Λ : AddSubgroup K}
variable {ψ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    (hu : ∀ x : K, conj (ψ x) = ψ (-x)) (hdet : IsUnit M.det)
    (hAdm : GaussAdm ψ L M) (hPP : perp ψ (perp ψ L) = L)
    (hfin : (PL Λ m).relIndex (PL L m) ≠ 0) :
    (∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)) *
        conj (∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)) =
      ((PL Λ m).relIndex (PL L m) : ℂ) *
        ((PL Λ m).relIndex ((PL (perp ψ L) m).map (mv M⁻¹)) : ℂ) := by
  classical
  have hle := PL_le hInv
  have hcard : Nat.card ((PL L m).map (prj Λ m)) = (PL Λ m).relIndex (PL L m) :=
    (relIndex_eq_card _ _).symm
  have : Finite ((PL L m).map (prj Λ m)) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)
  have : Fintype ((PL L m).map (prj Λ m)) := Fintype.ofFinite _
  let F : (PL L m).map (prj Λ m) → ℂ :=
    fun y => ψ (Ring.inverse 2 * (sec Λ y.1 ⬝ᵥ M *ᵥ sec Λ y.1))
  let B : (PL L m).map (prj Λ m) → (PL L m).map (prj Λ m) → ℂ :=
    fun y w => ψ (sec Λ y.1 ⬝ᵥ M *ᵥ sec Λ w.1)
  have hS : ∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y) = ∑ y, F y := by
    rw [finsum_eq_sum_of_support_subset (s := (Finset.univ : Finset ((PL L m).map (prj Λ m))).map
      ⟨Subtype.val, Subtype.val_injective⟩)]
    · rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun y _ => gaussF_of_mem ψ (sec_mem hle y.2)
    · intro y hy
      by_contra h
      apply hy
      apply gaussF_of_not_mem
      intro hs
      apply h
      simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ, Set.image_univ,
        Subtype.range_coe_subtype]
      exact ⟨_, hs, prj_sec _ _⟩

  have hrad : ∀ w : (PL L m).map (prj Λ m), (∀ y, B y w = 1) → M *ᵥ sec Λ w.1 ∈ PL (perp ψ L) m := by
    intro w hw
    apply mem_perp_of_dot
    intro x hx
    have := hw ⟨prj Λ m x, x, hx, rfl⟩
    rw [← this]
    exact (cb1 h2 hM hInv (sec_mem hle w.2) (sec_prj_sub Λ x)).symm
  rw [hS, gauss_abs F B, hcard]
  · congr 2
    rw [relIndex_eq_card]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
      (Equiv.subtypeEquivRight fun y => ?_))
    constructor
    · rintro ⟨hy, hw⟩
      refine ⟨sec Λ y, ⟨M *ᵥ sec Λ y, hrad ⟨y, hy⟩ hw, ?_⟩, prj_sec _ _⟩
      simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
    · rintro ⟨_, ⟨u, hu', rfl⟩, rfl⟩
      have hx : M⁻¹ *ᵥ u ∈ PL L m := by
        have := inv_mem h2 hM hAdm hu'
        rwa [hPP] at this
      refine ⟨⟨_, hx, rfl⟩, fun y' => ?_⟩
      show ψ (sec Λ y'.1 ⬝ᵥ M *ᵥ sec Λ (prj Λ m (mv M⁻¹ u))) = 1
      rw [cb2 h2 hM hInv (sec_mem hle y'.2) (sec_prj_sub Λ _), mv_apply, mulVec_mulVec,
        mul_nonsing_inv _ hdet, one_mulVec]
      exact dot_perp ψ (sec_mem hle y'.2) hu'
  · intro y w
    show ψ _ = ψ _ * ψ _ * ψ _
    rw [← psi_q_add ψ h2 hM]
    exact cq hInv ((PL L m).add_mem (sec_mem hle y.2) (sec_mem hle w.2)) (sec_add _ _)
  · intro y
    show ψ _ * conj (ψ _) = 1
    rw [hu, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · intro w y y'
    show ψ _ = ψ _ * ψ _
    rw [← AddChar.map_add_eq_mul, ← add_dotProduct]
    exact cb1 h2 hM hInv (sec_mem hle w.2) (sec_add _ _)
  · intro w
    show ψ _ = 1
    rw [symm_dot hM]
    exact b_one h2 hM hInv (sec_mem hle w.2) sec_zero
  · intro w hw
    have h1 := hAdm _ (mem_PL.1 (hrad w hw))
    rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, dotProduct_comm] at h1
    exact h1
end Formalism.FourierDecayAlt.P.A6x6
