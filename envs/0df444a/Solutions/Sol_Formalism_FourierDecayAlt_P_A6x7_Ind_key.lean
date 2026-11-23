-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:26.950821+00:00
-- url     : https://prove2.me/submissions/e399125c-4bc1-42da-aea3-5c89127ed50d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_finsum_zero_of_fibres
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_finsum_zero_of_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_single_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_shiftF
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_fin_supp
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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    (hdet : IsUnit M.det) {L L₂ Λ₀ : AddSubgroup K} (hL : IsLat L) (hL₂ : IsLat L₂)
    (hΛ₀ : IsLat Λ₀) (hle : L ≤ L₂) (hΛL : Λ₀ ≤ L) (hperp : perp ψ (perp ψ L) = L)
    (hA : GaussAdm ψ L M) (hI : LatInvN Λ₀ (gaussF ψ L M)) (hI₂ : LatInvN Λ₀ (gaussF ψ L₂ M)) :
    ∑ᶠ y : Fin m → K ⧸ Λ₀, gaussF ψ L₂ M (fun i => Quotient.out (y i)) =
      ∑ᶠ y : Fin m → K ⧸ Λ₀, gaussF ψ L M (fun i => Quotient.out (y i)) := by
  classical
  rw [← sub_eq_zero, ← finsum_sub_distrib (fin_supp hΛ₀ hL₂ M) (fin_supp hΛ₀ hL M)]
  set o : (Fin m → K ⧸ Λ₀) → (Fin m → K) := fun y i => Quotient.out (y i) with ho
  apply finsum_zero_of_fibres (fun y i => ((o y i : K) : K ⧸ L))
  · refine ((fin_supp (ψ := ψ) hΛ₀ hL₂ M).union (fin_supp (ψ := ψ) hΛ₀ hL M)).subset ?_
    intro y hy
    by_contra hcon
    rw [Set.mem_union, not_or, Function.notMem_support, Function.notMem_support] at hcon
    apply hy
    show gaussF ψ L₂ M (o y) - gaussF ψ L M (o y) = 0
    rw [hcon.1, hcon.2, sub_zero]
  intro c
  have hfib : ∀ y : Fin m → K ⧸ Λ₀, (fun i => ((o y i : K) : K ⧸ L)) = c →
      ∀ i, o y i - (Quotient.out (c i) : K) ∈ L := by
    intro y hy i
    have h1 : ((o y i : K) : K ⧸ L) = ((Quotient.out (c i) : K) : K ⧸ L) := by
      rw [QuotientAddGroup.out_eq']; exact congrFun hy i
    have h3 := QuotientAddGroup.eq.1 h1.symm
    rwa [neg_add_eq_sub] at h3
  by_cases hc : ∀ i, (Quotient.out (c i) : K) ∈ L
  · apply finsum_eq_zero_of_forall_eq_zero
    intro y
    split_ifs with hy
    · have hyL : ∀ i, o y i ∈ L := fun i => by
        have := L.add_mem (hfib y hy i) (hc i)
        simpa using this
      rw [gaussF_pos hyL, gaussF_pos (fun i => hle (hyL i)), sub_self]
    · rfl
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    have hex : ∃ a ∈ perp ψ L, ψ ((Quotient.out (c i) : K) * a) ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hi (hperp.le hcon)
    obtain ⟨a, ha, hne⟩ := hex
    set y₀ : Fin m → K := Pi.single i a with hy₀
    have hy₀m : ∀ j, y₀ j ∈ perp ψ L := single_mem ha i
    have hξ₀ : ∀ j, (M⁻¹ *ᵥ y₀) j ∈ L := inv_mem h2 hM hperp hA y₀ hy₀m
    have hq := hA y₀ hy₀m
    apply finsum_zero_of_shift (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀))) _
      (ψ ((Quotient.out (c i) : K) * a)) hne
    intro y
    have hout : ∃ l : Fin m → K, (∀ j, l j ∈ Λ₀) ∧
        o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) = o y + M⁻¹ *ᵥ y₀ + l := by
      have : ∀ j, ∃ l ∈ Λ₀, o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) j =
          o y j + (M⁻¹ *ᵥ y₀) j + l := by
        intro j
        obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add Λ₀ (o y j + (M⁻¹ *ᵥ y₀) j)
        refine ⟨l, l.2, ?_⟩
        rw [← hl]
        show Quotient.out (y j + (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) = _
        congr 1
        rw [QuotientAddGroup.mk_add, ho]
        simp only [QuotientAddGroup.out_eq']
      choose l hl hl' using this
      exact ⟨l, hl, funext hl'⟩
    obtain ⟨l, hl, hol⟩ := hout
    have hκ : (fun j => ((o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) j : K) :
        K ⧸ L)) = fun j => ((o y j : K) : K ⧸ L) := by
      funext j
      rw [hol, QuotientAddGroup.eq]
      have : -(o y + M⁻¹ *ᵥ y₀ + l) j + o y j = -((M⁻¹ *ᵥ y₀) j + l j) := by
        simp only [Pi.add_apply]; ring
      rw [this]
      exact L.neg_mem (L.add_mem (hξ₀ j) (hΛL (hl j)))
    rw [hκ]
    split_ifs with hy
    · show gaussF ψ L₂ M (o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y)) -
          gaussF ψ L M (o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y)) =
        _ * (gaussF ψ L₂ M (o y) - gaussF ψ L M (o y))
      rw [hol, hI₂ _ l hl, hI _ l hl, shiftF h2 hM hdet y₀ hq (fun j => hle (hξ₀ j)),
        shiftF h2 hM hdet y₀ hq hξ₀, ← mul_sub]
      congr 1
      rw [hy₀, dotProduct_single]
      have h5 := ha _ (hfib y hy i)
      have h6 : o y i * a = a * (o y i - (Quotient.out (c i) : K)) + (Quotient.out (c i) : K) * a := by
        ring
      rw [h6, AddChar.map_add_eq_mul, h5, one_mul]
    · rw [mul_zero]
end Formalism.FourierDecayAlt.P.A6x7.Ind
