-- Prove2me | solution 1 for GaussValuationUniqueness.not_inj_of_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:25.368277+00:00
-- url     : https://prove2.me/submissions/c9234764-79bd-42d4-b6a0-4e64f34f3091

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_NotInjOfTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
namespace GaussValuationUniqueness
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (S : Set E)
    (j0 : Fin (N + 1)) (ρ : Fin N → IntermediateField.adjoin F S) (hD : 1 ≤ D)
    (htr : Algebra.trdeg F (IntermediateField.adjoin F S) = ((D - 1 : ℕ) : Cardinal)) :
    ¬ Function.Injective (MvPolynomial.aeval (R := F) (imgR (D := D) j0 ρ)) := by
  intro hinj
  have hai : AlgebraicIndependent F (imgR (D := D) j0 ρ) := hinj
  have h1 := hai.cardinalMk_le_trdeg
  first
  | rw [← Algebra.trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  | rw [← trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  rw [htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h1
  have hT : Fintype.card (TVar D N) = (D + 1) * (N + 1) := by simp [TVar]
  have hS : Fintype.card (SVar D N) = 1 + (D + 1) * N := by simp [SVar]
  rw [Cardinal.mk_fintype, Cardinal.mk_fintype, hT, hS] at h1
  norm_cast at h1
  rw [show (D + 1) * (N + 1) = (D + 1) * N + (D + 1) by ring] at h1
  generalize (D + 1) * N = P at h1
  omega
end GaussValuationUniqueness
