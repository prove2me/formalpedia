-- Prove2me | solution 1 for Formalism.DivisorInequality.slope_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:33.090338+00:00
-- url     : https://prove2.me/submissions/3170b4f9-15af-4d74-9122-7ded2e493f1b

import Mathlib
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_BaseLevelBoundsWithCovolumeHolds
import Theorems.Thm_Formalism_DivisionValues_divisor_bounds_chain_weak
import Theorems.Thm_Formalism_DivisionValues_dual_lattice_measure
import Theorems.Thm_Formalism_DivisionValues_untwisted_choice
import Theorems.Thm_Formalism_ExtensionFiltration_log_covolume_slope_mu


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder
open Formalism Formalism.DivisorInequality
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DivisorInequality
theorem _root_.solution : BoundsMu := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hD hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ XW hXW
    M hM HT XT hHT0 hHTw Tl hT θ hθ κ hκ ρt ρr hρr hρ0 hρpos hρv hdet0 hdet Gm eb hLB hG nH Hm hH hHpos Pm hP
    hQ Mt hMt hLamP hGR R hR hRloc Sy Tw hTw hS hA0
    LG E3 E1 E2 elly gy Fy erry Jy ηy hF0 hGb hLG hI hJ hE1 hE2 hE3
  obtain ⟨err', Jx', η', -, hI', hJ', hs1, hs2, hs3⟩ := untwisted_choice (HeightOneSpectrum (𝓞 K)) J
    Sy Tw D hD hTw lw elly (fun y j => (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ))
    (fun y j => (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ))
    (fun y j => (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ)) Fy erry Jy ηy hA0 hF0 hI hJ
  have hch := divisor_bounds_chain_weak K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J
    (fun _ => D) XW hXW M hM HT XT hHT0 hHTw Tl hT θ hθ κ hκ ρt ρr hρr hρ0 hρpos hρv hdet0 hdet Gm eb hLB hG
    nH Hm hH hHpos Pm hP hQ Mt hMt hLamP hGR R hR hRloc Sy hS LG E3
    (fun j => lcv (XW j) (M j) / D) E1 E2 elly gy Fy err' Jx' η' hD hGb hLG (fun _ => le_rfl) hI' hJ'
    (fun j => by rw [hs1 j]; exact hE1 j) (fun j => by rw [hs2 j]; exact hE2 j) hE3
  have hF : ∑ j, ∑ y ∈ Sy, lw y * Fy y j = ∑ j, ∑ y ∈ Tw, lw y * Fy y j :=
    Finset.sum_congr rfl (fun j _ => hs3 j)
  rw [hF] at hch
  refine ⟨?_, fun j => ?_⟩
  · rw [dual_lattice_measure K D hD XE hXE R hR]
    exact hch
  · rw [Formalism.ExtensionFiltration.log_covolume_slope_mu K D hD (XW j) (hXW j) (M j) (hM j)]
    have : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
end Formalism.DivisorInequality
