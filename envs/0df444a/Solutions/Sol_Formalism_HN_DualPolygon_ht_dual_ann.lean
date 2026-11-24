-- Prove2me | solution 1 for Formalism.HN.DualPolygon.ht_dual_ann
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:06.634313+00:00
-- url     : https://prove2.me/submissions/5339b63b-7637-4dca-9bdb-dd9fafe0d17d

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_key_lemma
import Theorems.Thm_Formalism_HN_DualPolygon_rpow_neg_half_nat_pow
import Theorems.Thm_Formalism_HN_DualPolygon_rpow_neg_half_sq_mul
import Theorems.Thm_Formalism_HN_DualPolygon_ht_alg
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    ht b.dualBasis (dualFrame X) (dualLat A ⊓ annO N) * ht b X A = ht b X N := by
  obtain ⟨hdim, hcov⟩ := key_lemma b X hX A hA hsp N hN
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hn : finrank ℚ K = 2 * nPl K := sizeMu_finrank_eq K
  unfold ht
  rw [hrkAd, ← hdim, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD]
  rw [hn] at hcov
  push_cast
  exact ht_alg (nPl K) _ _ _ _ _ _ _ (rpow_neg_half_sq_mul hD) hcov
end Formalism.HN.DualPolygon
