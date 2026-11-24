-- Prove2me | solution 1 for Formalism.HN.DualPolygon.sat_of_ann
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:21.861064+00:00
-- url     : https://prove2.me/submissions/98ec1908-f413-4023-8bfd-20d329edd84e

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
import Theorems.Thm_Formalism_HN_DualPolygon_exists_basis_in
import Theorems.Thm_Formalism_HN_DualPolygon_exists_int_smul_mem
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_shiftInv_isSat_iff


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
    (hsp : Submodule.span K (A : Set V) = ⊤) (R : Submodule (𝓞 K) (Module.Dual K V))
    (hR : R ≤ dualLat A) :
    ∃ N, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N ∧ R ≤ dualLat A ⊓ annO N ∧
      rkK R + rkK N = finrank K V := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  set W : Submodule K V := (Submodule.span K (R : Set (Module.Dual K V))).dualCoannihilator with hW
  set N : Submodule (𝓞 K) V := A ⊓ W.restrictScalars (𝓞 K) with hN
  have hNA : N ≤ A := inf_le_left
  have hspN : Submodule.span K (N : Set V) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      exact hx.2
    · intro w hw
      obtain ⟨c, hc, hcw⟩ := exists_int_smul_mem A e he w
      have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.2 hc
      have hmem : (c : K) • w ∈ N := ⟨hcw, W.smul_mem _ hw⟩
      have : w = ((c : K))⁻¹ • ((c : K) • w) := by rw [smul_smul, inv_mul_cancel₀ hcK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hdim : rkK R + rkK N = finrank K V := by
    unfold rkK
    rw [hspN]
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq _
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N := by
    rw [shiftInv_isSat_iff (Formalism.HermitianLatticesTheory.realize b X) hlat N]
    refine ⟨hNA, fun N'' h1 h2 h3 => ?_⟩
    have hfg'' : N''.FG := Submodule.FG.of_le hA h2
    have hNfg : N.FG := Submodule.FG.of_le hA hNA
    obtain ⟨-, hr1, -⟩ := place_lattice_structure K V ι b X hX N'' hfg''
    obtain ⟨-, hr2, -⟩ := place_lattice_structure K V ι b X hX N hNfg
    have hn0 : 0 < finrank ℚ K := Module.finrank_pos
    have hrkK : rkK N'' = rkK N := by
      rw [hr1, hr2] at h3
      exact Nat.eq_of_mul_eq_mul_left hn0 h3
    have hsp_eq : Submodule.span K (N : Set V) = Submodule.span K (N'' : Set V) :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono h1) hrkK.symm
    apply le_antisymm _ h1
    intro x hx
    refine ⟨h2 hx, ?_⟩
    show x ∈ W
    rw [← hspN, hsp_eq]
    exact Submodule.subset_span hx
  refine ⟨N, hsat, fun f hf => ⟨hR hf, fun x hx => ?_⟩, hdim⟩
  have hxW : x ∈ W := hx.2
  exact (Submodule.mem_dualCoannihilator x).1 hxW f (Submodule.subset_span hf)
end Formalism.HN.DualPolygon
