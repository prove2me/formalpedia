-- Prove2me | solution 1 for Formalism.HN.DualPolygon.deg_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:11.346827+00:00
-- url     : https://prove2.me/submissions/faaffddc-accf-4128-a4e1-0f9191054c57

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
import Theorems.Thm_Formalism_HN_DualPolygon_dualFrame_unit
import Theorems.Thm_Formalism_HN_DualPolygon_dualLat_fg
import Theorems.Thm_Formalism_HN_DualPolygon_key_lemma
import Theorems.Thm_Formalism_F_covolPos
import Theorems.Thm_Formalism_HN_place_lattice_structure


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
    deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) =
        deg (Formalism.HermitianLatticesTheory.realize b X) N - deg (Formalism.HermitianLatticesTheory.realize b X) A +
          (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
            (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) : ℝ) ∧
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) : ℝ) =
        (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
  have hX' := dualFrame_unit X hX
  obtain ⟨hdim, hcov⟩ := key_lemma b X hX A hA hsp N hN
  have hNfg : N.FG := Submodule.FG.of_le hA hN.1
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hdfg := dualLat_fg A hsp
  have hRfg : (dualLat A ⊓ annO N).FG := Submodule.FG.of_le hdfg inf_le_left
  obtain ⟨hlatA, hrkA, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨hlatN, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  obtain ⟨hlatR, hrkR, -⟩ :=
    place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A ⊓ annO N) hRfg
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hn0 : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcR := Formalism.F.covolPos _ _ hlatR.2
  have hcA := Formalism.F.covolPos _ _ hlatA.2
  have hcN := Formalism.F.covolPos _ _ hlatN.2
  have hlog := congrArg Real.log hcov
  rw [Real.log_mul (mul_pos hcR hcA).ne' (by positivity), Real.log_mul hcR.ne' hcA.ne',
    Real.log_mul (by positivity) hcN.ne', Real.log_pow, Real.log_pow] at hlog
  set r := rkK (dualLat A ⊓ annO N) with hr
  refine ⟨?_, ?_⟩
  · unfold deg Formalism.F.deg
    rw [hrkR]
    have h1 : (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
        ((finrank ℚ K * r : ℕ) : ℝ) = ((finrank ℚ K * r : ℕ) : ℝ) * Real.log 2 -
          (r : ℝ) * Real.log |(NumberField.discr K : ℝ)| := by
      push_cast
      field_simp
    rw [h1]
    push_cast at hlog ⊢
    linarith
  · rw [hrkR, hrkA, hrkN, hrkAd, ← hdim]
    push_cast
    ring
end Formalism.HN.DualPolygon
