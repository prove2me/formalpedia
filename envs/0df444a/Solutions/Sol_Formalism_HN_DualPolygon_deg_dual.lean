-- Prove2me | solution 1 for Formalism.HN.DualPolygon.deg_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:23.685617+00:00
-- url     : https://prove2.me/submissions/6be03183-3013-4f97-b209-16039e42c29a

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
import Theorems.Thm_Formalism_HN_DualPolygon_annO_bot
import Theorems.Thm_Formalism_HN_DualPolygon_deg_R
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties


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
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        - deg (Formalism.HermitianLatticesTheory.realize b X) A +
          (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
            (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) ∧
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) =
        (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hSB := saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat
  have hsat0 : IsSat (Formalism.HermitianLatticesTheory.realize b X) A ⊥ := hSB.2.2.2.2.2.1
  obtain ⟨hdeg0, hrk0⟩ := deg_R b X hX A hA hsp ⊥ hsat0
  rw [annO_bot, inf_top_eq] at hdeg0 hrk0
  have hdegbot : deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 := hSB.2.2.2.2.1
  have hrkbot : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 :=
    (hSB.2.2.2.1 ⊥ bot_le).2 rfl
  have hb : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) : ℝ) = 0 := by
    exact_mod_cast hrkbot
  have hP : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) =
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) := by linarith
  refine ⟨?_, hP⟩
  have e0 := congrArg (fun t => (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| /
    (finrank ℚ K : ℝ)) * t) hP
  linarith
end Formalism.HN.DualPolygon
