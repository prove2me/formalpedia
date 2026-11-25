-- Prove2me | solution 1 for Formalism.HN.DualPolygon.mu_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:50.029814+00:00
-- url     : https://prove2.me/submissions/867ceb8a-f293-426b-98f2-56a4c66d6571

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
import Theorems.Thm_Formalism_HN_DualPolygon_dual_ne_bot
import Theorems.Thm_Formalism_HN_DualPolygon_key_one
import Theorems.Thm_Formalism_HN_DualPolygon_key_two
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_slope_characterization


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
    (hsp : Submodule.span K (A : Set V) = ⊤) (hA0 : A ≠ ⊥) :
    muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMin (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMax (Formalism.HermitianLatticesTheory.realize b X) A := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hdfg := dualLat_fg A hsp
  obtain ⟨hlat', -, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg
  have hd0 := dual_ne_bot b A hA hsp hA0
  have m1 := slope_characterization (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat' hd0
  have m2 := slope_characterization (𝓞 K) V _ _ A hlat hA0
  have key1 : ∀ θ : ℝ, muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ≤ θ ↔
      c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b X) A := fun θ =>
    (m1.1 θ).trans ((key_one b X hX A hA hsp θ).trans (m2.2.1 (c2 - θ)).symm)
  have key2 : ∀ θ : ℝ, c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ↔
      muMax (Formalism.HermitianLatticesTheory.realize b X) A ≤ θ := fun θ =>
    (m1.2.1 (c2 - θ)).trans ((key_two b X hX A hA hsp θ).trans (m2.1 θ).symm)
  refine ⟨le_antisymm ((key1 _).2 (by linarith)) ?_, le_antisymm ?_ ((key2 _).2 le_rfl)⟩
  · have := (key1 (muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1 le_rfl
    linarith
  · have := (key2 (c2 - muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1
      (by linarith)
    linarith
end Formalism.HN.DualPolygon
