-- Prove2me | solution 1 for Formalism.HN.DualPolygon.key_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:23.971094+00:00
-- url     : https://prove2.me/submissions/a53e4317-176e-4201-b837-eefdcb974ae6

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
import Theorems.Thm_Formalism_HN_DualPolygon_sat_exists
import Theorems.Thm_Formalism_HN_DualPolygon_deg_R
import Theorems.Thm_Formalism_HN_DualPolygon_corr_R

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
    (hsp : Submodule.span K (A : Set V) = ⊤) (θ : ℝ) :
    (∀ R : Submodule (𝓞 K) (Module.Dual K V), R ≤ dualLat A →
        deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R ≤
          θ * Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ↔
      ∀ N : Submodule (𝓞 K) V, N ≤ A →
        ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - θ) *
            ((Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N) ≤
          deg (Formalism.HermitianLatticesTheory.realize b X) A - deg (Formalism.HermitianLatticesTheory.realize b X) N := by
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  constructor
  · intro H N hN
    obtain ⟨N', -, hN', hrk, hdeg⟩ := sat_exists b X hX A hA N hN
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N' hN'
    have h3 := H (dualLat A ⊓ annO N') inf_le_left
    have hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N') by
          linarith)
    nlinarith [e1, hd, h3, hdeg]
  · intro H R hR
    obtain ⟨N, hN, hrk, hdeg⟩ := corr_R b X hX A hA hsp R hR
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N hN
    have h3 := H N hN.1
    have hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) by
          linarith)
    have e2 := congrArg (fun t => θ * t) hx
    nlinarith [e1, e2, hd, h3, hdeg]
end Formalism.HN.DualPolygon
