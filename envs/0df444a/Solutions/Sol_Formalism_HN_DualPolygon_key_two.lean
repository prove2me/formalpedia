-- Prove2me | solution 1 for Formalism.HN.DualPolygon.key_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:33.085455+00:00
-- url     : https://prove2.me/submissions/d99d9079-0e07-4896-a3a3-a1db36ec8256

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
import Theorems.Thm_Formalism_HN_DualPolygon_deg_dual

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
        ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - θ) *
            ((Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
              Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ≤
          deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) -
            deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ↔
      ∀ N : Submodule (𝓞 K) V, N ≤ A →
        deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ θ * Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  obtain ⟨hdeg0, hrk0⟩ := deg_dual b X hX A hA hsp
  have e0 := congrArg (fun t => c2 * t) hrk0
  constructor
  · intro H N hN
    obtain ⟨N', -, hN', hrk, hdeg⟩ := sat_exists b X hX A hA N hN
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N' hN'
    have h3 := H (dualLat A ⊓ annO N') inf_le_left
    have hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
          Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N') =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N by linarith)
    have e2 := congrArg (fun t => c2 * t) hr
    have e3 := congrArg (fun t => θ * t) hc
    nlinarith [e0, e1, e2, e3, hd, h3, hdeg, hdeg0]
  · intro H R hR
    obtain ⟨N, hN, hrk, hdeg⟩ := corr_R b X hX A hA hsp R hR
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N hN
    have h3 := H N hN.1
    have hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
          Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N by linarith)
    have e2 := congrArg (fun t => c2 * t) hr
    nlinarith [e0, e1, e2, hd, h3, hdeg, hdeg0]
end Formalism.HN.DualPolygon
