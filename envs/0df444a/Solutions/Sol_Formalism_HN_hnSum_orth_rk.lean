-- Prove2me | solution 1 for Formalism.HN.hnSum_orth_rk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:09:45.776822+00:00
-- url     : https://prove2.me/submissions/5f9b190f-14db-4e62-930d-e4249d15939c

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Theorems.Thm_Formalism_HN_hnSum_orth
import Theorems.Thm_Formalism_HN_hnSum_rk_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w x
variable {R : Type u} {V : Type v} {E : Type w} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
namespace Formalism.HN
theorem _root_.solution (h1 : DegSupermod.{u, v, w}) {A B : Submodule R V} (hA : IsLat ρ A)
    (hB : IsLat ρ B) (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) :
    rk ρ (A ⊔ B) = rk ρ A + rk ρ B := by
  obtain ⟨hL, hinf, -⟩ := hnSum_orth ρ hA hB h
  have e := (h1 R V E ρ (A ⊔ B) A B hL le_sup_left le_sup_right).1
  rw [hinf, hnSum_rk_bot] at e
  simpa using e
end Formalism.HN
