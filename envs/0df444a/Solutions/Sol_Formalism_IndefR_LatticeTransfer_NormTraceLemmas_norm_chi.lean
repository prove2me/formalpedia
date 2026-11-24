-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.NormTraceLemmas.norm_chi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.441832+00:00
-- url     : https://prove2.me/submissions/a404497f-32b6-48ce-ac96-f978191dc5ee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing

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
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.NormTraceLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
namespace Formalism.IndefR.LatticeTransfer.NormTraceLemmas
theorem _root_.solution (H : Subgroup G) [Finite H] (χ : H →* (𝓞 K)ˣ) (h : H) (σ : K →+* ℂ) :
    ‖σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
  have hu : ((χ h : (𝓞 K)ˣ) : 𝓞 K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) ^ Nat.card H = 1 := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hu
    rw [map_pow, map_one] at this
    exact this
  exact Complex.norm_eq_one_of_pow_eq_one h2 Nat.card_pos.ne'
end Formalism.IndefR.LatticeTransfer.NormTraceLemmas
