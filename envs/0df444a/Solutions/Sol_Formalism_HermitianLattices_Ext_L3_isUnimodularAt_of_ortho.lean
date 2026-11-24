-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.isUnimodularAt_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:52.830283+00:00
-- url     : https://prove2.me/submissions/210423aa-f962-4f5c-8c5e-3632f2e646a3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_star_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isLattice_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isUnimodular_of_ortho
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open StandardSymmetricSums
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L :=
  ((Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs (fun r => (star_int r).imp fun _ ht => ht) L
    (isLattice_of_ortho hL).fg).2).1 (isUnimodular_of_ortho hL)
end Formalism.HermitianLattices.Ext.L3
