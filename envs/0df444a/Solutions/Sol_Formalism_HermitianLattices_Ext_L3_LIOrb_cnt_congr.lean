-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:48:31.00485+00:00
-- url     : https://prove2.me/submissions/da3dd26d-9b8b-484f-af1a-5ea035cb3dad

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) {Ω Ω' : Set V}
    (hΩ : ∀ y ∈ A, CongrP 𝔭 k (h y y) (algebraMap F K (n : F)) → (y ∈ Ω ↔ y ∈ Ω')) :
    cnt h A 𝔭 k n Ω = cnt h A 𝔭 k n Ω' := by
  unfold cnt
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    exists_congr fun y => and_congr_right fun _ => and_congr_right fun hc => hΩ y y.2 hc)
end Formalism.HermitianLattices.Ext.L3.LIOrb
