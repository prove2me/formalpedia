-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.card_stabilizer_autSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:10.787535+00:00
-- url     : https://prove2.me/submissions/2c126e97-e409-431a-afea-2e646b100305

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub

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
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : V) :
    Nat.card (MulAction.stabilizer (autSub h L) t) =
      Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
