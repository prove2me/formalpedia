-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.mk_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:47.142814+00:00
-- url     : https://prove2.me/submissions/9e8dce8f-81c5-43c9-9595-82861410edaa

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix κ κ (𝓞 K)) (c c' : κ → 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (star c ⬝ᵥ (H *ᵥ c')) =
      star (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (c i)) ⬝ᵥ
        (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (c' i)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec _ H c' i
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
