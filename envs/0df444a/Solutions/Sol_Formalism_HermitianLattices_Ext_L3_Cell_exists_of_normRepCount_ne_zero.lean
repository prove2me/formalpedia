-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_of_normRepCount_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:11.390948+00:00
-- url     : https://prove2.me/submissions/23772517-ff3f-4712-a75c-d124a16fb540

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution {Q : Ideal (𝓞 K)} {n : 𝓞 K} (h : normRepCount K Q 1 n ≠ 0) :
    ∃ α : 𝓞 K, conjO K α * α - n ∈ Q := by
  unfold normRepCount at h
  obtain ⟨⟨x, y, -, hy⟩⟩ := (Nat.card_ne_zero.mp h).1
  refine ⟨y 0, ?_⟩
  rw [Fin.sum_univ_one] at hy
  exact Ideal.Quotient.eq.mp hy
end Formalism.HermitianLattices.Ext.L3.Cell
