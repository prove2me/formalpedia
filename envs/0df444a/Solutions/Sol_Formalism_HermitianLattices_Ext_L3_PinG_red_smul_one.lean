-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinG.red_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:16.377338+00:00
-- url     : https://prove2.me/submissions/5dd29a31-f88a-4300-9f91-d463221c2d00

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinG
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.PinG
theorem _root_.solution (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {c : 𝓞 F}
    (hc : c - 1 ∈ 𝔭 ^ k) (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (ι c • w) = red b h𝔭 k w := by
  rw [map_smul]
  funext i
  rw [Pi.smul_apply, Algebra.smul_def]
  have : algebraMap (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ k) (ι c) = 1 := by
    show Ideal.Quotient.mk _ (ι c) = 1
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    exact ι_mem_pow hc
  rw [this, one_mul]
end Formalism.HermitianLattices.Ext.L3.PinG
