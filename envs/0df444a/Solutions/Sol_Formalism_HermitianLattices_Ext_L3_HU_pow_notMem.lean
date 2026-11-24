-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.pow_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:55.112363+00:00
-- url     : https://prove2.me/submissions/5e8c70b0-b6ba-476f-a733-77d5f0255f6f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π₀ : 𝓞 F} (hπ : π₀ ∉ 𝔭 ^ 2) (e : ℕ) :
    π₀ ^ e ∉ 𝔭 ^ (e + 1) := by
  induction e with
  | zero =>
    rw [pow_zero, zero_add, pow_one]
    exact fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h)
  | succ e ih =>
    have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) ih hπ
    rwa [← pow_succ] at this
end Formalism.HermitianLattices.Ext.L3.HU
