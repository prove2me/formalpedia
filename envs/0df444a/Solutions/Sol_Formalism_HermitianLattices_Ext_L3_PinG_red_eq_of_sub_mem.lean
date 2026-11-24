-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinG.red_eq_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:11.649214+00:00
-- url     : https://prove2.me/submissions/ac33254f-0cdc-45aa-a094-03e0024536e2

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
theorem _root_.solution (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w w' : ↥(locF 𝔭 (spanO b)))
    (hww : (w : V) - w' ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) :
    red b h𝔭 k w = red b h𝔭 k w' := by
  have e : (Submodule.Quotient.mk w : ↥(locF 𝔭 (spanO b)) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))) = Submodule.Quotient.mk w' := by
    rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
    exact hww
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) =
    qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w'))
  rw [e]
end Formalism.HermitianLattices.Ext.L3.PinG
