-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nO_unif_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:23.556642+00:00
-- url     : https://prove2.me/submissions/d9acd87d-d65a-466a-9eb1-94d289b447b9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_zR_unif_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_relIndex_pK

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open NO
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π : 𝓞 F} (hπ : π ∈ 𝔭) (hπ' : π ∉ 𝔭 ^ 2) (k : ℕ) :
    nO 𝔭 (algebraMap F K (π : F) ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  show (zR 𝔭 _).relIndex _ = _
  rw [zR_unif_pow h𝔭 hπ hπ', relIndex_pK hK hF h𝔭]
end Formalism.HermitianLattices.Ext.L3.D2
