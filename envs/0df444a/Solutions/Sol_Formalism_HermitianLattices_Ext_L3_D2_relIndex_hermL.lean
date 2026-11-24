-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.relIndex_hermL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:27.424985+00:00
-- url     : https://prove2.me/submissions/e2b3671b-6e4c-4825-9d12-11534a16ea3c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_relIndex_sesqL_eq_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_relIndex_sesqL

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
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k c : ℕ}
    (hle : sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k) :
    (hermL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (hermL (locF 𝔭 A₀) 𝔭 k) *
        Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) =
      Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
  have h1 := relIndex_sesqL hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭 hle
  rw [relIndex_sesqL_eq_sq hK hF A₀ B₀ h𝔭 hle] at h1
  apply Nat.pow_left_injective (n := 2) (by norm_num)
  show _ ^ 2 = _ ^ 2
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm _ 2, mul_comm _ 2]
  exact h1
end Formalism.HermitianLattices.Ext.L3.D2
