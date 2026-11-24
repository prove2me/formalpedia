-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.absNorm_eq_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:33.521158+00:00
-- url     : https://prove2.me/submissions/c4a5985c-7470-42e9-9bba-5d27922788ef

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_sSup_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BrA
theorem _root_.solution {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (Ideal.absNorm I : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ sSup {e : ℕ | I ≤ 𝔭.1 ^ e} := by
  let φ : Ideal (𝓞 F) →* ℝ :=
    ((Nat.castRingHom ℝ : ℕ →+* ℝ) : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom
  have hφ : ∀ J, φ J = (Ideal.absNorm J : ℝ) := fun _ => rfl
  have h0 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I :=
    Ideal.hasFiniteMulSupport hI
  have h1 : φ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
    exact map_finprod φ h0
  have h2 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => φ (v.maxPowDividing I) :=
    h0.fun_comp (map_one φ)
  have h3 : ∏' v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := tprod_eq_finprod h2
  rw [← hφ, h1, ← h3, ← (maxEquiv F).tprod_eq]
  refine tprod_congr fun 𝔭 => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow, hφ,
    ← sSup_le_pow _ hI]
  rfl
end Formalism.HermitianLattices.Ext.L3.BrA
