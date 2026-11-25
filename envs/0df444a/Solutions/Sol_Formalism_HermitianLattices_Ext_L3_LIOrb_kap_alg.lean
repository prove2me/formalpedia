-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.kap_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:33:01.606252+00:00
-- url     : https://prove2.me/submissions/c2b15b36-f3d2-4ba8-bd78-16cd4e9f09a6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatioHolds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtHomInjective

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
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {E₁ E₂ Q₁ Q₂ ν₁ ν₂ μ₁ μ₂ a b c d a' b' o₁ o₂ : ℝ} (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (ha' : a' ≠ 0)
    (ho₁ : o₁ ≠ 0) (ho₂ : o₂ ≠ 0) (h1 : E₁ * Q₂ * b * a' = E₂ * Q₁ * a * b')
    (h2 : ν₁ * b = ν₂ * a) (h3 : μ₁ * d = μ₂ * c) (h4 : a' * o₁ * d = c * o₂ * b') :
    E₁ / (Q₁ * ν₁) * (μ₁ / o₁) = E₂ / (Q₂ * ν₂) * (μ₂ / o₂) := by
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hQ₁ hν₁) ho₁) (mul_ne_zero (mul_ne_zero hQ₂ hν₂) ho₂)]
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hb ha') ha) hd)
  linear_combination (μ₁ * d * ν₂ * a * o₂) * h1 + (E₂ * Q₁ * a * b' * ν₂ * a * o₂) * h3 -
    (E₂ * Q₁ * a * b' * μ₂ * c * o₂) * h2 - (E₂ * μ₂ * Q₁ * ν₁ * b * a) * h4
end Formalism.HermitianLattices.Ext.L3.LIOrb
