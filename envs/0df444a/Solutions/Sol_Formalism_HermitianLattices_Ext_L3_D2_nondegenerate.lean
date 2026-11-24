-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:10.509243+00:00
-- url     : https://prove2.me/submissions/082ea190-bd3c-49fa-84e1-b63bbfaa053f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) : h.Nondegenerate := by
  have key : ∀ x : V, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 := hd x hne φ
    rw [hx, map_zero, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩
end Formalism.HermitianLattices.Ext.L3.D2
