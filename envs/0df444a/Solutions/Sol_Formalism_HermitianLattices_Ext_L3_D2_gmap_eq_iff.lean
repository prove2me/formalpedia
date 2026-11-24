-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.gmap_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:03:20.1008+00:00
-- url     : https://prove2.me/submissions/b5f4bd66-b869-4921-9f3e-895b84da21c6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeMemOfMemSmulTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_glSub


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
theorem _root_.solution (a b : V ≃ₗ[K] V) (B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap a B = Formalism.HermitianLatticesTheory.gmap b B ↔ a⁻¹ * b ∈ glSub B := by
  rw [mem_glSub]
  constructor
  · intro e
    rw [autSub_gmap_mul, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro e
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, autSub_gmap_mul a, e]
end Formalism.HermitianLattices.Ext.L3.D2
