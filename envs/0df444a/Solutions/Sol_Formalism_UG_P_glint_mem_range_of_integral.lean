-- Prove2me | solution 1 for Formalism.UG.P.glint_mem_range_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:57.99115+00:00
-- url     : https://prove2.me/submissions/d2605b55-b4bc-4803-9e6c-3ac852773ee8

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (O : Subring L) (U : GL n L)
    (h1 : (U : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h2 : ((U⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    U ∈ (bc (n := n) O.subtype).range := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have inj : Function.Injective (RingHom.mapMatrix (m := n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext : 1
  simp only [bc, Units.coe_map]
  exact hA
end Formalism.UG.P
