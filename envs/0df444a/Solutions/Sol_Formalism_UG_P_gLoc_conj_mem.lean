-- Prove2me | solution 1 for Formalism.UG.P.gLoc_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:55.987291+00:00
-- url     : https://prove2.me/submissions/c1037214-52df-442d-9503-d9bf560d1c58

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {G : Type} [Group G] (K : Subgroup G) (P : G) (hP : P ∈ K) (g : G) :
    g ∈ K ↔ P⁻¹ * g * P ∈ K := by
  constructor
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hP) h) hP
  · intro h
    have := K.mul_mem (K.mul_mem hP h) (K.inv_mem hP)
    simpa [mul_assoc] using this
end Formalism.UG.P
