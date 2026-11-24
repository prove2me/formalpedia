-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:55.348744+00:00
-- url     : https://prove2.me/submissions/1f8d84ee-3150-4cc9-8e6e-42adfd0504d5

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (x : ℤᵐ⁰) :
    x < 1 ↔ x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
  induction x using WithZero.recZeroCoe with
  | zero => simp
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, WithZero.coe_le_coe]
    change Multiplicative.toAdd a < 0 ↔ Multiplicative.toAdd a ≤ -1
    omega
end Formalism.UG.P
