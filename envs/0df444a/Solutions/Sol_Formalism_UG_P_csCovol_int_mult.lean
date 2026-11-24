-- Prove2me | solution 1 for Formalism.UG.P.csCovol_int_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:12.543738+00:00
-- url     : https://prove2.me/submissions/67800b47-6cb0-4e54-a3a0-38aefe585dc2

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution {K : Type} [Field K] [NumberField K] (e : 𝓞 K) (he : e ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ c : 𝓞 K, (algebraMap ℤ (𝓞 K) n) = c * e := by
  obtain ⟨c, hc⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 K) e
  refine ⟨Algebra.intNorm ℤ (𝓞 K) e, ?_, c, by rw [hc, mul_comm]⟩
  first
  | exact Algebra.intNorm_ne_zero.mpr he
  | exact (Algebra.intNorm_eq_zero.not).mpr he
  | simpa using he
end Formalism.UG.P
