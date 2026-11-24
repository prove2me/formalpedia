-- Prove2me | solution 1 for Formalism.UG.P.prod_pow_sub_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:45.737867+00:00
-- url     : https://prove2.me/submissions/6099cd8d-c3d7-4ccb-a279-39bedada3917

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {q : ℤ} (hq : 2 ≤ q) {j n : ℕ} (hj : j ≤ n) :
    ∏ i ∈ Finset.range j, (q ^ (n - i) - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi' := Finset.mem_range.1 hi
  have : 1 < q ^ (n - i) := one_lt_pow₀ (by omega) (by omega)
  omega
end Formalism.UG.P
