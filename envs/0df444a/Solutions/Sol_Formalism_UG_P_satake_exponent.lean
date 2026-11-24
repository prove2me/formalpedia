-- Prove2me | solution 1 for Formalism.UG.P.satake_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:03.454803+00:00
-- url     : https://prove2.me/submissions/cd99f0ee-02be-4abc-98fa-1fe7ccd1f833

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_cpow_prod
import Theorems.Thm_Formalism_UG_P_satakeInv_two_mul
import Theorems.Thm_Formalism_UG_P_satake_two_le_qV


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
theorem _root_.solution (α : Fin n → ℂ) (S : Finset (Fin n)) :
    ((qV F v : ℂ)) ^ satakeInv Finset.univ S *
      ∏ a ∈ S, (α a * (qV F v : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (a : ℂ)) / 2))) =
      (qV F v : ℂ) ^ (((S.card : ℂ) * ((n : ℂ) - S.card)) / 2) * ∏ a ∈ S, α a := by
  have hq : (qV F v : ℂ) ≠ 0 := by
    have := satake_two_le_qV v
    exact_mod_cast (show qV F v ≠ 0 by omega)
  rw [Finset.prod_mul_distrib, satake_cpow_prod _ hq, ← Complex.cpow_natCast, mul_left_comm,
    ← Complex.cpow_add _ _ hq, mul_comm]
  congr 2
  have h := satakeInv_two_mul S
  have h' : 2 * (satakeInv Finset.univ S : ℂ) =
      ∑ a ∈ S, ((n : ℂ) - 1 - 2 * ((a : ℕ) : ℂ)) + (S.card : ℂ) * ((n : ℂ) - S.card) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
  linear_combination h' / 2
end Formalism.UG.P
