-- Prove2me | solution 1 for Formalism.MainNotions.J.ef_one_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:58.371061+00:00
-- url     : https://prove2.me/submissions/eeda22cb-55e7-49de-8da7-939d3a717d2c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_ef_pos
import Theorems.Thm_Formalism_MainNotions_J_sum_ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime)
    (h : (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by
  intro P hP
  have h1 : ∑ _Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K), 1 =
      ∑ Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
        (span {(p : ℤ)}).ramificationIdx' Q * (span {(p : ℤ)}).inertiaDeg' Q := by
    rw [sum_ef K p hp, ← h, Finset.sum_const, smul_eq_mul, mul_one]
  exact ((Finset.sum_eq_sum_iff_of_le (fun Q hQ => ef_pos K p hp Q hQ)).mp h1 P hP).symm
end Formalism.MainNotions.J
