-- Prove2me | solution 1 for Formalism.L2.DIV.conj_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:33:50.426641+00:00
-- url     : https://prove2.me/submissions/bfc92826-a101-4d3e-bfee-891459fa28c4

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (τ : Qb →+* ℂ) {N : ℕ} (hN : 0 < N) {z : Qb} (hz : z ∈ mus N) :
    starRingEnd ℂ (τ z) = τ z⁻¹ := by
  have h1 : (τ z) ^ N = 1 := by rw [← map_pow, show z ^ N = 1 from hz, map_one]
  rw [map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hN.ne')]
end Formalism.L2.DIV
