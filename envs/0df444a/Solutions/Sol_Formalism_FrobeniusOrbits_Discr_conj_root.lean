-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.conj_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:07.727491+00:00
-- url     : https://prove2.me/submissions/32ffaf7d-d857-4297-a437-f09aa868c17c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Discr
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) : starRingEnd ℂ z = z⁻¹ := by
  have h1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hm
  have h2 : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  exact eq_inv_of_mul_eq_one_right h2
end Formalism.FrobeniusOrbits.Discr
