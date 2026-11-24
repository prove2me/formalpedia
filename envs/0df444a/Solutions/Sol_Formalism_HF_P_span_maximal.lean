-- Prove2me | solution 1 for Formalism.HF.P.span_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:11.239093+00:00
-- url     : https://prove2.me/submissions/095cc612-7e50-4039-b015-3569f7c506cb

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Filter Topology Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (p : ℕ) (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := by
  have hprime : (span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  have hne : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  exact hprime.isMaximal hne
end Formalism.HF.P
