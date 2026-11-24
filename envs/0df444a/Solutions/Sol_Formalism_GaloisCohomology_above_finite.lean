-- Prove2me | solution 1 for Formalism.GaloisCohomology.above_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:31.534862+00:00
-- url     : https://prove2.me/submissions/24e9fedf-5b6f-4690-8559-46fcbc9e472c

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_GaloisCohomology_GaloisCohomologyProofs_LdataNonempty
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open Formalism Formalism.GaloisCohomology
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]
namespace Formalism.GaloisCohomology
theorem _root_.solution : (Above F l).Finite := by
  have hl : ((l : ℕ) : 𝓞 F) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap (𝓞 F) F) h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact (Fact.out : l.Prime).ne_zero h2
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hl
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  show v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 F)}
  rw [Ideal.dvd_span_singleton]
  exact hv
end Formalism.GaloisCohomology
