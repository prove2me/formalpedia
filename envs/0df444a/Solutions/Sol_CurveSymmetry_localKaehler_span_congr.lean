-- Prove2me | solution 1 for CurveSymmetry.localKaehler_span_congr
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:13.082418+00:00
-- url     : https://prove2.me/submissions/04a4551d-6864-4daf-9138-937b16b94541

-- Solution generated from lean/LocalDifferentials.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_08_Differentials
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama

section
open CurveSymmetry
set_option autoImplicit false
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
  [Module.Finite A Ω[A⁄R]]
theorem solution {u u' : A}
    (hres : ∀ x : A, ∃ r : R, x - algebraMap R A r ∈ IsLocalRing.maximalIdeal A)
    (hu : IsLocalRing.maximalIdeal A = Ideal.span {u})
    (hu' : IsLocalRing.maximalIdeal A = Ideal.span {u'}) :
    Submodule.span A {KaehlerDifferential.D R A u} =
      Submodule.span A {KaehlerDifferential.D R A u'} := by
  rw [localKaehler_span_eq_top hres hu, localKaehler_span_eq_top hres hu']
end

#print axioms solution
