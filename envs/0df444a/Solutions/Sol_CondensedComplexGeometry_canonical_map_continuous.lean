-- Prove2me | solution 1 for CondensedComplexGeometry.canonical_map_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T19:08:08.828462+00:00
-- url     : https://prove2.me/submissions/98e31ae6-8974-4c3c-958f-b1e57ec72368

import Mathlib
import Definitions.Def_CondensedComplexGeometry_berkovich

set_option autoImplicit false

universe u

namespace CondensedComplexGeometry

theorem cm_mem (R : Type u) [CommRing R] [Algebra ℂ R] (f : ↥(ComplexCharacters R)) :
    (fun x => ‖f.1 x‖₊) ∈ BerkovichSpectrum R := by
  obtain ⟨φ, hφ⟩ := f.2
  refine ⟨fun x y => ?_, fun x y => ?_, fun c => ?_⟩
  · simp only [← hφ, map_mul, nnnorm_mul]
  · simp only [← hφ, map_add]; exact nnnorm_add_le _ _
  · simp only [← hφ, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]; rfl

noncomputable def cm_g (R : Type u) [CommRing R] [Algebra ℂ R] :
    ↥(ComplexCharacters R) → ↥(BerkovichSpectrum R) :=
  fun f => ⟨fun x => ‖f.1 x‖₊, cm_mem R f⟩

theorem cm_g_continuous (R : Type u) [CommRing R] [Algebra ℂ R] : Continuous (cm_g R) :=
  Continuous.subtype_mk (continuous_pi fun x =>
    continuous_nnnorm.comp ((continuous_apply x).comp continuous_subtype_val)) _

end CondensedComplexGeometry

open CondensedComplexGeometry in
theorem solution (R : Type u) [CommRing R] [Algebra ℂ R] :
    ∃ (g : ↥(ComplexCharacters R) → ↥(BerkovichSpectrum R)),
      Continuous g ∧ ∀ (f : ↥(ComplexCharacters R)) (x : R),
        ((g f).1 x : ℝ) = ‖f.1 x‖ :=
  ⟨cm_g R, cm_g_continuous R, fun _ _ => rfl⟩
