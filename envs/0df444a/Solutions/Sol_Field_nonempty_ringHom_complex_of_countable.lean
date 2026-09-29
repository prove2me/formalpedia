-- Prove2me | solution 1 for Field.nonempty_ringHom_complex_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/49ffa1c1-9056-5743-88c2-7a71f441c292

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Field_nonempty_ringHom_complex_of_countable

open Cardinal

universe u

theorem solution
    (K : Type u) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by
  classical
  haveI : FaithfulSMul ℚ K :=
    (faithfulSMul_iff_algebraMap_injective ℚ K).2 (algebraMap ℚ K).injective
  haveI : FaithfulSMul ℚ ℂ :=
    (faithfulSMul_iff_algebraMap_injective ℚ ℂ).2 (algebraMap ℚ ℂ).injective

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ

  have hct : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' (R := ℚ) _ ht
      mk_le_aleph0 (by rw [mk_complex]; exact aleph0_lt_continuum)

  have h1 : Cardinal.lift.{0} #s ≤ Cardinal.lift.{u} #t := by
    rw [← hct, mk_complex, lift_continuum]
    calc Cardinal.lift.{0} #s ≤ Cardinal.lift.{0} ℵ₀ := lift_le.2 mk_le_aleph0
      _ = ℵ₀ := lift_aleph0
      _ ≤ 𝔠 := aleph0_le_continuum
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.1 h1

  have hind : AlgebraicIndependent ℚ (fun i : s => ((e i : t) : ℂ)) :=
    ht.1.comp e e.injective
  set A := Algebra.adjoin ℚ (Set.range ((↑) : s → K)) with hA
  let g : A →ₐ[ℚ] ℂ :=
    (MvPolynomial.aeval (fun i : s => ((e i : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g :=
    (algebraicIndependent_iff_injective_aeval.1 hind).comp hs.1.aevalEquiv.symm.injective

  haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
  letI : Algebra A ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree A ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  haveI : Module.IsTorsionFree A K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  exact ⟨(IsAlgClosed.lift (R := A) (S := K) (M := ℂ)).toRingHom⟩

end S_Field_nonempty_ringHom_complex_of_countable
end P2MW
export P2MW.S_Field_nonempty_ringHom_complex_of_countable (solution)
