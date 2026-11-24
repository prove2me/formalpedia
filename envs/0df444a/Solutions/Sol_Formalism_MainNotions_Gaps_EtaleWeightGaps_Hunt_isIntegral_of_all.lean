-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.isIntegral_of_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:13.051808+00:00
-- url     : https://prove2.me/submissions/9709e77e-a47b-48a6-aa64-86cab8b916b3

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_IsIntegralOfAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
theorem _root_.solution (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [IsArtinianRing A] [IsReduced A] (a : A)
    (h : ∀ m : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk m.asIdeal a)) : IsIntegral O a := by
  classical
  haveI : Finite (MaximalSpectrum A) := by
    haveI := (IsArtinianRing.setOf_isMaximal_finite A).to_subtype
    exact Finite.of_injective
      (fun m : MaximalSpectrum A => (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal A | I.IsMaximal}))
      (fun x y hxy => MaximalSpectrum.ext (congrArg Subtype.val hxy))
  letI := Fintype.ofFinite (MaximalSpectrum A)
  choose p hp hpa using fun m : MaximalSpectrum A => h m
  have hmem : ∀ m : MaximalSpectrum A, Polynomial.aeval a (p m) ∈ m.asIdeal := by
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : (Ideal.Quotient.mk m.asIdeal) (Polynomial.aeval a (p m)) =
        Polynomial.aeval (Ideal.Quotient.mk m.asIdeal a) (p m) := by
      rw [← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
    rw [e, Polynomial.aeval_def]
    exact hpa m
  have hzero : ∀ x : A, (∀ m : MaximalSpectrum A, x ∈ m.asIdeal) → x = 0 := by
    intro x hx
    have hj : x ∈ Ideal.jacobson (⊥ : Ideal A) := by
      rw [Ideal.jacobson]
      refine Ideal.mem_sInf.mpr ?_
      rintro J ⟨-, hJ⟩
      exact hx ⟨J, hJ⟩
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    have hxn : x ^ n = 0 := by
      have := Ideal.pow_mem_pow hj n
      rw [hn] at this
      exact (Submodule.mem_bot _).mp this
    exact IsReduced.eq_zero x ⟨n, hxn⟩
  refine ⟨∏ m, p m, Polynomial.monic_prod_of_monic _ _ fun m _ => hp m, ?_⟩
  rw [← Polynomial.aeval_def, map_prod]
  apply hzero
  intro m
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
  exact Ideal.mul_mem_right _ _ (hmem m)
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
