-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.BE.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:38.499607+00:00
-- url     : https://prove2.me/submissions/00fbfc6a-3e82-4b41-bfbb-465bee79da7b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.HermitianLattices.Ext.L3.WA.BE
namespace Formalism.HermitianLattices.Ext.L3.WA.BE
theorem _root_.solution {R : Type*} [CommRing R] [IsDedekindDomain R] {I P Q : Ideal R} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hQ : Q.IsPrime) :
    ∃ r ∈ I, r ≠ 0 ∧ ∃ s : R, s ∉ P ∧ s ∉ Q ∧ ∀ x ∈ I, ∃ y : R, s * x = r * y := by
  have hIP : ∀ {P' : Ideal R}, P'.IsPrime → ¬ (I ≤ I * P') := by
    intro P' hP' hle
    have e : I * P' = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) hle
    exact hP'.ne_top (mul_left_cancel₀ (by rwa [Ideal.zero_eq_bot]) e)
  have hnot : ¬ ((I : Set R) ⊆ ((I * P : Ideal R) : Set R) ∪ ((I * Q : Ideal R) : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hIP hP h
    · exact hIP hQ h
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr.1 (Submodule.zero_mem _)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {r} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrI))
  have hJP : ∀ {P' : Ideal R}, r ∉ I * P' → ¬ (J ≤ P') := by
    intro P' hr' hJ'
    apply hr'
    have hrr : r ∈ Ideal.span {r} := Ideal.mem_span_singleton_self r
    rw [hJ] at hrr
    exact Ideal.mul_mono_right hJ' hrr
  have hnot2 : ¬ ((J : Set R) ⊆ (P : Set R) ∪ (Q : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hJP hr.1 h
    · exact hJP hr.2 h
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.mp hnot2
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hs
  refine ⟨r, hrI, hr0, s, hs.1, hs.2, fun x hx => ?_⟩
  have hmem : s * x ∈ Ideal.span {r} := by
    rw [hJ, mul_comm s x]
    exact Ideal.mul_mem_mul hx hsJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨y, by rw [← hy, mul_comm]⟩
end Formalism.HermitianLattices.Ext.L3.WA.BE
