-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.index_ideal_smul_top_le_norm_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:48.180336+00:00
-- url     : https://prove2.me/submissions/1fbb9540-503e-4e26-b1b7-eb7e05ccb5c0

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {E : Type} [Field E] [NumberField E] (p : Ideal (𝓞 E)) [hp : p.IsMaximal] (hp0 : p ≠ ⊥)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (k : ℕ) (htf : TF E X)
    (hli : LIB E X k) :
    (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≠ 0 ∧
      (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index ≤ Ideal.absNorm p ^ k := by
  classical
  letI : Field (𝓞 E ⧸ p) := Ideal.Quotient.field p
  have hN0 : Ideal.absNorm p ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hNF : Nat.card (𝓞 E ⧸ p) = Ideal.absNorm p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ p) := Nat.finite_of_card_ne_zero (by rwa [hNF])
  haveI : Module.Finite (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  haveI : Finite (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) := Module.finite_of_finite (𝓞 E ⧸ p)
  have hsm : ∀ (a : 𝓞 E) (q : X ⧸ (p • (⊤ : Submodule (𝓞 E) X))),
      (Ideal.Quotient.mk p a) • q = a • q := by
    intro a q; rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hdim : Module.finrank (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) ≤ k := by
    set b := Module.finBasis (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X)))
    choose v hv using fun i => Submodule.Quotient.mk_surjective _ (b i)
    have hli' : LinearIndependent (𝓞 E) v := by
      rw [linearIndependent_iff']
      intro s g hg i0 hi0
      by_contra hne
      set Jg : Ideal (𝓞 E) := Ideal.span (g '' ↑s)
      have hJ0 : Jg ≠ ⊥ := by
        intro h; apply hne
        have : g i0 ∈ Jg := Ideal.subset_span ⟨i0, hi0, rfl⟩
        rw [h] at this; exact (Submodule.mem_bot _).1 this
      have hp2 : 2 ≤ Ideal.absNorm p := by
        have : Ideal.absNorm p ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hp.ne_top
        omega
      have hex : ∃ e, ¬ Jg ≤ p ^ (e + 1) := by
        by_contra hall
        push_neg at hall
        have hN : Ideal.absNorm Jg ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
        have h0 := Ideal.absNorm_dvd_absNorm_of_le (hall (Ideal.absNorm Jg))
        rw [map_pow] at h0
        have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h0
        have h2 : Ideal.absNorm Jg < 2 ^ (Ideal.absNorm Jg + 1) :=
          (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
        have h3 : 2 ^ (Ideal.absNorm Jg + 1) ≤ Ideal.absNorm p ^ (Ideal.absNorm Jg + 1) :=
          Nat.pow_le_pow_left hp2 _
        omega
      set e := Nat.find hex with he_def
      have he1 : ¬ Jg ≤ p ^ (e + 1) := Nat.find_spec hex
      have he : Jg ≤ p ^ e := by
        rcases Nat.eq_zero_or_pos e with h0 | hpos
        · rw [h0, pow_zero, Ideal.one_eq_top]; exact le_top
        · have := Nat.find_min hex (show e - 1 < e by omega)
          rw [Nat.sub_add_cancel hpos] at this
          exact not_not.1 this
      have hpe : p ^ e ≠ ⊥ := pow_ne_zero e hp0
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpe
      obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
      have hA0 : A ≠ ⊥ := by
        rintro rfl
        rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hA
        exact hc0 hA
      have hnot : ¬ Jg * A ≤ p ^ (e + 1) * A := by
        intro h
        apply he1
        have h' : p ^ (e + 1) * A ∣ Jg * A := Ideal.dvd_iff_le.2 h
        exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_right hA0).1 h')
      have hgen : ∃ i ∈ s, ∃ x ∈ A, g i * x ∉ p ^ (e + 1) * A := by
        by_contra hall
        push_neg at hall
        apply hnot
        have hcol : Jg ≤ (p ^ (e + 1) * A).colon A := by
          rw [Ideal.span_le]
          rintro _ ⟨i, hi, rfl⟩
          exact Submodule.mem_colon.2 fun x hx => hall i hi x hx
        exact Ideal.mul_le.2 fun r hr x hx => Submodule.mem_colon.1 (hcol hr) x hx
      obtain ⟨i1, hi1, x, hx, hnx⟩ := hgen
      have hy : ∀ i ∈ s, ∃ y : 𝓞 E, y * c = g i * x := by
        intro i hi
        have : g i * x ∈ Ideal.span {c} := by
          rw [hA]
          exact Ideal.mul_mem_mul (he (Ideal.subset_span ⟨i, hi, rfl⟩)) hx
        exact Ideal.mem_span_singleton'.1 this
      choose! y hy using hy
      have hrel : ∑ i ∈ s, y i • v i = 0 := by
        apply htf c hc0
        rw [Finset.smul_sum]
        have : ∑ i ∈ s, c • y i • v i = x • ∑ i ∈ s, g i • v i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [smul_smul, smul_smul, mul_comm c, hy i hi, mul_comm]
        rw [this, hg, smul_zero]
      have hrelQ : ∑ i ∈ s, (Ideal.Quotient.mk p (y i)) • b i = 0 := by
        have := congrArg (Submodule.mkQ (p • (⊤ : Submodule (𝓞 E) X))) hrel
        rw [map_sum, map_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsm, map_smul, Submodule.mkQ_apply, hv]
      have hy1 : Ideal.Quotient.mk p (y i1) = 0 :=
        linearIndependent_iff'.1 b.linearIndependent s _ hrelQ i1 hi1
      rw [Ideal.Quotient.eq_zero_iff_mem] at hy1
      apply hnx
      rw [← hy i1 hi1, pow_succ', mul_assoc, ← hA]
      exact Ideal.mul_mem_mul hy1 (Ideal.mem_span_singleton_self c)
    simpa using hli (Fin _) v hli'
  have hidx : (p • (⊤ : Submodule (𝓞 E) X)).toAddSubgroup.index =
      Ideal.absNorm p ^ Module.finrank (𝓞 E ⧸ p) (X ⧸ (p • (⊤ : Submodule (𝓞 E) X))) := by
    rw [← hNF, ← Module.natCard_eq_pow_finrank]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hidx]; exact pow_ne_zero _ hN0
  · rw [hidx]; exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN0) hdim
end Formalism.HermitianLatticeCounting.P
