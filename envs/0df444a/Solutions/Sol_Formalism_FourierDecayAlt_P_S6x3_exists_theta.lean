-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:25.824032+00:00
-- url     : https://prove2.me/submissions/e85f9c53-a312-4600-a1d1-eec08452623c

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_trace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g)
    (hU : UnramAbove E g) :
    ∃ θ w : 𝓞 E, (θ : E) + complexConj E θ = 1 + (g : E) * w := by
  set F := maximalRealSubfield E with hF
  let I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  have key : I ⊔ Ideal.span {(g : 𝓞 F)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgP : (g : 𝓞 F) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hP0 : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hgP
      exact hg.ne' (by exact_mod_cast hgP)
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hP0 hP.ne_top
    have hPF : ((P : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      simpa using hP0
    rw [FractionalIdeal.mem_inv_iff hPF] at hx
    have hxP : ∀ p ∈ P, ∃ z : 𝓞 F, x * (p : F) = z := by
      intro p hp
      have := hx (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨p, hp, rfl⟩)
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).mp this
      exact ⟨z, hz.symm⟩

    have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
    have hdual : algebraMap F E x ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨a0, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
      have h1 : Algebra.traceForm F E (algebraMap F E x) (algebraMap (𝓞 E) E a0)
          = x * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) a0) := by
        rw [Algebra.traceForm_apply, ← Algebra.smul_def, map_smul, smul_eq_mul,
          Algebra.algebraMap_intTrace (L := E)]
      rw [h1]
      obtain ⟨z, hz⟩ := hxP (Algebra.intTrace (𝓞 F) (𝓞 E) a0)
        (hle (Ideal.mem_sup_left ⟨a0, rfl⟩))
      exact ⟨z, hz.symm⟩
    obtain ⟨d, hd, j, hj, hdj⟩ := Ideal.isCoprime_iff_exists.mp hU
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hj
    have hd' : algebraMap (𝓞 E) E d ∈
        (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
      rw [← coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩
    rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.dual_ne_zero _ _ h10)] at hd'
    obtain ⟨z1, hz1⟩ := (FractionalIdeal.mem_one_iff _).mp (hd' _ hdual)
    obtain ⟨z2, hz2⟩ := hxP _ hgP
    have hxE : algebraMap F E x = algebraMap (𝓞 E) E (z1 + y * algebraMap (𝓞 F) (𝓞 E) z2) := by
      have e1 : algebraMap (𝓞 E) E d + algebraMap (𝓞 E) E y * (g : E) = 1 := by
        have := congrArg (algebraMap (𝓞 E) E) hdj
        simpa using this
      have e2 : algebraMap F E x * (g : E) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z2) := by
        have := congrArg (algebraMap F E) hz2
        rw [map_mul] at this
        have e4 : algebraMap F E (((g : 𝓞 F) : 𝓞 F) : F) = (g : E) := by simp
        rw [e4] at this
        exact this
      rw [map_add, map_mul, hz1, ← e2]
      linear_combination (-(algebraMap F E x)) * e1
    have hint : IsIntegral ℤ x := by
      have : IsIntegral ℤ (algebraMap F E x) := by
        rw [hxE]; exact RingOfIntegers.isIntegral_coe _
      exact (isIntegral_algebraMap_iff (algebraMap F E).injective).mp this
    exact hx1 ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hint⟩, rfl⟩)
  have h1 : (1 : 𝓞 F) ∈ I ⊔ Ideal.span {(g : 𝓞 F)} := by rw [key]; trivial
  obtain ⟨i, ⟨θ, rfl⟩, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  refine ⟨θ, -algebraMap (𝓞 F) (𝓞 E) w, ?_⟩
  rw [← trace_eq, ← Algebra.algebraMap_intTrace (A := 𝓞 F) (B := 𝓞 E)]
  have := congrArg (fun t : 𝓞 F => algebraMap F E (algebraMap (𝓞 F) F t)) hij
  simp only [map_add, map_mul, map_one, map_natCast] at this
  have e3 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) w) = algebraMap F E (algebraMap (𝓞 F) F w) := rfl
  have e5 : ((-algebraMap (𝓞 F) (𝓞 E) w : 𝓞 E) : E)
      = -algebraMap F E (algebraMap (𝓞 F) F w) := by
    rw [← e3]; exact map_neg (algebraMap (𝓞 E) E) _
  rw [e5]
  linear_combination this
end Formalism.FourierDecayAlt.P.S6x3
