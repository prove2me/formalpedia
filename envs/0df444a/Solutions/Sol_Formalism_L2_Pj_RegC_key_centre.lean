-- Prove2me | solution 1 for Formalism.L2.Pj.RegC.key_centre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:02.1491+00:00
-- url     : https://prove2.me/submissions/a07a3953-188c-4aa2-8a9a-67f50ea8c46b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Theorems.Thm_Formalism_L2_Pj_RegA_reg_vertical_e
import Theorems.Thm_Formalism_L2_Pj_RegB_mem_loc_of_heightOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_regVert_valuationRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_reg_horizontal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.L2.Pj.RegC
open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
private theorem hdvr_lemma {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (f : FractionRing A)
    (hno : ¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) :
    ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  haveI := ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing P hP
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (A := A) f
  have hb0' : algebraMap A (FractionRing A) b0 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0
  have h1P : (1 : A) ∉ P := (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime P) a0)
    (algebraMap A (Localization.AtPrime P) b0)
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    have h1 : algebraMap A (Localization.AtPrime P) (a0 * r) =
        algebraMap A (Localization.AtPrime P) (b0 * s) := by
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 h1
    have hK : algebraMap A (FractionRing A) (u * (a0 * r)) =
        algebraMap A (FractionRing A) (u * (b0 * s)) := by rw [hu]
    simp only [map_mul] at hK
    have ha0 : algebraMap A (FractionRing A) a0 ≠ 0 := by
      intro h0
      apply hno
      exact ⟨0, 1, h1P, by simp [h0]⟩
    by_cases hr : (u : A) * r ∈ P
    · refine ⟨u * r, u * s, hr, ?_, ?_⟩
      · exact P.primeCompl.mul_mem u.2 s.2
      · rw [map_mul, map_mul, inv_div, div_mul_eq_mul_div, div_eq_iff ha0]
        linear_combination -1 * hK
    · exfalso
      apply hno
      refine ⟨u * s, u * r, hr, ?_⟩
      rw [map_mul, map_mul, div_mul_eq_mul_div, div_eq_iff hb0']
      linear_combination hK
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    have h1 : algebraMap A (Localization.AtPrime P) (b0 * r) =
        algebraMap A (Localization.AtPrime P) (a0 * s) := by
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 h1
    have hK : algebraMap A (FractionRing A) (u * (b0 * r)) =
        algebraMap A (FractionRing A) (u * (a0 * s)) := by rw [hu]
    simp only [map_mul] at hK
    exfalso
    apply hno
    refine ⟨u * r, u * s, P.primeCompl.mul_mem u.2 s.2, ?_⟩
    rw [map_mul, map_mul, div_mul_eq_mul_div, div_eq_iff hb0']
    linear_combination -1 * hK
end Formalism.L2.Pj.RegC
end

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.RegC
open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
namespace Formalism.L2.Pj.RegC
theorem _root_.solution {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A) (e : A) (he : e ≠ 0)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (qq : Ideal A) [qq.IsPrime] (hqq : qq ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) :
    ∃ a s : A, s ∉ qq ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  haveI : IsNoetherianRing A := by
    first
    | exact Algebra.FiniteType.isNoetherianRing O A
    | infer_instance
  refine Formalism.L2.Pj.RegB.mem_loc_of_heightOne qq f (fun P hP h1 hle => ?_)
  haveI := hP
  by_cases hv : Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P
  · exact Formalism.L2.Pj.RegA.reg_vertical_e f e he hf P h1 hv
  · refine ReciprocityTheory.ChartRestriction.G.T0.reg_horizontal P hv ?_ e he f (hdvr_lemma P h1 f) hf
    intro htop
    apply hqq
    rw [eq_top_iff, ← htop]
    exact sup_le_sup_right hle _
end Formalism.L2.Pj.RegC
