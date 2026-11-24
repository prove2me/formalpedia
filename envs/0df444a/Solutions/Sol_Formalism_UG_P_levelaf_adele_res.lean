-- Prove2me | solution 1 for Formalism.UG.P.levelaf_adele_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:52.396646+00:00
-- url     : https://prove2.me/submissions/e109e51e-2a1b-4892-b717-03f9d55c59ec

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_int_mem_v
import Theorems.Thm_Formalism_UG_P_levelaf_finite_places
import Theorems.Thm_Formalism_UG_P_levelaf_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_glint_finite_quotient_of_dvr
import Theorems.Thm_Formalism_UG_P_glint_finite_residueField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.UG.P
theorem _root_.solution (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ T : Set (FiniteAdeleRing (𝓞 F) F), T.Finite ∧ T ⊆ intAd F ∧
      ∀ a ∈ intAd F, ∃ t ∈ T, ∃ y ∈ intAd F, a = t + algebraMap (𝓞 F) _ D * y := by
  classical
  set P := {v : HeightOneSpectrum (𝓞 F) | Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1}
    with hPdef
  have hP : P.Finite := levelaf_finite_places D hD
  have : Finite P := hP.to_subtype
  let Dv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F :=
    fun v => ⟨_, levelaf_int_mem_v v D⟩
  have hDv0 : ∀ v, Dv v ≠ 0 := by
    intro v h
    exact levelaf_algebraMap_ne_zero v D hD (congrArg Subtype.val h)
  have : ∀ v : P, Finite ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸
      Ideal.span {Dv v}) := fun v =>
    glint_finite_quotient_of_dvr (glint_finite_residueField (v : HeightOneSpectrum (𝓞 F))) _
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hDv0 v)
  let φ : intAd F → ∀ v : P, (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸
      Ideal.span {Dv v} :=
    fun a v => Ideal.Quotient.mk _ ⟨(a : FiniteAdeleRing (𝓞 F) F) v, a.2 v⟩
  have key : ∀ a a' : intAd F, φ a = φ a' → ∃ y ∈ intAd F,
      (a : FiniteAdeleRing (𝓞 F) F) = a' + algebraMap (𝓞 F) _ D * y := by
    intro a a' h
    have hle : ∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v - (a' : FiniteAdeleRing (𝓞 F) F) v) ≤
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
      intro v
      by_cases hv : v ∈ P
      · have := congrFun h ⟨v, hv⟩
        simp only [φ] at this
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at this
        obtain ⟨z, hz⟩ := this
        have hz' := congrArg Subtype.val hz
        simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, Dv] at hz'
        rw [← hz', Valuation.map_mul]
        calc _ ≤ 1 * Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) :=
              mul_le_mul_left ((mem_adicCompletionIntegers _ _ _).1 z.2) _
          _ = _ := one_mul _
      · have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1 :=
          le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv)
        rw [h1]
        exact (mem_adicCompletionIntegers _ _ _).1 (sub_mem (a.2 v) (a'.2 v))
    set y : FiniteAdeleRing (𝓞 F) F :=
      algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ * ((a : FiniteAdeleRing (𝓞 F) F) - a') with hy
    refine ⟨y, fun v => ?_, ?_⟩
    · show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ *
          ((a : FiniteAdeleRing (𝓞 F) F) v - (a' : FiniteAdeleRing (𝓞 F) F) v) ∈ _
      have hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)
      rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
        ← IsScalarTower.algebraMap_apply]
      calc _ ≤ (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D))⁻¹ *
            Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := mul_le_mul_right (hle v) _
        _ = 1 := inv_mul_cancel₀ hne
    · have hD' : algebraMap (𝓞 F) F D ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
      rw [hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F), ← mul_assoc,
        ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]
      ring
  let rep : (∀ v : P, (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸
      Ideal.span {Dv v}) → intAd F := fun q => if h : ∃ a, φ a = q then h.choose else 0
  refine ⟨Set.range (fun q => ((rep q : intAd F) : FiniteAdeleRing (𝓞 F) F)), Set.finite_range _,
    ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩; exact (rep q).2
  · intro a ha
    have hex : ∃ b, φ b = φ ⟨a, ha⟩ := ⟨_, rfl⟩
    have hrep : φ (rep (φ ⟨a, ha⟩)) = φ ⟨a, ha⟩ := by
      simp only [rep, dif_pos hex]; exact hex.choose_spec
    obtain ⟨y, hy, e⟩ := key ⟨a, ha⟩ _ hrep.symm
    exact ⟨_, ⟨_, rfl⟩, y, hy, e⟩
end Formalism.UG.P
