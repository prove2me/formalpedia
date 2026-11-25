-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:46.915352+00:00
-- url     : https://prove2.me/submissions/76dbf157-3e1e-40ee-9818-a8308e393240

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexSSubInfEq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
private theorem exists_int_add_star_eq_one_of_isCMUnram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ θ : 𝓞 K, algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ) = 1 := by
  classical
  have hstarF : ∀ f : F, star (algebraMap F K f) = algebraMap F K f := fun f => (hF _).mpr ⟨f, rfl⟩
  have hint : ∀ c : 𝓞 F, IsIntegral ℤ (algebraMap F K (algebraMap (𝓞 F) F c)) := fun c =>
    (isIntegral_algebraMap_iff (algebraMap F K).injective).mpr
      (NumberField.RingOfIntegers.isIntegral_coe c)
  have hcompat : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) =
      algebraMap F K (algebraMap (𝓞 F) F x) := fun x => rfl
  let tr : 𝓞 K → K := fun θ => algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ)
  show ∃ θ : 𝓞 K, tr θ = 1
  by_contra hne
  push_neg at hne
  let I : Ideal (𝓞 F) :=
    { carrier := {a | ∃ θ : 𝓞 K, tr θ = algebraMap F K (algebraMap (𝓞 F) F a)}
      add_mem' := by
        rintro a b ⟨θ, hθ⟩ ⟨θ', hθ'⟩
        refine ⟨θ + θ', ?_⟩
        simp only [tr, map_add, star_add] at hθ hθ' ⊢
        linear_combination hθ + hθ'
      zero_mem' := ⟨0, by simp [tr]⟩
      smul_mem' := by
        rintro c a ⟨θ, hθ⟩
        refine ⟨algebraMap (𝓞 F) (𝓞 K) c * θ, ?_⟩
        simp only [tr, smul_eq_mul, map_mul, star_mul', hcompat, hstarF] at hθ ⊢
        linear_combination (algebraMap F K (algebraMap (𝓞 F) F c)) * hθ }
  have hI : (1 : 𝓞 F) ∉ I := by
    rintro ⟨θ, hθ⟩
    exact hne θ (by simpa using hθ)
  obtain ⟨𝔮, h𝔮, hI𝔮⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr hI)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔮 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = algebraMap F K (algebraMap (𝓞 F) F 0) := by
      rw [← hcompat, hx, map_zero, map_zero, map_zero]
    have h2 := IsFractionRing.injective (𝓞 F) F ((algebraMap F K).injective h1)
    rw [h2]
    exact 𝔮.zero_mem
  obtain ⟨P, hP, hP𝔮⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) 𝔮 hker
  obtain ⟨a, t, ht, hat⟩ := hK.2.2 P hP
  have hta : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K a := by rw [ht, star_star]
  have hdfix : star ((algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2) =
      (algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2 := by
    rw [star_pow, star_sub, ← ht, hta]
    ring
  obtain ⟨f, hf⟩ := (hF _).mp hdfix
  have hfi : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := K) (algebraMap F K).injective, hf]
    have := NumberField.RingOfIntegers.isIntegral_coe ((a - t) ^ 2)
    simpa using this
  let fO : 𝓞 F := ⟨f, hfi⟩
  have hfI : fO ∈ I := by
    refine ⟨a * (a - t), ?_⟩
    show algebraMap (𝓞 K) K (a * (a - t)) + star (algebraMap (𝓞 K) K (a * (a - t))) =
      algebraMap F K f
    rw [hf]
    simp only [map_mul, map_sub, star_mul', star_sub, ← ht, hta]
    ring
  have hmem : algebraMap (𝓞 F) (𝓞 K) fO ∈ P := by
    rw [← Ideal.mem_comap, hP𝔮]
    exact hI𝔮 hfI
  have heq : algebraMap (𝓞 F) (𝓞 K) fO = (a - t) ^ 2 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hcompat]
    show algebraMap F K f = _
    rw [hf]
    simp
  rw [heq] at hmem
  exact hat (hP.isPrime.mem_of_pow_mem 2 hmem)
end Formalism.HermitianLattices.Ext.L3.D2
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    ∃ θ : K, θ ∈ pK K 𝔭 0 ∧ θ + star θ = 1 := by
  obtain ⟨θ, hθ⟩ := exists_int_add_star_eq_one_of_isCMUnram hK hF
  exact ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_pK 𝔭 θ, hθ⟩
end Formalism.HermitianLattices.Ext.L3.D2
