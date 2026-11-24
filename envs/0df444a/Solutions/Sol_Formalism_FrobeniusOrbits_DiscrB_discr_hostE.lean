-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.discr_hostE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:52.606837+00:00
-- url     : https://prove2.me/submissions/077e25a2-3954-443e-b28f-ce9e348dafe5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_isCoprime_odd_two_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_adjoin_eq_top_of_map
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_exp_E
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_odd_of_mod
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_bE_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_ConjReal_aE_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_finrank_cmField
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_eq_adjoin
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_finrank_real_subfield
import Theorems.Thm_Formalism_FrobeniusOrbits_finrank_cmField
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HF_Final_mqDiscr
import Theorems.Thm_Formalism_HF_P_adjoin_top_of_lift
import Theorems.Thm_Formalism_HF_P_nrRealPlaces_zero
import Theorems.Thm_Formalism_Q3_mqGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.DiscrB
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]
variable {e q d : ℕ} {ζ a b : L}
namespace Formalism.FrobeniusOrbits.DiscrB
theorem _root_.solution (h1 : DiscrMaximalRealCyclotomic) (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b) :
    discr (hostE ζ a b) = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) := by
  classical
  have hqd := hH.toHypOdd
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := hH
  have hne : q ≠ d := hqd.2.2.1
  let α₀ : Fin 2 → hostE ζ a b := ![aE ζ a b, bE ζ a b]
  let K₁ : IntermediateField ℚ (hostE ζ a b) := adjoin ℚ (Set.range α₀)
  let K₂ : IntermediateField ℚ (hostE ζ a b) := adjoin ℚ {thE ζ a b}
  let β : Fin 2 → K₁ := fun i => ⟨α₀ i, subset_adjoin _ _ ⟨i, rfl⟩⟩
  let qq : Fin 2 → ℕ := ![q, d]
  have hβ : Formalism.Q3.IsMQ (fun i => -(qq i : ℤ)) β := by
    refine ⟨fun i => Subtype.ext ?_, ?_⟩
    · fin_cases i
      · simpa [β, α₀, qq] using ConjReal.aE_sq h
      · simpa [β, α₀, qq] using bE_sq h
    · apply Formalism.HF.P.adjoin_top_of_lift
      rw [← Set.range_comp]
      rfl
  have hqq : ∀ i, (qq i).Prime ∧ qq i % 4 = 3 := by
    intro i; fin_cases i
    · exact ⟨hqp, by simp [qq]; omega⟩
    · exact ⟨hdp, by simp [qq]; omega⟩
  have hinj : Function.Injective qq := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [qq]
  have hd₁ : discr K₁ = (q : ℤ) ^ 2 * (d : ℤ) ^ 2 := by
    rw [Formalism.HF.Final.mqDiscr 2 qq (by norm_num) hqq hinj K₁ β hβ]
    simp [Fin.prod_univ_two, qq]
  have hGal₁ : IsGalois ℚ K₁ := (Formalism.Q3.mqGalois 2 K₁ _ β hβ
    (fun i => neg_ne_zero.2 (Nat.cast_ne_zero.2 (hqq i).1.ne_zero))).1
  let ι : hostE ζ a b →ₐ[ℚ] L := ((hostE ζ a b).val : hostE ζ a b →+* L).toRatAlgHom
  have hmap : K₂.map ι = F1 ζ := by
    rw [adjoin_map, Set.image_singleton]
    rfl
  let f₂ := (K₂.equivMap ι).trans (equivOfEq hmap)
  have hd₂ : discr K₂ = 2 ^ (2 ^ e * (e + 1) - 1) := by
    rw [discr_eq_discr_of_algEquiv _ f₂.toRingEquiv.toRatAlgEquiv, h1 e L ζ h.1]
  have hf₂ : Module.finrank ℚ K₂ = 2 ^ e := by
    rw [f₂.toLinearEquiv.finrank_eq]
    exact RealCyclotomicSubfield.finrank_real_subfield h.1
  have hcop : IsCoprime (discr K₁) (discr K₂) := by
    rw [hd₁, hd₂]
    apply isCoprime_odd_two_pow
    exact ((odd_of_mod (by omega)).pow).mul ((odd_of_mod (by omega)).pow)
  have hld := linearDisjoint_of_isGalois_isCoprime_discr (hostE ζ a b) K₁ K₂ hcop
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    rw [← adjoin_union]
    refine adjoin_eq_top_of_map ι _ ℚ⟮ζ + ζ⁻¹, a, b⟯ ?_
      (fun x => by rw [← Galois.hostE_eq_adjoin]; exact x.2)
    congr 1
    ext x
    simp [α₀, aE, bE, thE, ι]
    tauto
  have hf₁ : Module.finrank ℚ K₁ = 4 := by
    have := hld.finrank_sup
    rw [hsup, finrank_top', finrank_cmField hqd h, hf₂] at this
    have h4 : 2 ^ (e + 2) = 4 * 2 ^ e := by ring
    rw [h4] at this
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm
  have hnat := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (hostE ζ a b) K₁ K₂ hld hsup
    (isCoprime_differentIdeal_of_isCoprime_discr (hostE ζ a b) hcop)
  have hr : nrRealPlaces (hostE ζ a b) = 0 :=
    Formalism.HF.P.nrRealPlaces_zero (aE ζ a b) (-(q : ℤ)) (by have := hqp.pos; omega)
      (by rw [ConjReal.aE_sq h]; push_cast; rfl)
  have hc : nrComplexPlaces (hostE ζ a b) = 2 ^ (e + 1) := by
    have := card_add_two_mul_card_eq_rank (K := hostE ζ a b)
    rw [hr, finrank_cmField hqd h, pow_succ] at this
    linarith
  have hs : (discr (hostE ζ a b)).sign = 1 := by
    rw [sign_discr, hc]
    exact Even.neg_one_pow ⟨2 ^ e, by ring⟩
  rw [← Int.sign_mul_natAbs (discr (hostE ζ a b)), hs, hnat, hd₁, hd₂, hf₁, hf₂, one_mul]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  push_cast
  rw [← pow_mul, exp_E, show 2 ^ (e + 1) = 2 * 2 ^ e by ring, pow_mul]
  ring
end Formalism.FrobeniusOrbits.DiscrB
