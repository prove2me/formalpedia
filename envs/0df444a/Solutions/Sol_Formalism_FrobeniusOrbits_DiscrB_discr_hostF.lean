-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.discr_hostF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:53.361843+00:00
-- url     : https://prove2.me/submissions/f63ad227-c1db-4f58-8d49-f269970c3ce1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_isCoprime_odd_two_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_adjoin_eq_top_of_map
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_exp_F
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_odd_of_mod
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_finrank_real_subfield
import Theorems.Thm_Formalism_FrobeniusOrbits_finrank_hostF
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_hostF_iff_adjoin
import Theorems.Thm_Formalism_HF_Final_quadDiscr
import Theorems.Thm_Formalism_HF_P_adjoin_top_of_lift
import Theorems.Thm_Formalism_HF_quadDiscr
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
    discr (hostF ζ a b) = 2 ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e) := by
  classical
  have hqd := hH.toHypOdd
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := hH
  have hne : q ≠ d := hqd.2.2.1
  let ι : hostF ζ a b →ₐ[ℚ] L :=
    (((hostE ζ a b).val : hostE ζ a b →+* L).comp (hostF ζ a b).subtype).toRatAlgHom
  have hab : aE ζ a b * bE ζ a b ∈ hostF ζ a b :=
    (mem_hostF_iff_adjoin hqd h _).2 (subset_adjoin ℚ _ (by simp [aE, bE]))
  have hth : thE ζ a b ∈ hostF ζ a b :=
    (mem_hostF_iff_adjoin hqd h _).2 (subset_adjoin ℚ _ (by simp [thE]))
  let abF : hostF ζ a b := ⟨_, hab⟩
  let thF : hostF ζ a b := ⟨_, hth⟩
  let M₁ : IntermediateField ℚ (hostF ζ a b) := adjoin ℚ {abF}
  let M₂ : IntermediateField ℚ (hostF ζ a b) := adjoin ℚ {thF}
  let x₁ : M₁ := ⟨abF, mem_adjoin_simple_self _ _⟩
  have hx₁ : x₁ ^ 2 = (((q : ℤ) * d : ℤ) : M₁) := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    push_cast
    show (a * b) ^ 2 = _
    rw [mul_pow, h.2.1, h.2.2.1]
    ring
  have htop₁ : adjoin ℚ {x₁} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
  have hsf : Squarefree ((q : ℤ) * d) := by
    rw [show ((q : ℤ) * d) = ((q * d : ℕ) : ℤ) by push_cast; rfl, Int.squarefree_natCast,
      Nat.squarefree_mul_iff]
    exact ⟨(Nat.coprime_primes hqp hdp).2 hne, hqp.squarefree, hdp.squarefree⟩
  have hmod : ((q : ℤ) * d) % 4 = 1 := by
    have hq4 : (q : ℤ) % 4 = 3 := by omega
    have hd4 : (d : ℤ) % 4 = 3 := by omega
    rw [Int.mul_emod, hq4, hd4]
    norm_num
  have hd₁ : discr M₁ = (q : ℤ) * d := Formalism.HF.Final.quadDiscr M₁ _ x₁ hx₁ htop₁ hsf hmod
  have hGal₁ : IsGalois ℚ M₁ := (Formalism.Q3.mqGalois 1 M₁ (fun _ => (q : ℤ) * d) (fun _ => x₁)
    ⟨fun _ => hx₁, by rw [Set.range_const]; exact htop₁⟩
    (fun _ => mul_ne_zero (Nat.cast_ne_zero.2 hqp.ne_zero) (Nat.cast_ne_zero.2 hdp.ne_zero))).1
  have hmap : M₂.map ι = F1 ζ := by
    rw [adjoin_map, Set.image_singleton]
    rfl
  let f₂ := (M₂.equivMap ι).trans (equivOfEq hmap)
  have hd₂ : discr M₂ = 2 ^ (2 ^ e * (e + 1) - 1) := by
    rw [discr_eq_discr_of_algEquiv _ f₂.toRingEquiv.toRatAlgEquiv, h1 e L ζ h.1]
  have hf₂ : Module.finrank ℚ M₂ = 2 ^ e := by
    rw [f₂.toLinearEquiv.finrank_eq]
    exact RealCyclotomicSubfield.finrank_real_subfield h.1
  have hcop : IsCoprime (discr M₁) (discr M₂) := by
    rw [hd₁, hd₂]
    apply isCoprime_odd_two_pow
    exact (odd_of_mod (by omega)).mul (odd_of_mod (by omega))
  have hld := linearDisjoint_of_isGalois_isCoprime_discr (hostF ζ a b) M₁ M₂ hcop
  have hsup : M₁ ⊔ M₂ = ⊤ := by
    rw [← adjoin_union]
    refine adjoin_eq_top_of_map ι _ ℚ⟮a * b, ζ + ζ⁻¹⟯ ?_
      (fun x => (mem_hostF_iff_adjoin hqd h (x : hostE ζ a b)).1 x.2)
    congr 1
    ext x
    simp [ι, abF, thF, aE, bE, thE]
    tauto
  have hf₁ : Module.finrank ℚ M₁ = 2 := by
    have := hld.finrank_sup
    rw [hsup, finrank_top', finrank_hostF hqd h, hf₂] at this
    have h2 : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
    rw [h2] at this
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm
  have hnat := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (hostF ζ a b) M₁ M₂ hld hsup
    (isCoprime_differentIdeal_of_isCoprime_discr (hostF ζ a b) hcop)
  have hs : (discr (hostF ζ a b)).sign = 1 := by
    rw [sign_discr, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero]
  rw [← Int.sign_mul_natAbs (discr (hostF ζ a b)), hs, hnat, hd₁, hd₂, hf₁, hf₂, one_mul]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  push_cast
  rw [← pow_mul, exp_F]
  ring
end Formalism.FrobeniusOrbits.DiscrB
