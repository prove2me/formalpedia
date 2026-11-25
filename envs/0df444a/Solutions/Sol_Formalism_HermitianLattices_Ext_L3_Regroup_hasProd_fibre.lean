-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Regroup.hasProd_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:58.516035+00:00
-- url     : https://prove2.me/submissions/6d64a035-81da-43b0-9700-f6719b23ad37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap_eq_comap_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_comap_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_comap_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_comap_eq_comap_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_isMaximal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_etaF_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_eulerFac_inv_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_eulerFac_mul_conj_inv_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.Regroup
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.Regroup
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 1 ≤ M)
    (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    HasProd (fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1)
      (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
  classical
  obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
  have hmem : ∀ c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭},
      c.1.1 = P ∨ c.1.1 = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    intro c
    have h1 : c.1.1.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := congrArg Subtype.val c.2
    exact (comap_eq_comap_iff hK hF hP c.1.2).1 (hP𝔭.trans h1.symm)
  have heta := etaF_comap hK hF hP
  rw [hP𝔭] at heta
  let c0 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} := ⟨⟨P, hP⟩, Subtype.ext hP𝔭⟩
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have hN := absNorm_comap_inert hK hF hP hc
    rw [hP𝔭] at hN
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P), eulerFac_inv_inert hK hP hc, heta, if_pos hc, ← hN]
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_singleton]
        apply Subtype.ext
        apply Subtype.ext
        rcases hmem b with h | h
        · exact h
        · exact h.trans hc)
    rw [Finset.prod_singleton] at h
    rw [← hval]
    exact h
  · have hN := absNorm_comap_split hK hF hP hc
    rw [hP𝔭] at hN
    have hPb := conjIdeal_isMaximal hK hP
    have hPb𝔭 : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := by
      rw [← hP𝔭]
      exact ((comap_eq_comap_iff hK hF hP hPb).2 (Or.inr rfl)).symm
    let c1 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} :=
      ⟨⟨Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, hPb⟩, Subtype.ext hPb𝔭⟩
    have hne : c0 ≠ c1 := by
      intro h
      exact hc (congrArg (fun c => c.1.1) h).symm
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P * _), eulerFac_mul_conj_inv_split hK hP hc M hM, heta,
        if_neg hc, hN, one_pow, one_mul]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0, c1})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hmem b with h | h
        · exact Or.inl (Subtype.ext (Subtype.ext h))
        · exact Or.inr (Subtype.ext (Subtype.ext h)))
    rw [Finset.prod_pair hne] at h
    rw [← hval]
    exact h
end Formalism.HermitianLattices.Ext.L3.Regroup
