-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot.extP_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:41.453983+00:00
-- url     : https://prove2.me/submissions/43bda6c9-327c-4e5d-a90a-d491bc094bfe

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_absNorm_extP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_comap_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_conjIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_isMaximal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap___comap_ebbf3c779431


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hP' := conjIdeal_isMaximal hK hP
  have h1 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P := Ideal.map_comap_le
  have h2 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    have : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) =
        P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [conjIdeal_eq_comap]
      exact SplitPrimeIdeals.comap_ι_comap (conjO_eq_iff_mem_range hF) P
    rw [← this]
    exact Ideal.map_comap_le
  have hcop : IsCoprime P (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) :=
    (Ideal.isCoprime_iff_sup_eq).2 (hP.coprime_of_ne hP' (Ne.symm hc))
  have h3 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf h1 h2
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 h3
  have hN := absNorm_extP hK hF (P.comap (algebraMap (𝓞 F) (𝓞 K)))
  rw [hC, map_mul, map_mul, absNorm_conjIdeal hK, absNorm_comap_split hK hF hP hc, sq] at hN
  have hpos : 0 < Ideal.absNorm P * Ideal.absNorm P := by
    have : 0 < Ideal.absNorm P := by
      have := IdealNormInequalities.one_lt_absNorm hP
      exact_mod_cast zero_lt_one.trans this
    positivity
  have hC1 : Ideal.absNorm C = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [hN, mul_one])
  rw [hC, Ideal.absNorm_eq_one_iff.1 hC1, Ideal.mul_top]
end Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
