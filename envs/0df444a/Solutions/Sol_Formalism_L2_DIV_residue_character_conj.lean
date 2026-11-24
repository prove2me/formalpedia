-- Prove2me | solution 1 for Formalism.L2.DIV.residue_character_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:05.943809+00:00
-- url     : https://prove2.me/submissions/7ac9b240-a84b-4660-b42d-1cc51a5b6c4b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_one_sub_eps_mem
import Theorems.Thm_P2M_Formalism_L2_DIV_tpOff_proof__b4afce82c913
import Theorems.Thm_Formalism_L2_DIV_b_mkU
import Theorems.Thm_Formalism_L2_DIV_b_mkU_supp
import Theorems.Thm_P2M_Formalism_L2_DIV_tpExU_proof__f73447c0298f
import Theorems.Thm_Formalism_L2_DIV_b_resChar_spec
import Theorems.Thm_Formalism_L2_DIV_b_other_of_split
import Theorems.Thm_Formalism_L2_DIV_b_mkU_idF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution : ResCharConj := by
  intro F E _ _ _ _ _ L _ ξ hξ hF v P P' hne hsplit n a a' ha ha'
  obtain ⟨hPv, hP'v⟩ := b_under_of_split v P P' hsplit
  have hn : n ∉ v.asIdeal := by
    intro h
    rw [← hPv] at h
    have h0 : (a : 𝓞 E ⧸ P.asIdeal) = 0 := by
      rw [ha, Ideal.Quotient.eq_zero_iff_mem]; exact h
    have : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
    exact a.ne_zero h0
  obtain ⟨u, hu⟩ := b_mkU (E := E) v (algebraMap (𝓞 F) (𝓞 E) n) 1 n hn (mul_one _)
  have husupp := b_mkU_supp v _ u hu
  have hun : ∀ Q : HeightOneSpectrum (𝓞 E), Q.asIdeal.under (𝓞 F) = v.asIdeal →
      (u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) ∈ Q.asIdeal.map (toRInt F E) := by
    intro Q hQ
    have : (u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) =
        (1 - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) * (1 - bEps E v) := by rw [hu]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (b_one_sub_eps_mem v Q hQ)
  obtain ⟨u1, b1, hb1, hu1, hu1P, hu1P'⟩ := tpExU_proof' P v hPv a
  have h1 := b_resChar_spec ξ hξ P v hPv u1 a b1 hb1 hu1 hu1P hu1P'
  have h2 := b_resChar_spec ξ hξ P' v hP'v (u * u1⁻¹) a' (algebraMap (𝓞 F) (𝓞 E) n) ha'.symm
    (by rw [map_mul, map_inv]; exact mul_mem husupp (inv_mem hu1))
    (by
      have : ((u * u1⁻¹ : (RInt F E)ˣ) : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) =
          (((u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) -
            toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) * ((u1 : RInt F E) - 1)) * ((u1⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        have e : (u1 : RInt F E) * ((u1⁻¹ : (RInt F E)ˣ) : RInt F E) = 1 := Units.mul_inv u1
        rw [Units.val_mul]
        linear_combination (toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) * e
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.sub_mem _ (hun P' hP'v) (Ideal.mul_mem_left _ _ (hu1P' P' hne.symm))))
    (by
      intro Q hQ
      have : ((u * u1⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 =
          ((u : RInt F E) - u1) * ((u1⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.mul_inv, Units.val_mul]
      rw [this]
      apply Ideal.mul_mem_right
      by_cases hQP : Q = P
      · subst hQP
        have hbb : algebraMap (𝓞 F) (𝓞 E) n - b1 ∈ Q.asIdeal := by
          rw [← Ideal.Quotient.eq, hb1, ha]
        have : (u : RInt F E) - u1 = ((u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n)) -
            ((u1 : RInt F E) - toRInt F E b1) + toRInt F E (algebraMap (𝓞 F) (𝓞 E) n - b1) := by
          rw [map_sub]; ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.sub_mem _ (hun Q hPv) hu1P) (Ideal.mem_map_of_mem _ hbb)
      · have hoff := b_other_of_split v P P' Q hsplit hQP hQ
        have : (u : RInt F E) - u1 = ((u : RInt F E) - 1) - ((u1 : RInt F E) - 1) := by ring
        rw [this]
        exact Ideal.sub_mem _ (tpOff_proof' v Q hoff u husupp) (tpOff_proof' v Q hoff u1 hu1))
  rw [← h1, ← h2, ← map_mul, ← map_mul, mul_comm, inv_mul_cancel_right]
  exact hF (b_mkU_idF v n hn u hu)
end Formalism.L2.DIV
