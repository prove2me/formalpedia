-- Prove2me | solution 1 for Formalism.HC.Der.inertia_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:20.309799+00:00
-- url     : https://prove2.me/submissions/7be0cbbb-12d9-4b2c-81ad-fd38e798d128

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_ordCompl_d
import Theorems.Thm_Formalism_HC_Der_val_one_modEq
import Theorems.Thm_Formalism_HC_Der_exists_art_iod
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_HC_D7_ordCompl_d
import Theorems.Thm_Formalism_HC_Der_cyc_isGalois
import Theorems.Thm_Formalism_HC_Der_exists_over
import Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff
import Theorems.Thm_Formalism_HC_Der_tauN_inertia_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = φ.iod) := by
  intro P _ _ σ
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, hI, -⟩ := exists_over (emb H) H.d P
  constructor
  · intro h
    obtain ⟨τ, hτ1, hτ2⟩ := (hI σ).mp h
    obtain ⟨w, rfl⟩ := (tauN H.condN).surjective τ
    have h1 := (tauN_inertia_iff H.condN H.d Q w).mp hτ2
    rw [ordCompl_d H] at h1
    have hg : H.gal σ = H.art w := (gal_eq_art_iff H σ w).mpr hτ1
    rw [hg]
    exact H.art_d w h1
  · intro h
    have key : ∀ w : (ZMod H.condN)ˣ, (w : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] →
        H.gal σ = H.art w → ∀ x : 𝓞 H.E, σ • x - x ∈ P := by
      intro w hw1 hg
      apply (hI σ).mpr
      refine ⟨tauN H.condN w, (gal_eq_art_iff H σ w).mp hg, ?_⟩
      apply (tauN_inertia_iff H.condN H.d Q w).mpr
      rw [ordCompl_d H]
      exact hw1
    rcases h with h | h
    · exact key 1 (val_one_modEq _ _ (QSq_dvd H)) (h.trans (map_one _).symm)
    · obtain ⟨u, hu1, hu2⟩ := exists_art_iod H
      exact key u hu1 (h.trans hu2.symm)
end Formalism.HC.Der
