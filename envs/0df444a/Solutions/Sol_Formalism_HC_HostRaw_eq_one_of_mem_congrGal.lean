-- Prove2me | solution 1 for Formalism.HC.HostRaw.eq_one_of_mem_congrGal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:37.240966+00:00
-- url     : https://prove2.me/submissions/71896a84-c376-4af8-8c51-6c77807e605d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_HostRaw_art_eq_one_of_modEq
import Theorems.Thm_Formalism_HC_HostRaw_mem_congrGal_iff
import Theorems.Thm_P2M_RH_Formalism_HC_HostRaw_ordCompl_q_2735571a88a0a567
import Theorems.Thm_Formalism_HC_HostRaw_art_eq_one_of_jacobi
import Theorems.Thm_Formalism_HC_D7_ordCompl_d
import Theorems.Thm_Formalism_HC_D7_ordCompl_q
import Theorems.Thm_Formalism_HC_Der_ordCompl_d
import Theorems.Thm_Formalism_HC_HostRaw_not_dvd_condN_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution (hps : H.PsQ) {l : ℕ} (hl : l.Prime) (hlS : ¬ l ∣ H.QS) (σ : H.E ≃ₐ[ℚ] H.E)
    (hσ : σ ∈ H.congrGal (ordCompl[l] H.condN)) (h1 : (H.gal σ).1.1 = 1) (h2 : (H.gal σ).1.2 = 1) : σ = 1 := by
  obtain ⟨u, hu, hg⟩ := (H.mem_congrGal_iff (Nat.ordCompl_dvd _ _) σ).1 hσ
  rw [← H.gal.map_eq_one_iff, hg]
  rw [hg] at h1 h2
  by_cases hq : l = H.q
  · rw [hq, H.ordCompl_q] at hu
    refine H.art_eq_one_of_jacobi u hu ?_
    rw [← hps u, h1, Units.val_one]
  by_cases hd : l = H.d
  · rw [hd, ordCompl_d] at hu
    refine (H.art_d u hu).resolve_right fun h => ?_
    rw [h] at h2
    exact absurd h2 (by show ¬ (-1 : ℤˣ) = 1; decide)
  · have hN : ¬ l ∣ H.condN := (H.not_dvd_condN_iff hl).2 ⟨hlS, hq, hd⟩
    rw [Nat.factorization_eq_zero_of_not_dvd hN, pow_zero, Nat.div_one] at hu
    exact H.art_eq_one_of_modEq u hu
end Formalism.HC.HostRaw
