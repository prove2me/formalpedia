-- Prove2me | solution 1 for Formalism.MainNotions.J.splits_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:34.086603+00:00
-- url     : https://prove2.me/submissions/49166b17-2a93-445b-8581-8423de0cf294

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_pI_ne_bot
import Theorems.Thm_Formalism_MainNotions_J_pI_max
import Theorems.Thm_Formalism_MainNotions_J_img_places
import Theorems.Thm_Formalism_MainNotions_J_ncard_places
import Theorems.Thm_Formalism_MainNotions_J_ef_one_of_card
import Theorems.Thm_Formalism_MainNotions_J_card_of_ef_one
import Theorems.Thm_Formalism_MainNotions_J_ef_one_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
variable (L : Type) [Field L] [NumberField L] [Algebra K L]
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime)
    (h : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L) :
    Nat.card {v : HeightOneSpectrum (𝓞 K) // ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} = Module.finrank ℚ K ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  haveI := pI_max p hp
  have hL : (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L)).card = Module.finrank ℚ L := by
    rw [← ncard_places L p hp]
    exact h
  have hefK := ef_one_sub K p L hp (ef_one_of_card L p hp hL)
  refine ⟨?_, ?_⟩
  · rw [← card_of_ef_one K p hp hefK, ← ncard_places K p hp]
    exact Nat.card_coe_set_eq _
  · intro v hv
    have hmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K) := by
      rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset (pI_ne_bot p hp), ← img_places K p hp]
      exact ⟨v, hv, rfl⟩
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hmem
    have hf1 : (span {(p : ℤ)}).inertiaDeg' v.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_left (hefK _ hmem)
    have hn := Ideal.absNorm_eq_pow_inertiaDeg' (R := 𝓞 K) (p := p) v.asIdeal hp
    rw [hf1, pow_one] at hn
    rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
end Formalism.MainNotions.J
