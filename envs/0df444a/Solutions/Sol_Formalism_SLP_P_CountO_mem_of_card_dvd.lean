-- Prove2me | solution 1 for Formalism.SLP.P.CountO.mem_of_card_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:29.32832+00:00
-- url     : https://prove2.me/submissions/a8ce88e0-818f-4c8a-b9c8-871a4b4ee227

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
open NumberField
variable (E : Type) [Field E] [NumberField E]
variable {E}
namespace Formalism.SLP.P.CountO
theorem _root_.solution {P : Ideal (𝓞 E)} [P.IsMaximal] {p e : ℕ}
    (h : Nat.card (𝓞 E ⧸ P) ∣ p ^ e) : ((p : ℕ) : 𝓞 E) ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  letI : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
  by_cases hfin : Finite (𝓞 E ⧸ P)
  · obtain ⟨ℓ, hℓ⟩ := CharP.exists (𝓞 E ⧸ P)
    haveI := hℓ
    haveI : Fintype (𝓞 E ⧸ P) := Fintype.ofFinite _
    obtain ⟨n, hℓp, hn⟩ := FiniteField.card (𝓞 E ⧸ P) ℓ
    have hdvd : ℓ ∣ Nat.card (𝓞 E ⧸ P) := by
      rw [Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self ℓ (PNat.ne_zero n)
    have h2 : ℓ ∣ p := hℓp.dvd_of_dvd_pow (dvd_trans hdvd h)
    exact (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) ℓ p).2 h2
  · haveI : Infinite (𝓞 E ⧸ P) := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite] at h
    have h0 : p ^ e = 0 := zero_dvd_iff.1 h
    have hp : p = 0 := by
      rcases Nat.eq_zero_or_pos e with he | he
      · simp [he] at h0
      · exact (pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 he)).1 h0
    simp [hp]
end Formalism.SLP.P.CountO
