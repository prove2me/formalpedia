-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.split_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:28:33.441709+00:00
-- url     : https://prove2.me/submissions/24d916e0-0c68-44b6-a0a3-d82fed8de897

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfA
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_image_places_primesOver
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_ram_inertia_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E) :
    {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 F)
  have hone : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    rintro ⟨q, hq, hql⟩
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
        rw [hql.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 F))
      exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
    have hqmem : ((p : ℕ) : 𝓞 F) ∈ q := by
      have : (p : ℤ) ∈ q.under ℤ := by rw [← hql.over]; exact Ideal.mem_span_singleton_self _
      simpa using this
    obtain ⟨h1, h2⟩ := ram_inertia_sub (E := E) p hp hs ⟨q, hq, hq0⟩ hqmem
    change q.ramificationIdx ℤ * q.inertiaDeg ℤ = 1
    rw [h1, h2]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [RingOfIntegers.rank] at hsum
  rw [← hsum, ← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h),
    image_places_primesOver p hp, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
end Formalism.L2.SG.Pf.SatGramLoc
