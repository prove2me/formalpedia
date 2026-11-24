-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.ram_inertia_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:38.058665+00:00
-- url     : https://prove2.me/submissions/bc3ec7bb-1b16-4e0b-a1e0-cabfe12f5485

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfA
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_liesOver_natCast
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_ram_inertia_split

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
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hvp := v.isPrime
  have hvl : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_natCast p hp v hv
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
  have hPZ : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
      rw [hPZ.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))
    exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
  have hPmem : ((p : ℕ) : 𝓞 E) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [← hPZ.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  obtain ⟨he, hf⟩ := ram_inertia_split (K := E) p hp hs ⟨P, hPp, hP0⟩ hPmem
  change P.ramificationIdx ℤ = 1 at he
  change P.inertiaDeg ℤ = 1 at hf
  rw [Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P] at he
  rw [Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P] at hf
  exact ⟨Nat.eq_one_of_mul_eq_one_right he, Nat.eq_one_of_mul_eq_one_right hf⟩
end Formalism.L2.SG.Pf.SatGramLoc
