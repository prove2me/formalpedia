-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerFrob_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:33.492239+00:00
-- url     : https://prove2.me/submissions/dcd19bbb-4a03-4c4b-84cc-664bcf1c8e24

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_frob_sgn
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_cyc_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (hG : LayerGalois) : LayerFrob := by
  intro n q d hn hqd L _ _ ζ a b h p _ hp2 hpq hpd P _ _
  obtain ⟨hGal, -, -, hbij⟩ := hG n q d hn hqd L ζ a b h
  have : IsGalois ℚ L := hGal
  have hp : p.Prime := Fact.out
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have hnq : ¬ (p : ℤ) ∣ -(q : ℤ) := by
    rw [dvd_neg]; intro hd'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hqd.1).mp (by exact_mod_cast hd'))
  have hnd : ¬ (p : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg]; intro hd'
    exact hpd ((Nat.prime_dvd_prime_iff_eq hp hqd.2.1).mp (by exact_mod_cast hd'))
  have hval : ∀ σ : Gal(L/ℚ), IsArithFrobAt ℤ σ P →
      (((galMap h.1 a b σ).1 : ZMod (2 ^ n)) = (p : ZMod (2 ^ n)) ∧
        (((galMap h.1 a b σ).2.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galMap h.1 a b σ).2.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p) := fun σ H =>
    ⟨odd_cyc_frob h.1 p hp2 P σ H, odd_frob_sgn p hp2 P σ H a _ ha hnq,
      odd_frob_sgn p hp2 P σ H b _ hb hnd⟩
  have : Finite (𝓞 L ⧸ P) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) P
  refine ⟨⟨τ, hτ⟩, fun σ => ⟨hval σ, fun hσ => ?_⟩⟩
  have hτv := hval τ hτ
  have : σ = τ := hbij.1 (Prod.ext (Units.ext (hσ.1.trans hτv.1.symm))
    (Prod.ext (Units.ext (hσ.2.1.trans hτv.2.1.symm)) (Units.ext (hσ.2.2.trans hτv.2.2.symm))))
  subst this
  exact hτ
end Formalism.TwoAdicCyclotomicDecomposition
