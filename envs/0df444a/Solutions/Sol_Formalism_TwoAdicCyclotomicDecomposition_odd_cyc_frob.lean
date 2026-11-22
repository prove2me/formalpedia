-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_cyc_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:32.480357+00:00
-- url     : https://prove2.me/submissions/fe1bb22f-2217-42c4-8c6f-c220ee8c7fb0

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card_under
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_natCast_not_mem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_two_pow_not_dvd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_autToPow_smul

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
theorem _root_.solution {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(L/ℚ))
    (H : IsArithFrobAt ℤ σ P) :
    ((hζ.autToPow ℚ σ : ZMod (2 ^ n))) = (p : ZMod (2 ^ n)) := by
  have hZ : IsPrimitiveRoot hζ.toInteger (2 ^ n) := hζ.toInteger_isPrimitiveRoot
  have hm : ((2 ^ n : ℕ) : 𝓞 L) ∉ P :=
    odd_natCast_not_mem p P _ (odd_two_pow_not_dvd p n Fact.out hp2)
  have h₁ := AlgHom.IsArithFrobAt.apply_of_pow_eq_one H hZ.pow_eq_one hm
  rw [odd_card_under p P] at h₁
  have h₃ : hζ.toInteger ^ ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val = hζ.toInteger ^ p := by
    rw [← odd_autToPow_smul hζ σ]; exact h₁
  rw [(hZ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hZ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val] at h₃
  exact h₃
end Formalism.TwoAdicCyclotomicDecomposition
