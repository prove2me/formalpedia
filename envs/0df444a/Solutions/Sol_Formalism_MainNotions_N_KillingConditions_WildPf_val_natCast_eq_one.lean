-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.val_natCast_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:50.035486+00:00
-- url     : https://prove2.me/submissions/e543fa81-bae6-449f-8617-1eef061b992a

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_val_intCast_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable {A}
namespace Formalism.MainNotions.N.KillingConditions.WildPf
theorem _root_.solution {p m : ℕ} (hpA : A.valuation ((p : ℕ) : Ω) < 1) (hm : Nat.Coprime m p) :
    A.valuation ((m : ℕ) : Ω) = 1 := by
  have hle : A.valuation ((m : ℕ) : Ω) ≤ 1 := by
    exact (A.valuation_le_one_iff _).2 (natCast_mem A m)
  by_contra hne
  have hlt : A.valuation ((m : ℕ) : Ω) < 1 := lt_of_le_of_ne hle hne
  have hb : ((m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab m p
    rw [hm.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hb' : ((m : ℕ) : Ω) * ((Nat.gcdA m p : ℤ) : Ω) + ((p : ℕ) : Ω) * ((Nat.gcdB m p : ℤ) : Ω) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hb
  have h1 : A.valuation (1 : Ω) < 1 := by
    rw [← hb']
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le _)) hlt
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le _)) hpA
  rw [map_one] at h1
  exact lt_irrefl _ h1
end Formalism.MainNotions.N.KillingConditions.WildPf
