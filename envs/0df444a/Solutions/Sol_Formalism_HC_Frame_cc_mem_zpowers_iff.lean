-- Prove2me | solution 1 for Formalism.HC.Frame.cc_mem_zpowers_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:12.372216+00:00
-- url     : https://prove2.me/submissions/850c21f4-969e-49e1-b6db-43373c423241

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'
private theorem sign_group_sq_eq_one_var (x : G0) : x ^ 2 = 1 :=
  Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)
private theorem G0_pow_eq_ite_even (x : G0) (i : ℕ) : x ^ i = if Even i then 1 else x := by
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [if_pos ⟨k, rfl⟩, ← two_mul, pow_mul, sign_group_sq_eq_one_var, one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.2 ⟨k, rfl⟩), pow_succ, pow_mul, sign_group_sq_eq_one_var, one_pow, one_mul]
private theorem G0_zpow_eq_ite_even (x : G0) (k : ℤ) : x ^ k = if Even k then 1 else x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, sign_group_sq_eq_one_var]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_pos ⟨m, rfl⟩, ← two_mul, zpow_mul, h2, one_zpow]
  · rw [if_neg (Int.not_even_iff_odd.2 ⟨m, rfl⟩), zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (g : φ.GG) : φ.cc ∈ Subgroup.zpowers g ↔ g.1 = c0 ∧ Odd (orderOf g.2) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 : g.1 ^ k = c0 := congrArg Prod.fst hk
    have h2 : g.2 ^ k = 1 := congrArg Prod.snd hk
    rw [G0_zpow_eq_ite_even] at h1
    split_ifs at h1 with hk2
    · exact (int_units_neg_one_ne_one (congrArg Prod.fst h1).symm).elim
    · refine ⟨h1, ?_⟩
      have hd := orderOf_dvd_iff_zpow_eq_one.2 h2
      rcases Nat.even_or_odd (orderOf g.2) with he | ho
      · have h2d : (2 : ℤ) ∣ (orderOf g.2 : ℤ) := by exact_mod_cast even_iff_two_dvd.1 he
        exact absurd (even_iff_two_dvd.2 (dvd_trans h2d hd)) hk2
      · exact ho
  · rintro ⟨hc, ho⟩
    refine Subgroup.mem_zpowers_iff.2 ⟨(orderOf g.2 : ℤ), ?_⟩
    rw [zpow_natCast]
    refine Prod.ext ?_ ?_
    · show g.1 ^ orderOf g.2 = c0
      rw [hc, G0_pow_eq_ite_even, if_neg (Nat.not_even_iff_odd.2 ho)]
    · show g.2 ^ orderOf g.2 = 1
      exact pow_orderOf_eq_one g.2
end Formalism.HC.Frame
