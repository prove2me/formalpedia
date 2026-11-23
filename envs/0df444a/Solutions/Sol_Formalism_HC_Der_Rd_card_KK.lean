-- Prove2me | solution 1 for Formalism.HC.Der.Rd.card_KK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:31.754223+00:00
-- url     : https://prove2.me/submissions/545077fe-4ec0-44f5-b807-e07957897efd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_mem_ker_iff
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
private theorem ne_zero_of_dvd_of_neZero {f : ℕ} (hf : f ∣ N) : f ≠ 0 := by
  rintro rfl
  exact NeZero.ne N (zero_dvd_iff.mp hf)
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution {f : ℕ} (hf : f ∣ N) : (KK N f).card * f.totient = N.totient := by
  classical
  haveI : NeZero f := ⟨ne_zero_of_dvd_of_neZero hf⟩
  have h1 : (KK N f).card = Nat.card (ZMod.unitsMap hf).ker := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_of_subtype (p := fun u => u ∈ (ZMod.unitsMap hf).ker) _
      fun u => by rw [mem_KK, mem_ker_iff hf]).symm
  have h2 : (ZMod.unitsMap hf).ker.index = Nat.card (ZMod f)ˣ := by
    first
    | exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective hf)).toEquiv
    | rw [Subgroup.index_ker, Set.range_eq_univ.mpr (ZMod.unitsMap_surjective hf), Nat.card_univ]
  rw [h1, ← ZMod.card_units_eq_totient f, ← Nat.card_eq_fintype_card, ← h2, Subgroup.card_mul_index,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
end Formalism.HC.Der.Rd
