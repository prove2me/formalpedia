-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.mirabolic_is_mackey
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:27.546935+00:00
-- url     : https://prove2.me/submissions/877c722a-806f-4470-8fa8-b591f919d610

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_mirabolic_mackey_pair
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_one
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_mul
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_isMirab_of_isUniU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : MirabolicIsMackey := by
  intro k A _ _ _ n ψ hψ P U hP hU
  refine ⟨?_, ?_, ?_⟩
  · show ψ (supd ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = 1
    rw [Units.val_one, supd_one, AddChar.map_zero_eq_one]
  · intro u hu u' hu'
    show ψ (supd (((u * u' : P) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      ψ (supd ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) *
        ψ (supd ((u' : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
    rw [Subgroup.coe_mul, Units.val_mul, supd_mul _ _ ((hU u).1 hu) ((hU u').1 hu'),
      AddChar.map_add_eq_mul]
  · intro h hh
    have hm : IsMirab ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := (hP h).1 h.2
    have hnu : ¬ IsUniU ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      fun hu => hh ((hU h).2 hu)
    obtain ⟨u, hu1, hu2, hne⟩ := mirabolic_mackey_pair k A n ψ hψ (h : GL (Fin (n + 1)) k) hm hnu
    have huP : u ∈ P := (hP u).2 (isMirab_of_isUniU _ hu1)
    refine ⟨⟨u, huP⟩, (hU _).2 hu1, (hU _).2 ?_, ?_⟩
    · simpa using hu2
    · simpa using hne
end Formalism.EigenvalueLevelCeiling
