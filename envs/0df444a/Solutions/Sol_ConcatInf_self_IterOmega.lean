-- Prove2me | solution 1 for ConcatInf_self_IterOmega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:17.240842+00:00
-- url     : https://prove2.me/submissions/6ddee7df-d6ff-4f91-93e1-9e8f2f23bcbc

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
import Theorems.Thm_mem_ConcatInf_IterOmega
import Theorems.Thm_P2M_Stream__append_extract_drop_29d8f2c46a9f
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e


set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (List A)} :
    L * L^ω = L^ω := by
  ext as ; constructor
  · intro h
    obtain ⟨φ, h_mono, h_init, h_rest⟩ := mem_ConcatInf_IterOmega h
    rcases (show φ 0 = 0 ∨ φ 0 > 0 by omega) with h_φ | h_φ
    · use φ
    use (fun k ↦ if k = 0 then 0 else φ (k - 1)) ; simp ; constructor
    · apply strictMono_nat_of_lt_succ ; intro n
      rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n, h_φ]
      exact h_mono (show n - 1 < n by omega)
    · intro n
      rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n, h_init]
      specialize h_rest (n - 1) ; simp_all [(show n - 1 + 1 = n by omega)]
  · rintro ⟨φ, h_mono, h_init, h_rest⟩
    use (as.extract (φ 0) (φ 1)), (as.drop (φ 1))
    simp [h_rest] ; constructor
    · use (fun k ↦ φ (k + 1) - φ 1) ; constructor
      · intro m n h_mn ; simp
        have := h_mono (show m + 1 < n + 1 by omega)
        have := StrictMono.monotone h_mono (show 1 ≤ m + 1 by omega)
        omega
      · simp ; intro n
        have h1 := StrictMono.monotone h_mono (show 1 ≤ n + 1 by omega)
        have h2 := StrictMono.monotone h_mono (show 1 ≤ n + 1 + 1 by omega)
        simp [extract_drop, h_rest, (show φ 1 + (φ (n + 1) - φ 1) = φ (n + 1) by omega),
          (show φ 1 + (φ (n + 1 + 1) - φ 1) = φ (n + 1 + 1) by omega)]
    · ext k
      simp [h_init, append_extract_drop]
