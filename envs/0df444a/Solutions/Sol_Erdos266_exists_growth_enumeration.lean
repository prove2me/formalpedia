-- Prove2me | solution 1 for Erdos266.exists_growth_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:24.926936+00:00
-- url     : https://prove2.me/submissions/0181f291-9d51-483c-9c56-673f9b527232

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
public import Theorems.Thm_Erdos266_abs_tSeq_le
public import Theorems.Thm_Erdos266_tSeq_bijective

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution :
    ∃ t : ℕ → ℚ, Function.Bijective t ∧ ∀ j : ℕ, |t j| ≤ (j : ℚ) + 1 :=
  ⟨tSeq, tSeq_bijective, abs_tSeq_le⟩
end Erdos266
