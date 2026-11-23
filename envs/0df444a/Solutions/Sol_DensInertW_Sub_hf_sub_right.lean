-- Prove2me | solution 1 for DensInertW.Sub.hf_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:15.403966+00:00
-- url     : https://prove2.me/submissions/2c805ffb-0d48-4491-8bda-6ddf2f04ebd0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW.Sub
theorem _root_.solution (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (x y y' : Fin n → L) : hf q M x (y - y') = hf q M x y - hf q M x y' := by
  have hs : ∀ a b : L, (a - b) ^ q = a ^ q - b ^ q := fun a b => by
    have h := hadd (a - b) b
    rw [sub_add_cancel] at h
    rw [h]
    ring
  simp only [hf, Pi.sub_apply, hs, mul_sub, Finset.sum_sub_distrib]
end DensInertW.Sub
