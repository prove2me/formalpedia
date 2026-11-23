-- Prove2me | solution 1 for Formalism.HC.Der.Rd.mem_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:17.153138+00:00
-- url     : https://prove2.me/submissions/d7f64bf2-cea7-4fb2-91eb-7e6f4d797c2f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
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
private theorem coe_unitsMap_eq_natCast_val_of_dvd {d : ℕ} (hd : d ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap hd u : (ZMod d)ˣ) : ZMod d) = (((u : ZMod N).val : ℕ) : ZMod d) := by
  rw [← ZMod.cast_eq_val]
  first
  | rfl
  | exact ZMod.unitsMap_val hd u
  | simp [ZMod.unitsMap_def]
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution {f : ℕ} (hf : f ∣ N) (u : (ZMod N)ˣ) :
    u ∈ (ZMod.unitsMap hf).ker ↔ (u : ZMod N).val ≡ 1 [MOD f] := by
  rw [MonoidHom.mem_ker, Units.ext_iff, coe_unitsMap_eq_natCast_val_of_dvd, Units.val_one, ← Nat.cast_one (R := ZMod f),
    ZMod.natCast_eq_natCast_iff]
end Formalism.HC.Der.Rd
