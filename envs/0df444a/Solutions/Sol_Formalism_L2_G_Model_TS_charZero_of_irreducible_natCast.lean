-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.charZero_of_irreducible_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:13.914327+00:00
-- url     : https://prove2.me/submissions/39920ca7-d71e-4f62-87bf-8fa778190e60

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FormSK
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FormSK
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST
namespace Formalism.L2.G.Model.TS
theorem _root_.solution {W : Type*} [CommRing W] [IsDomain W] {p : ℕ} (hp : p.Prime)
    (h : Irreducible (p : W)) : CharZero W := by
  rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
  · exfalso
    haveI : CharP W (ringChar W) := ringChar.charP W
    haveI : Fact (ringChar W).Prime := ⟨hq⟩
    by_cases hpq : p = ringChar W
    · exact h.ne_zero (by rw [hpq]; exact CharP.cast_eq_zero W _)
    · apply h.not_isUnit
      have hu : IsUnit (p : ZMod (ringChar W)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (Nat.coprime_primes hp hq).mpr hpq
      have hu' := hu.map (ZMod.castHom (dvd_refl _) W)
      simpa using hu'
  · haveI : CharP W 0 := by
      rw [← hq]
      exact ringChar.charP W
    exact CharP.charP_to_charZero W
end Formalism.L2.G.Model.TS
