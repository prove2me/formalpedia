-- Prove2me | solution 1 for Formalism.REAL.CharId_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:45.473291+00:00
-- url     : https://prove2.me/submissions/4558839a-4a6d-4561-8ae1-8707ad641945

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_M_apply
import Theorems.Thm_Formalism_REAL_CharId_T_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (c d : Fin n) :
    twistedAction E c d * CharId_M E = CharId_M E * twistedAction E c d := by
  apply LinearMap.ext
  intro y
  funext x
  simp only [Module.End.mul_apply, CharId_T_apply, CharId_M_apply, map_sum, map_sub]
  have key : ∀ b, E c d (E x b (y b)) = E x b (E c d (y b)) +
      ((if d = x then E c b (y b) else 0) - (if b = c then E x d (y b) else 0)) := by
    intro b
    have h := LinearMap.congr_fun (hE c d x b) (y b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_iff_eq_add', h]
    split_ifs <;> simp
  have hb : ∀ b, E x b (if b = d then y c else 0) = if b = d then E x b (y c) else 0 := by
    intro b
    split_ifs <;> simp
  simp only [key, hb, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hxd : x = d
  · subst hxd
    simp
    abel
  · simp [hxd, Ne.symm hxd]
    abel
end Formalism.REAL
