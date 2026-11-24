-- Prove2me | solution 1 for Formalism.REAL.isWeightVector_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:51.620944+00:00
-- url     : https://prove2.me/submissions/cbc76969-962d-4ea8-84e9-44bb04ca8af5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (hrel : KRel ε F) {ν : Fin n → ℝ} {v : V}
    (hv : IsWeight F ν v) (a b : Fin n) (hab : ε a = ε b) :
    IsWeight F (ν + root a b) (F a b v) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T v) (hrel c c a b rfl hab)
  have e1 : (if c = a then F c b else 0) v = (if c = a then (1 : ℂ) else 0) • F a b v := by
    split_ifs with h1
    · subst h1
      simp
    · simp
  have e2 : (if b = c then F a c else 0) v = (if c = b then (1 : ℂ) else 0) • F a b v := by
    by_cases h2 : c = b
    · subst h2
      simp
    · simp [h2, Ne.symm h2]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul, e1, e2] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← sub_smul, ← add_smul]
  congr 1
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> ring
end Formalism.REAL
