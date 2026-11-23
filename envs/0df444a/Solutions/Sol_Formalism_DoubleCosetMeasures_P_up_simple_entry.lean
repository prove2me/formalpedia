-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.up_simple_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:29.625791+00:00
-- url     : https://prove2.me/submissions/c8e617eb-552d-495f-b41d-3a4250d21656

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) (hy : IsUpUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) j ⟨j.val + 1, h⟩ = x j ⟨j.val + 1, h⟩ + y j ⟨j.val + 1, h⟩ := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hx.2 j, hy.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : x j k = 0 := hx.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : y k ⟨j.val + 1, h⟩ = 0 := hy.1 (by simpa using hlt)
      simp [this]
end Formalism.DoubleCosetMeasures.P
