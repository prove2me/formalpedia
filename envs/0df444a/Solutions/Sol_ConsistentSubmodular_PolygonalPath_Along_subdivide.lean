-- Prove2me | solution 1 for ConsistentSubmodular.PolygonalPath.Along.subdivide
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:43.035738+00:00
-- url     : https://prove2.me/submissions/6bc91f71-0602-433f-b490-cbc465c89261

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision
import Theorems.Thm_ConsistentSubmodular_PolygonalPath_subdivide_edge

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

theorem mix_mix (p q : Point m) (a b x : ℝ) :
    mix (mix p q a) (mix p q b) x = mix p q ((1 - x) * a + x * b) := by
  funext i
  simp only [mix]
  ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

namespace PolygonalPath

theorem subdivide_terminal (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N) :
    (γ.subdivide N).node (Fin.last (γ.subdivide N).pieces) = γ.node (Fin.last γ.pieces) := by
  simp [subdivide, Nat.mul_div_cancel _ hN]

end PolygonalPath

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}
open ConsistentSubmodular.PolygonalPath

theorem solution {γ : PolygonalPath m} {Φ : Point m → Prop}
    (hγ : γ.Along Φ) (N : ℕ) (hN : 0 < N) : (γ.subdivide N).Along Φ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro j
    by_cases hj : j.val < (γ.subdivide N).pieces
    · obtain ⟨a, r, hr, he, _⟩ := γ.subdivide_edge N hN ⟨j.val, hj⟩
      have hjcast : (⟨j.val, hj⟩ : Fin (γ.subdivide N).pieces).castSucc = j := Fin.ext rfl
      rw [hjcast] at he
      rw [he]
      apply hγ.2 a _ (div_nonneg (Nat.cast_nonneg _) hn.le)
      apply (div_le_one hn).mpr
      exact_mod_cast Nat.le_of_lt hr
    · have he : j = Fin.last (γ.subdivide N).pieces := Fin.ext (by simp only [Fin.val_last]; have := j.isLt; omega)
      rw [he, γ.subdivide_terminal N hN]
      exact hγ.1 _
  · intro j x hx hx'
    obtain ⟨a, r, hr, hl, hu⟩ := γ.subdivide_edge N hN j
    rw [hl, hu, mix_mix]
    apply hγ.2 a
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hx') (by positivity))
        (mul_nonneg hx (by positivity))
    · have hb : ((r : ℝ) + 1) / N ≤ 1 := by
        apply (div_le_one hn).mpr
        exact_mod_cast (show r + 1 ≤ N by omega)
      have ha : (r : ℝ) / N ≤ 1 := by
        apply (div_le_one hn).mpr
        exact_mod_cast Nat.le_of_lt hr
      nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr ha),
        mul_nonneg hx (sub_nonneg.mpr hb)]

end
