-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.Iset_disj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:46.821438+00:00
-- url     : https://prove2.me/submissions/83ac6787-ae96-4704-b8fe-6fdcc8329337

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} (ha : Antitone lam) (b : ℤ) (i j : Fin n)
    (hij : i ≠ j) :
    Disjoint ((Iset lam b i).image (fun y => y - (i : ℤ)))
      ((Iset lam b j).image (fun y => y - (j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_image, Iset, Finset.mem_Icc] at hx hx'
  obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ := hx
  obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := hx'
  have hmi : min (len lam i) b ≤ lam i.castSucc - lam i.succ := min_le_left _ _
  have hmj : min (len lam j) b ≤ lam j.castSucc - lam j.succ := min_le_left _ _
  rcases lt_or_gt_of_ne hij with h | h
  · have h2 : lam j.castSucc ≤ lam i.succ := ha (Fin.succ_le_castSucc_iff.mpr h)
    have h3 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast h
    omega
  · have h2 : lam i.castSucc ≤ lam j.succ := ha (Fin.succ_le_castSucc_iff.mpr h)
    have h3 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast h
    omega
end Formalism.LogVandermondeBounds.flipTwoThree
