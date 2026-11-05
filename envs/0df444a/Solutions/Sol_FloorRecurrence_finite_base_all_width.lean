-- Prove2me | solution 1 for FloorRecurrence.finite_base_all_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/57b8d37c-7fc1-47f2-8835-266fc7649222

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
import Theorems.Thm_FloorRecurrence_all_width_bound
import Theorems.Thm_FloorRecurrence_boundConstant_nonneg
import Theorems.Thm_FloorRecurrence_boundConstant_overhead
import Theorems.Thm_FloorRecurrence_boundConstant_base

set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution {ι : Type} (rows : List ι) (c : ι → ℝ) (t : ι → ℕ)
    (m : ℕ) (f : ℕ → ℝ) (p C γ : ℝ)
    (hm : 0 < m) (hp : 0 ≤ p)
    (hc : ∀ i ∈ rows, 0 ≤ c i) (ht : ∀ i ∈ rows, 0 < t i)
    (htm : ∀ i ∈ rows, t i < m)
    (hγ : γ = (rows.map (fun i => c i * ((t i : ℝ) / m) ^ p)).sum) (hγ1 : γ < 1)
    (physical_recurrence : ∀ e, m ≤ e →
      f e ≤ C + (rows.map (fun i => c i * f (t i * (e / m)))).sum) :
    ∀ e, 0 < e → f e ≤ boundConstant m f C γ * (e : ℝ) ^ p :=
  all_width_bound rows c t m f p (boundConstant m f C γ) C γ hm hp
    (boundConstant_nonneg m f C γ hγ1) hc ht htm hγ hγ1
    (boundConstant_overhead m f C γ hγ1)
    (boundConstant_base m f C γ p hγ1 hp) physical_recurrence
end FloorRecurrence
