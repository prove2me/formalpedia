-- Prove2me | solution 1 for Formalism.HN.PolygonExample.one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:14.527797+00:00
-- url     : https://prove2.me/submissions/bfe4ad9d-9d71-4660-8375-9d387513be2d

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_coord0
import Theorems.Thm_Formalism_HN_PolygonExample_coord1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PolygonExample
namespace Formalism.HN.PolygonExample
theorem _root_.solution {x : E2} (hx : x ∈ Lx) (h0 : x ≠ 0) : 1 ≤ ‖x‖ := by
  have key : ∀ (y : E2) (i : Fin 2), |y i| ≤ ‖y‖ := by
    intro y i
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    simpa [Real.norm_eq_abs, sq_abs] using this
  rw [Lx, Submodule.mem_span_pair] at hx
  obtain ⟨m, n, rfl⟩ := hx
  by_cases hm : m = 0
  · have hn : n ≠ 0 := by
      rintro rfl
      subst hm
      exact h0 (by simp)
    have k1 := key (m • e₀ + n • ((2 : ℝ) • e₁)) 1
    rw [coord1, abs_mul] at k1
    have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    norm_num at k1
    linarith
  · have k0 := key (m • e₀ + n • ((2 : ℝ) • e₁)) 0
    rw [coord0] at k0
    have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    linarith
end Formalism.HN.PolygonExample
