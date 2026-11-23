-- Prove2me | solution 1 for Formalism.REAL.compact_highest_weight_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:34.166902+00:00
-- url     : https://prove2.me/submissions/5296dce1-a3fb-4c47-bd42-159957429562

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_glRel_kRel
import Theorems.Thm_Formalism_REAL_isUnitary_kUnit


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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (hl : KLow) (hw : KWtOrth) {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ ν : Fin n → ℝ} {u y : V}
    (hg : GlRel E) (hu : IsUnitary ε E) (hΛ : KHighest ε E Λ u) (hy : y ∈ kSpan ε E u)
    (hyh : KHighest ε E ν y) (hy0 : y ≠ 0) : ν = Λ := by
  by_contra hne
  have hk := isUnitary_kUnit ε E hu
  obtain ⟨hspan, -⟩ := hl V n ε E Λ u (glRel_kRel ε E hg) hΛ
  rw [hspan] at hy
  have key : ∀ z ∈ lowSpan ε E u, ⟪z, y⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw', rfl⟩ := hx
      cases w with
      | nil => simpa [ew] using hw V n ε E Λ ν u y hk hΛ.1 hyh.1 (Ne.symm hne)
      | cons p w =>
        have hp := hw' p (List.mem_cons_self ..)
        simp only [ew, Module.End.mul_apply]
        rw [hk p.1 p.2 hp.1, hyh.2 p.2 p.1 hp.2 hp.1.symm, inner_zero_right]
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_left, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  exact hy0 (inner_self_eq_zero.mp (key y hy))
end Formalism.REAL
