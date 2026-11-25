-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.comp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:38.522898+00:00
-- url     : https://prove2.me/submissions/00078cec-463f-4bcb-9449-e4356bb15108

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_lap_map
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_rowShift_map
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_coeff_comp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {K : Type} [Field K] [CharZero K] {σ : Type}
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (lam : K →ₗ[ℚ] ℚ) {P : MvPolynomial (Letter Ty r n) K} (hP : P ∈ HHa r n K cc isX a) :
    comp lam P ∈ HHa r n ℚ cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  have hmono : ∀ m : Letter Ty r n →₀ ℕ, monomial m (1 : K) = map (algebraMap ℚ K) (monomial m (1 : ℚ)) := by
    intro m
    rw [map_monomial, (algebraMap ℚ K).map_one]
  refine ⟨?_, fun σ i i' hii t => ?_, fun m hm => ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ a0 a1
    have hc := comp_comm lam (lap r n K 1 τ (cc τ) a0 a1) (lap r n ℚ 1 τ (cc τ) a0 a1)
      (fun m => by rw [hmono, lap_map]) P
    rw [h1 τ hτ a0 a1, comp_zero] at hc
    exact hc.symm
  · have hc := comp_comm lam (rowShift r n K σ i i' (algebraMap ℚ K t)).toLinearMap
      (rowShift r n ℚ σ i i' t).toLinearMap (fun m => by
        simp only [AlgHom.toLinearMap_apply]
        rw [hmono, rowShift_map]) P
    simp only [AlgHom.toLinearMap_apply] at hc
    rw [h2 σ i i' hii] at hc
    exact hc.symm
  · rw [mem_support_iff, coeff_comp] at hm
    exact h3 m (mem_support_iff.mpr fun h0 => hm (by rw [h0, map_zero]))
end Formalism.L2.FormalSeriesBounds.HaP
