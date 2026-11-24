-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.exists_of_vBB_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:31:55.12635+00:00
-- url     : https://prove2.me/submissions/ea1e8fe4-2c8a-4ff1-98b5-bba7342940fd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F : MvPolynomial σ K) (h : vBB v F = 0) :
    (∃ α ∈ F.support, vge v (-(vN v (fact α)) / 2) (F.coeff α) ∧
      vle v (-(vN v (fact α)) / 2) (F.coeff α)) ∧ bge v 0 F := by
  refine ⟨?_, (bge_iff v 0 F).mpr (by rw [h]; rfl)⟩
  have hne : F.support.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    unfold vBB at h
    rw [hc, Finset.inf_empty] at h
    exact absurd h (by simp)
  obtain ⟨α, hα, hinf⟩ := Finset.exists_mem_eq_inf F.support hne
    (fun α => vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ))
  refine ⟨α, hα, ?_⟩
  have h0 : vR v (F.coeff α) + ((vN v (fact α) / 2 : ℝ) : WithTop ℝ) = 0 := by
    rw [← h]; exact hinf.symm
  unfold vge vle
  cases hx : vR v (F.coeff α) with
  | top => rw [hx] at h0; simp at h0
  | coe y =>
    rw [hx, ← WithTop.coe_add] at h0
    have h1 : y + vN v (fact α) / 2 = 0 := by exact_mod_cast h0
    have h2 : y = -(vN v (fact α)) / 2 := by linarith
    rw [h2]
    exact ⟨le_refl _, le_refl _⟩
end Formalism.MainNotions.PlaneGram
