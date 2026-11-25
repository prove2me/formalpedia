-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.block_poisson_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:34.281086+00:00
-- url     : https://prove2.me/submissions/1b023451-0c49-42c8-9396-738697ad007e

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx4_rd_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.BlockPoissonFrame := by
  intro hEmb hTD hTw hPow E _ _ _ g r hg i hi1 hi2
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hdd : S6.dd E ≠ 0 := by
    unfold S6.dd
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    first
      | exact differentIdeal_ne_bot
      | (intro h; have h2 := NumberField.absNorm_differentIdeal (K := E); rw [h, Ideal.absNorm_bot] at h2; exact NumberField.discr_ne_zero E (Int.natAbs_eq_zero.mp h2.symm))
  have hB0 : ∀ ν : ℤ, S6.idl E g 2 ν ≠ 0 := by
    intro ν
    unfold S6.idl
    refine mul_ne_zero (zpow_ne_zero _ hdd) ?_
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact zpow_ne_zero _ hgE
  have hBA : ∀ ν : ℤ, S6.idl E g 2 ν ≤ S6.idl E g 1 ν := by
    intro ν
    unfold S6.idl
    have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) ≤
        FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ)) := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
      exact ⟨(g : 𝓞 E), by simp only [Algebra.smul_def, map_natCast, zpow_one, zpow_two]⟩
    first
      | exact FractionalIdeal.mul_le.mpr fun a ha b hb => FractionalIdeal.mul_mem_mul ha (hs hb)
      | exact mul_le_mul_left' hs _
      | (gcongr; exact hs)
  have hc0 : S6.rd E ^ (-(S6.nuBlock r i 1)) ≠ 0 := zpow_ne_zero _ (Jx4.rd_pos E).ne'
  obtain ⟨hinj, -, -, hsm, -⟩ := hEmb E
  refine ⟨?_, ?_, ?_, ?_⟩
  · beta_reduce
    have hfun : ⇑(semb E (S6.rd E ^ (-(S6.nuBlock r i 1)))) =
        fun t => S6.rd E ^ (-(S6.nuBlock r i 1)) • cemb E t := funext (hsm _)
    rw [hfun]
    exact (smul_right_injective (CV E) hc0).comp hinj
  · beta_reduce
    intro t ht
    exact Submodule.mem_map.mpr ⟨t, ht, rfl⟩
  · beta_reduce
    unfold dm
    ext w
    simp
  · beta_reduce
    intro μ hμ
    have hL := hTw E _ _ 1 (hB0 (S6.nuBlock r i 1)) (hBA _) (hPow E g 2 (S6.nuBlock r i 1))
    exact (hTD E _ g _ hg hc0 hL.2 μ).1 hμ
end Formalism.FourierDecayAlt.P
