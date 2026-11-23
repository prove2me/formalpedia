-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.t_DualMeasureBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:00.7438+00:00
-- url     : https://prove2.me/submissions/eb317081-652b-451a-a128-a0568f5596aa

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_rd_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_idl_zero_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_sqrt_disc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_norm_B

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
open scoped Classical
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution : DualMeasureBound := by
  intro hDeg hConj hUnr hBet hIdx hSub hSup hNorm hCov E _ _ _ hU g ν s hg
  have hrd := rd_pos E
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hdual : S6.dualLat E g (S6.perLat E g ν s) =
      S6.twLat E (S6.dualIdl E g ν) (S6.idl E g 0 (-(ν + 1))) (s + 1) :=
    le_antisymm (hSub E g ν s hg) (hSup E hU g ν s hg)
  have hB := idl_zero_eq E g ν hg
  have hA0 : S6.dualIdl E g ν ≠ 0 := idl_ne_zero hNorm E g _ _ hg
  have hB0 : S6.idl E g 0 (-(ν + 1)) ≠ 0 := idl_ne_zero hNorm E g _ _ hg
  have hi := (hIdx E (S6.dualIdl E g ν) g (s + 1) hA0 (hConj E g _ _) hg ((hUnr E hU).2 g)).2
  rw [← hB, ← hdual] at hi
  have hle : S6.zsub E (S6.idl E g 0 (-(ν + 1))) ≤ S6.dualLat E g (S6.perLat E g ν s) := by
    rw [hdual]
    refine (hBet E _ _ (s + 1) ?_ (hConj E g _ _)).1
    rw [hB]
    have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) ≤ 1 := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff]
      exact ⟨(g : 𝓞 E), by simp⟩
    calc S6.dualIdl E g ν * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E)
        ≤ S6.dualIdl E g ν * 1 := by gcongr
      _ = S6.dualIdl E g ν := mul_one _
  have hidx0 : S6.idx E (S6.zsub E (S6.idl E g 0 (-(ν + 1)))) (S6.dualLat E g (S6.perLat E g ν s)) ≠ 0 := by
    rw [hi]; positivity
  obtain ⟨-, -, h3⟩ := hCov E _ _ 1 hB0 one_ne_zero hle hidx0
  have hx : 0 < S6.rd E ^ (-(ν + 1)) := zpow_pos hrd _
  have hNA : (FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ) =
      (((g : ℝ) ^ (-1 : ℤ) * S6.rd E ^ (-(ν + 1))) ^ S6.deg E) ^ 2 := by
    have h := hNorm E g (-1) (-(ν + 1)) hg
    unfold S6.dualIdl
    rw [← h, Real.sq_sqrt]
    exact_mod_cast (FractionalIdeal.absNorm_nonneg _)
  have hval : ZLattice.covolume (E := mixedEmbedding.mixedSpace E)
      (S6.frameLat E (S6.dualLat E g (S6.perLat E g ν s)) 1) =
      ((g : ℝ) * (S6.rd E / 2)) ^ S6.deg E * (FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ) := by
    rw [h3, hi, norm_B hNorm E g ν hg, sqrt_disc hDeg E, hNA, abs_one, one_pow, one_mul]
    set x := S6.rd E ^ (-(ν + 1)) with hxdef
    push_cast
    rw [zpow_neg_one, mul_pow, mul_pow, div_pow, inv_pow, inv_pow, mul_pow]
    field_simp
  refine ⟨hval, fun h2 => ?_⟩
  rw [hval]
  have hn : 0 < (FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ) := by
    rw [hNA]; positivity
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have ha : 1 ≤ ((g : ℝ) * (S6.rd E / 2)) ^ S6.deg E := by
    apply one_le_pow₀
    nlinarith
  apply inv_anti₀ hn
  nlinarith
end Formalism.FourierDecayAlt.P.Jx3
