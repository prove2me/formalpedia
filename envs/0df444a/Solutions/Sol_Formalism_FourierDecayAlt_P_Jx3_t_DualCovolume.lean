-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.t_DualCovolume
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:42.345865+00:00
-- url     : https://prove2.me/submissions/47f98424-d712-4aec-b6d7-c1caf957724d

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
theorem _root_.solution : DualCovolume := by
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
  have hc : S6.rd E ^ (ν + 1) ≠ 0 := (zpow_pos hrd _).ne'
  have hidx0 : S6.idx E (S6.zsub E (S6.idl E g 0 (-(ν + 1)))) (S6.dualLat E g (S6.perLat E g ν s)) ≠ 0 := by
    rw [hi]; positivity
  obtain ⟨-, -, h3⟩ := hCov E _ _ (S6.rd E ^ (ν + 1)) hB0 hc hle hidx0
  rw [h3, hi, norm_B hNorm E g ν hg, sqrt_disc hDeg E, abs_of_pos (zpow_pos hrd _)]
  have e1 : (S6.rd E ^ (ν + 1)) ^ (2 * S6.deg E) * ((S6.rd E ^ (-(ν + 1))) ^ S6.deg E) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (S6.deg E) 2, ← mul_pow, ← zpow_add₀ hrd.ne']
    simp
  rw [e1, one_mul]
  push_cast
  rw [div_pow, div_pow, inv_pow]
  field_simp
end Formalism.FourierDecayAlt.P.Jx3
