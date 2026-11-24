-- Prove2me | solution 1 for Formalism.L2.Th1.E.Th0Analytic_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:27.046323+00:00
-- url     : https://prove2.me/submissions/2f1d0a41-d039-45c3-9d35-f6d70282109d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_L2_Th1_E_Tor_nat_mul_mem
import Theorems.Thm_Formalism_L2_Th1_E_Tor_norm_natCast
import Theorems.Thm_Formalism_L2_Th1_E_Tor_nsmul_ptOf
import Theorems.Thm_Formalism_L2_Th1_E_Tor_restrict
import Theorems.Thm_Formalism_L2_Th1_E_Tor_cc_phL
import Theorems.Thm_Formalism_L2_Th1_E_Tor_cc_inU
import Theorems.Thm_Formalism_L2_Th1_E_Tor_inU_const_mul
import Theorems.Thm_Formalism_L2_Th1_E_Tor_gaussOne_C_mul
import Theorems.Thm_Formalism_L2_Th1_E_AnalyticTrans_of
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_iff_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Tor
open Classical
namespace Formalism.L2.Th1.E
theorem _root_.solution (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hU : TransUnit) (hG : TransGauss) (hO : OpUTh0Root) : ThetaZeroAnalytic := by
  intro l _ L ι hl2 hW ω₀ hω hω2
  have hl2' : ¬ l ∣ 2 := fun h => hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h2t : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by
    have e : ((2 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ := by
      push_cast
      ring
    rw [e]
    exact hω
  obtain ⟨hc1, hOne⟩ := AnalyticTrans_of hS hA hZ hI hU l L ι hW (ω₀ / 2) 2 (by norm_num) hl2' h2t hω2
  have hιc : ι (opU L (ω₀ / 2) (sgStar L) 0) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc1
    exact zero_ne_one hc1
  have hc : opU L (ω₀ / 2) (sgStar L) 0 ≠ 0 := fun h0 => hιc (by rw [h0, map_zero])
  have hth : th0 L (ω₀ / 2) =
      fun z => (opU L (ω₀ / 2) (sgStar L) 0)⁻¹ * opU L (ω₀ / 2) (sgStar L) z := by
    funext z
    rw [th0, div_eq_inv_mul]
  have hin : inU l L ι (th0 L (ω₀ / 2)) =
      C (ι (opU L (ω₀ / 2) (sgStar L) 0))⁻¹ * inU l L ι (opU L (ω₀ / 2) (sgStar L)) := by
    rw [hth, inU_const_mul, map_inv₀]
  have hcc : constantCoeff (inU l L ι (th0 L (ω₀ / 2))) = 1 := by
    rw [cc_inU, th0, div_self hc, map_one]
  have key : fExp (phL l L ι - phPrime l L ι (ω₀ / 2)) =
      C (ι (opU L (ω₀ / 2) (sgStar L) 0))⁻¹ * gT l L ι (ω₀ / 2) := by
    rw [phPrime, sub_neg_eq_add,
      Formalism.L2.Th1.B.fExp_add (cc_phL l L ι) (Formalism.L2.Th1.B.constantCoeff_fLog hcc),
      Formalism.L2.Th1.B.fExp_fLog hcc, hin, gT]
    ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change constantCoeff (phL l L ι - phPrime l L ι (ω₀ / 2)) = 0
    have h1 : constantCoeff (fLog (inU l L ι (th0 L (ω₀ / 2)))) = 0 :=
      Formalism.L2.Th1.B.constantCoeff_fLog hcc
    rw [phPrime, sub_neg_eq_add, map_add, cc_phL, h1, add_zero]
  · change Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) (fExp (phL l L ι - phPrime l L ι (ω₀ / 2)))
    rw [key]
    exact (Ser.intS_iff_integral _).1 hOne.2
  · intro t N hN hlN hNt
    have hN2 : ¬ l ∣ 2 * N := fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim hl2' hlN
    have e1 : ((2 * N : ℕ) : ℂ) * t = ((2 : ℕ) : ℂ) * ((N : ℂ) * t) := by
      push_cast
      ring
    have e2 : ((2 * N : ℕ) : ℂ) * (ω₀ / 2) = (N : ℂ) * ω₀ := by
      push_cast
      ring
    have m1 : ((2 * N : ℕ) : ℂ) * t ∈ L.lattice := by
      rw [e1]
      exact nat_mul_mem L 2 hNt
    have m2 : ((2 * N : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by
      rw [e2]
      exact nat_mul_mem L N hω
    have m3 : ((2 * N : ℕ) : ℂ) * (t + ω₀ / 2) ∈ L.lattice := by
      rw [mul_add]
      exact add_mem m1 m2
    obtain ⟨ζ, m, hm, hζ, hop⟩ := hO L t (ω₀ / 2) (2 * N) (by omega) m1 m2 hω2
    have hζ1 : ‖ι ζ‖ = 1 := by
      have h1 : ‖ι ζ‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, hζ, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
    obtain ⟨hIP, hTS⟩ := restrict l L ι hS hA hZ hI hW (t + ω₀ / 2) (2 * N) (by omega) hN2 m3
    have hg : GaussOne (gT l L ι (t + ω₀ / 2)) :=
      hG ℂ_[l] (curveL l L ι) hW (AddSubgroup.zmultiples (t + ω₀ / 2)) _ _ hIP hTS
        ⟨t + ω₀ / 2, AddSubgroup.mem_zmultiples _⟩ (2 * N) (norm_natCast l hN2)
        (by
          change (2 * N) • ptOf l L ι (t + ω₀ / 2) = 0
          rw [nsmul_ptOf l L ι hA hZ]
          exact (hZ l L ι _).2 m3)
    have e3 : fExp (phL l L ι) * inU l L ι (opU L t (th0 L (ω₀ / 2))) =
        C (ι (ζ * (opU L (ω₀ / 2) (sgStar L) 0)⁻¹)) * gT l L ι (t + ω₀ / 2) := by
      rw [hop, inU_const_mul, gT]
      ring
    rw [e3]
    refine gaussOne_C_mul ?_ hg
    rw [map_mul, map_inv₀, norm_mul, norm_inv, hζ1, hc1, inv_one, one_mul]
end Formalism.L2.Th1.E
