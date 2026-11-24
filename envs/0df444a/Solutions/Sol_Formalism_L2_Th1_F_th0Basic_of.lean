-- Prove2me | solution 1 for Formalism.L2.Th1.F.th0Basic_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:04.541852+00:00
-- url     : https://prove2.me/submissions/a28ddcee-d46a-43e8-ba46-bc4208b95ccf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_sub_swap
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_thetaZero_periodLattice_eq
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_th0Const_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ThetaZeroHermitianLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution (hb : SgStarBasic) (hq : SgStarQuasi) (hi : AltEInt) : ThetaZeroBasic := by
  intro L ω₀ hω hn
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn ⊢
  have hs : sgStar L t ≠ 0 := fun h0 => hn (((hb L).2.2.1 t).1 h0)
  have hχ : semiChar L (t + t) = -1 := by
    rw [semiChar, if_neg (by rw [h2]; exact hn)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hd := (hb L).1
    show Differentiable ℂ (fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0)
    simp only [opU, herm]
    fun_prop
  · simp only [th0]
    exact div_self ((th0Const_of hb L t).2 hn)
  · intro z
    rw [thetaZero_periodLattice_eq L t (-z), thetaZero_periodLattice_eq L t z]
    have h1 : sgStar L (-z + t) = -sgStar L (z - t) := by
      rw [show -z + t = -(z - t) by ring]; exact (hb L).2.1 _
    have h3 := hq L (t + t) (z - t) hω
    rw [show z - t + (t + t) = z + t by ring, hχ] at h3
    have key : Complex.exp (-(Real.pi : ℂ) * herm L (-z) t)
        = Complex.exp ((Real.pi : ℂ) * herm L (z - t) (t + t) + (Real.pi : ℂ) * herm L (t + t) (t + t) / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [← Complex.exp_add]; congr 1
      simp only [herm, map_add, map_neg, map_sub]; ring
    rw [h1, h3]
    linear_combination (-sgStar L (z - t) / sgStar L t) * key
  · intro z
    rw [thetaZero_periodLattice_eq, div_eq_zero_iff, mul_eq_zero, (hb L).2.2.1]
    simp [Complex.exp_ne_zero, hs]
  · intro ω hω' z
    obtain ⟨k, hk⟩ := hi L ω (t + t) hω' hω
    have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
        = Complex.exp (-((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))) := by
      rw [hk]; push_cast; exact (exp_pi_int k).symm
    have hsw := herm_sub_swap L (t + t) ω
    have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L (z + ω) t)
        = Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [he]; simp only [← Complex.exp_add]; congr 1
      simp only [herm, map_add] at hsw ⊢
      linear_combination ((Real.pi : ℂ) / 2) * hsw
    rw [thetaZero_periodLattice_eq L t (z + ω), thetaZero_periodLattice_eq L t z, show z + ω + t = (z + t) + ω by ring, hq L ω (z + t) hω']
    linear_combination (semiChar L ω * sgStar L (z + t) / sgStar L t) * key
end Formalism.L2.Th1.F
