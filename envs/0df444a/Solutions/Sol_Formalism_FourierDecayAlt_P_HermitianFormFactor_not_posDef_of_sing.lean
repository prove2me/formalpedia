-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.not_posDef_of_sing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:18:15.190721+00:00
-- url     : https://prove2.me/submissions/f99ae149-3060-42ca-a458-dc3266bf3cd6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (M : Matrix Q Q ℂ) (n : Q → ℂ) (hn : n ≠ 0) (hM : Mᴴ *ᵥ n = 0) (j₀ : Q) (s : ℝ) (hs : s ≤ 0) :
    ¬ (Mᴴ * M + (s : ℂ) • Matrix.single j₀ j₀ (1 : ℂ)).PosDef := by
  intro hP
  have hd : Mᴴ.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨n, hn, hM⟩
  have hd' : M.det = 0 := by
    rw [Matrix.det_conjTranspose] at hd; exact star_eq_zero.mp hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd'
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hP hv
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_zero, zero_add] at hpos
  have hval : star v ⬝ᵥ (((s : ℂ) • Matrix.single j₀ j₀ (1 : ℂ)) *ᵥ v) =
      ((s * Complex.normSq (v j₀) : ℝ) : ℂ) := by
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Complex.normSq_eq_conj_mul_self]
    rw [Finset.sum_eq_single j₀]
    · first
      | (simp; done)
      | (simp; ring)
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hval, Complex.zero_lt_real] at hpos
  nlinarith [Complex.normSq_nonneg (v j₀)]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
