-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.trans_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:49.415289+00:00
-- url     : https://prove2.me/submissions/b8057efe-55d4-4665-a62b-7d0548e308f0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_self_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) (z v₁ v₂ : Fin m → ℂ) (T : ℝ) (hT : T ≠ 0)
    (hz : herm H z z = -(T : ℂ)) (h12 : herm H v₁ v₁ = herm H v₂ v₂) (hζ : herm H v₁ z = herm H v₂ z)
    (hne : (herm H v₁ v₁).re * T + Complex.normSq (herm H v₁ z) ≠ 0) :
    ∃ g ∈ UH H, g *ᵥ z = z ∧ g *ᵥ v₁ = v₂ := by
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  set ζ : ℂ := herm H v₁ z with hζdef
  set q : ℝ := ((herm H v₁ v₁).re * T + Complex.normSq ζ) / T with hqdef
  have hq : q ≠ 0 := div_ne_zero hne hT
  have key : ∀ v : Fin m → ℂ, herm H v z = ζ → herm H v v = herm H v₁ v₁ →
      herm H (v + (ζ / T) • z) (v + (ζ / T) • z) = q ∧ herm H z (v + (ζ / T) • z) = 0 := by
    intro v hv hvv
    have hzv : herm H z v = star ζ := by rw [herm_symm H hH v z, hv]
    have hst : star (ζ / (T : ℂ)) = star ζ / T := by simp
    have hns : (Complex.normSq ζ : ℂ) = ζ * star ζ := by
      rw [Complex.star_def, Complex.mul_conj]
    constructor
    · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hv, hzv, hz, hvv, hst]
      rw [herm_self_real H hH v₁, hqdef]
      push_cast
      rw [hns]
      field_simp
      ring
    · simp only [herm_add_right, herm_smul_right, hzv, hz, hst]
      field_simp
      ring
  obtain ⟨h1a, h1b⟩ := key v₁ rfl rfl
  obtain ⟨h2a, h2b⟩ := key v₂ hζ.symm h12.symm
  obtain ⟨g, hg, hga, hgx⟩ := trans H hH _ _ q hq h1a h2a
  have hgz : g *ᵥ z = z := hgx z h1b h2b
  refine ⟨g, hg, hgz, ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hgz] at hga
  exact add_right_cancel hga
end Formalism.FourierDecayAlt.P.TwoByOneBlock
