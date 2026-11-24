-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fibre_orbit_description
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:08.956216+00:00
-- url     : https://prove2.me/submissions/d1483882-fe7e-4aa5-8608-7bfeb6d0e1f2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WittOrthonormalBasis
import Theorems.Thm_Formalism_FourierDecayAlt_P_WittOrthonormalBasis_witt_nd
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_col_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_fixed_frame_property
import Theorems.Thm_Formalism_FourierDecayAlt_P_gram_block_form
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_mul
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction WittOrthonormalBasis
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.FibreOrbit := by
  intro k r z z' hstd g₁ hg₁ g₂ hg₂ hG hZ
  have hH2 : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r

  have hunit : ∀ g ∈ B.GV k r, IsUnit g.det := by
    intro g hg
    have hg' : g ᴴ * Hpk k r * g = Hpk k r := hg
    have : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
      calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hH2]
    exact Matrix.isUnit_det_of_left_inverse this
  have hinv : ∀ g ∈ B.GV k r, g⁻¹ ∈ B.GV k r := by
    intro g hg
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
    calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
      _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ (hunit g hg)]; simp
  have hmul : ∀ g ∈ B.GV k r, ∀ h ∈ B.GV k r, g * h ∈ B.GV k r := by
    intro g hg h hh
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
    show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg', hh']
  have hGf : Gf k r z z' g₂ = Gf k r z z' g₁ := by simp only [Gf, Dmin, hZ]
  have hp1 : C2.PosPt k r z z' g₁ := ⟨hg₁, hG⟩
  have hp2 : C2.PosPt k r z z' g₂ := ⟨hg₂, by rw [hGf]; exact hG⟩
  have hgram : gramM k r z z' g₁ = gramM k r z z' g₂ := by
    rw [gram_block_form k r z z' hstd.2.1 hstd.2.2 g₁ hg₁, gram_block_form k r z z' hstd.2.1 hstd.2.2 g₂ hg₂,
      hZ]
  rw [gn_gramM_eq, gn_gramM_eq] at hgram
  obtain ⟨s0, hs0, hs0V⟩ := witt_nd hstd hp1 hp2 hgram
  have hcol : ∀ j, s0 *ᵥ gramVec k r z z' g₁ j = gramVec k r z z' g₂ j := by
    intro j
    rw [← col_mul s0 z z' g₁ j, hs0V]
    rfl
  have hfa : ∀ a, s0 *ᵥ fvec k r z a = fvec k r z a := fun a => hcol (Sum.inl a)
  have hfb : ∀ b, s0 *ᵥ (g₁ *ᵥ fvec k r z' b) = g₂ *ᵥ fvec k r z' b := fun b => hcol (Sum.inr b)
  have hu0 := hunit s0 hs0
  have hu1 := hunit g₁ hg₁
  have hu2 := hunit g₂ hg₂
  refine ⟨s0⁻¹, ?_, g₁⁻¹ * s0⁻¹ * g₂, ?_, ?_⟩
  · rw [← fixed_frame_property k r z hstd.2.1]
    refine ⟨hinv s0 hs0, fun a => ?_⟩
    calc s0⁻¹ *ᵥ fvec k r z a = s0⁻¹ *ᵥ (s0 *ᵥ fvec k r z a) := by rw [hfa]
      _ = fvec k r z a := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu0, Matrix.one_mulVec]
  · rw [← fixed_frame_property k r z' hstd.2.2]
    refine ⟨hmul _ (hmul _ (hinv g₁ hg₁) _ (hinv s0 hs0)) _ hg₂, fun b => ?_⟩
    calc (g₁⁻¹ * s0⁻¹ * g₂) *ᵥ fvec k r z' b = g₁⁻¹ *ᵥ (s0⁻¹ *ᵥ (g₂ *ᵥ fvec k r z' b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = g₁⁻¹ *ᵥ (s0⁻¹ *ᵥ (s0 *ᵥ (g₁ *ᵥ fvec k r z' b))) := by rw [hfb]
      _ = fvec k r z' b := by
          have e0 : s0⁻¹ *ᵥ (s0 *ᵥ (g₁ *ᵥ fvec k r z' b)) = g₁ *ᵥ fvec k r z' b := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu0, Matrix.one_mulVec]
          rw [e0, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu1, Matrix.one_mulVec]
  · rw [Matrix.nonsing_inv_nonsing_inv _ hu0]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc s0 g₁ g₁⁻¹, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu0,
      Matrix.one_mul]
end Formalism.FourierDecayAlt.P
