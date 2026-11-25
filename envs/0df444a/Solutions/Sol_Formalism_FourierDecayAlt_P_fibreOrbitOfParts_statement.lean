-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fibreOrbitOfParts_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:06.50279+00:00
-- url     : https://prove2.me/submissions/9a6c158f-9b22-4885-8342-7b6b06ac100b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_fix_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 C2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.FibreOrbitOfParts := by
  intro hW hFF hGB hC1 k r z z' hstd g₁ hg₁ g₂ hg₂ hG hZ
  have hG2 : 0 < Gf k r z z' g₂ := by
    have : Gf k r z z' g₂ = Gf k r z z' g₁ := by unfold Gf Dmin; rw [hZ]
    rw [this]; exact hG
  have hli1 := (hC1 k r z z' g₁ hstd ⟨hg₁, hG⟩).1
  have hli2 := (hC1 k r z z' g₂ hstd ⟨hg₂, hG2⟩).1
  have hgram : ∀ i j, herm (Hpk k r) (gramVec k r z z' g₁ i) (gramVec k r z z' g₁ j) =
      herm (Hpk k r) (gramVec k r z z' g₂ i) (gramVec k r z z' g₂ j) := by
    intro i j
    have e : gramM k r z z' g₁ = gramM k r z z' g₂ := by
      rw [hGB k r z z' hstd.2.1 hstd.2.2 g₁ hg₁, hGB k r z z' hstd.2.1 hstd.2.2 g₂ hg₂, hZ]
    exact congrFun (congrFun e j) i
  obtain ⟨s0, hs0, hs0x⟩ := hW k r _ (gramVec k r z z' g₁) (gramVec k r z z' g₂) hli1 hli2 hgram
  have hs0F : s0 ∈ C2.FixSet k r z := ⟨hs0, fun a => hs0x (Sum.inl a)⟩
  have hu0 : IsUnit s0.det := WeylGroupFacts.isUnit_of_uh hs0
  have hu1 : IsUnit g₁.det := WeylGroupFacts.isUnit_of_uh hg₁
  have hu2 : IsUnit g₂.det := WeylGroupFacts.isUnit_of_uh hg₂
  set t := g₂⁻¹ * s0 * g₁ with ht
  have htF : t ∈ C2.FixSet k r z' := by
    refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hg₂) hs0) hg₁, fun b => ?_⟩
    have := hs0x (Sum.inr b)
    simp only [gramVec] at this
    rw [ht, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu2, Matrix.one_mulVec]
  have hut : IsUnit t.det := WeylGroupFacts.isUnit_of_uh htF.1
  refine ⟨s0⁻¹, ?_, t⁻¹, ?_, ?_⟩
  · rw [← hFF k r z hstd.2.1]; exact fix_inv hs0F
  · rw [← hFF k r z' hstd.2.2]; exact fix_inv htF
  · rw [Matrix.nonsing_inv_nonsing_inv _ hu0]
    have e : g₂ * t = s0 * g₁ := by
      rw [ht, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]
    calc g₂ = g₂ * t * t⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut, Matrix.mul_one]
      _ = s0 * g₁ * t⁻¹ := by rw [e]
end Formalism.FourierDecayAlt.P
