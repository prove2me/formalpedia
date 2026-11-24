-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.spec_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:25.464625+00:00
-- url     : https://prove2.me/submissions/0ee25339-a33f-4dd4-b2bc-1af83cb2b212

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SpecAbstract
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X : Type*}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {ι : Type*} (𝓕 : Set (X → (Wq →L[ℂ] Wp))) (G : Set X)
    (T : ℂ → (X → (Wq →L[ℂ] Wp)) → X → (Wq →L[ℂ] Wp)) (c : X → ℂ) (hc : ∀ g ∈ G, c g ≠ 0)
    (Y₀ : ℂ) (hA : ∀ F ∈ 𝓕, (fun x => (c x)⁻¹ • T Y₀ F x) ∈ 𝓕)
    (lam : ι → ℂ → ℂ) (S : X → ι → Submodule ℂ Wq)
    (heig : ∀ F ∈ 𝓕, ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ, ∀ Y, T Y F g v = (c g * lam σ Y) • F g v)
    (J : X → (Wq →L[ℂ] Wp)) (hJ : J ∈ 𝓕) (n : ℕ) :
    ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J ∈ 𝓕) ∧
      ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ,
        ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) g v = (lam σ Y₀) ^ n • J g v := by
  induction n with
  | zero => exact ⟨hJ, fun g _ σ v _ => by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact hA _ h1
    · intro g hg σ v hv
      rw [Function.iterate_succ_apply']
      simp only [ContinuousLinearMap.smul_apply]
      rw [heig _ h1 g hg σ v hv Y₀, h2 g hg σ v hv]
      simp only [smul_smul]
      congr 1
      have hcg := hc g hg
      rw [pow_succ]
      field_simp
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
