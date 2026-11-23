-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.shift_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:19.569835+00:00
-- url     : https://prove2.me/submissions/e03f7b11-50d4-417f-b39c-7a70b4ee4ba7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add__182a426a02a7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) {d : ℕ} {n : ℤ} (hn : 1 ≤ n) {t t₁ : Kˣ} {σ : K}
    (hσ : σ ∈ Pk R ϖ (-(d : ℤ))) (ht : (t : K) ∈ Pk R ϖ (n + d)) (hs : IsShift t t₁ σ) :
    ∃ μ ∈ Pk R ϖ n, (t₁ : K) = t * (1 + μ) ∧ (1 + σ * t) * (1 + μ) = 1 ∧ σ * t ∈ Pk R ϖ n := by
  have hσt : σ * t ∈ Pk R ϖ n := by
    have := Pk_mul hσ ht
    convert this using 2; ring
  obtain ⟨μ, hμ, hμ1⟩ := inv_one_add' h hn hσt
  refine ⟨μ, hμ, ?_, hμ1, hσt⟩
  have e1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t₁
  have e2 : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t
  have hs' : ((t₁⁻¹ : Kˣ) : K) = ((t⁻¹ : Kˣ) : K) + σ := hs
  have e3 : (t₁ : K) * (1 + σ * t) = t := by
    linear_combination (-(t : K) * t₁) * hs' + (t : K) * e1 - (t₁ : K) * e2
  calc (t₁ : K) = t₁ * ((1 + σ * t) * (1 + μ)) := by rw [hμ1, mul_one]
    _ = t * (1 + μ) := by rw [← mul_assoc, e3]
end Formalism.FourierDecayAlt.P.HenselRootsBounded
