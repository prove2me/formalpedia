-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.Adic.inv_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:39.225734+00:00
-- url     : https://prove2.me/submissions/c88a80e3-0a99-4320-b449-3e58a0c955b5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_I_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_unit_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.A6x8
namespace Adic
theorem _root_.solution (h : Adic R ϖ) {Om : Set K} (hC : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ M : ℕ, ∀ z ∈ Om, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R := by
  refine hC.induction_on
    (p := fun S => ∃ M : ℕ, ∀ z ∈ S, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨M, hM⟩
    exact ⟨M, fun z hz => hM z (hST hz)⟩
  · rintro S T ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', fun z hz z' e => ?_⟩
    rcases hz with hz | hz
    · have := R.mul_mem (R.pow_mem h.mem M') (hM z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M' * ((ϖ : K) ^ M * z') := by ring
      rwa [e']
    · have := R.mul_mem (R.pow_mem h.mem M) (hM' z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M * ((ϖ : K) ^ M' * z') := by ring
      rwa [e']
  · intro x hx
    obtain ⟨u, rfl⟩ := hU x hx
    obtain ⟨M, hM⟩ := h.absorb ((u⁻¹ : Kˣ) : K)
    refine ⟨{z | (z - (u : K)) * ((u⁻¹ : Kˣ) : K) ∈ I R (ϖ : K)}, mem_nhdsWithin_of_mem_nhds ?_, M,
      fun z hz z' e => ?_⟩
    · have : ContinuousAt (fun z : K => (z - (u : K)) * ((u⁻¹ : Kˣ) : K)) (u : K) :=
        ((continuous_id.sub continuous_const).mul continuous_const).continuousAt
      exact this.preimage_mem_nhds (by simpa using I_nhds h.isOpen ϖ)
    · obtain ⟨v, hv, ev⟩ := h.unit_one _ hz
      have i1 : (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by simp
      have : z' = ((u⁻¹ : Kˣ) : K) * v := by
        linear_combination ((u⁻¹ : Kˣ) : K) * v * e - z' * v * i1 - z' * ev
      rw [this, ← mul_assoc]
      exact R.mul_mem hM hv
end Adic
end Formalism.FourierDecayAlt.P.A6x8
