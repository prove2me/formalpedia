-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.TT_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.068605+00:00
-- url     : https://prove2.me/submissions/9c3a937f-db8c-4200-b789-a187d7864417

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded

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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution {R : Subring K} {s : ℕ} {Cut : Set K} {τ : Kˣ} {F : Kˣ → ℂ}
    (hω : ∀ c c' : Kˣ, (c' : K) - c ∈ R → (c : K) ∈ Cut → (c' : K) ∈ Cut ∧
      ∃ ω : Kˣ, c' = c * ω ^ s ∧ ∀ z : Kˣ, z ^ s = τ * c → F (z * ω) = F z)
    (c c' : Kˣ) (hcc : (c' : K) - c ∈ R) : TT s Cut τ F c' = TT s Cut τ F c := by
  classical
  unfold TT
  by_cases hc : (c : K) ∈ Cut
  · obtain ⟨hc', ω, hcω, hF⟩ := hω c c' hcc hc
    rw [if_pos hc, if_pos hc', ← finsum_comp_equiv (Equiv.mulRight ω)]
    refine finsum_congr fun z => ?_
    have hiff : (z * ω) ^ s = τ * c' ↔ z ^ s = τ * c := by
      rw [hcω, mul_pow, ← mul_assoc]
      exact mul_left_inj _
    show (if (z * ω) ^ s = τ * c' then F (z * ω) else 0) = _
    by_cases hz : z ^ s = τ * c
    · rw [if_pos hz, if_pos (hiff.2 hz), hF z hz]
    · rw [if_neg hz, if_neg (fun hh => hz (hiff.1 hh))]
  · have hc' : (c' : K) ∉ Cut := by
      intro hc'
      have : (c : K) - c' ∈ R := by
        have := R.neg_mem hcc
        simpa using this
      exact hc (hω c' c this hc').1
    rw [if_neg hc, if_neg hc']
end Formalism.FourierDecayAlt.P.HenselRootsBounded
