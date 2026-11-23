-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.TT_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.074131+00:00
-- url     : https://prove2.me/submissions/7ddea399-b949-4be6-ab3a-19f7dd96dc28

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
theorem _root_.solution {s : ℕ} {Cut : Set K} {τ : Kˣ} {F G : Kˣ → ℂ} (υ : Kˣ)
    (hcut : ∀ c : Kˣ, (c : K) ∈ Cut ↔ ((υ ^ s * c : Kˣ) : K) ∈ Cut)
    (hG : ∀ c z : Kˣ, (c : K) ∈ Cut → z ^ s = τ * c → F (z * υ) = G z) (c : Kˣ) :
    TT s Cut τ F (υ ^ s * c) = TT s Cut τ G c := by
  classical
  unfold TT
  by_cases hc : (c : K) ∈ Cut
  · rw [if_pos hc, if_pos ((hcut c).1 hc), ← finsum_comp_equiv (Equiv.mulRight υ)]
    refine finsum_congr fun z => ?_
    have hiff : (z * υ) ^ s = τ * (υ ^ s * c) ↔ z ^ s = τ * c := by
      rw [mul_pow, mul_left_comm τ, mul_comm (z ^ s)]
      exact mul_right_inj _
    show (if (z * υ) ^ s = τ * (υ ^ s * c) then F (z * υ) else 0) = _
    by_cases hz : z ^ s = τ * c
    · rw [if_pos hz, if_pos (hiff.2 hz), hG c z hc hz]
    · rw [if_neg hz, if_neg (fun hh => hz (hiff.1 hh))]
  · rw [if_neg hc, if_neg (fun hh => hc ((hcut c).2 hh))]
end Formalism.FourierDecayAlt.P.HenselRootsBounded
