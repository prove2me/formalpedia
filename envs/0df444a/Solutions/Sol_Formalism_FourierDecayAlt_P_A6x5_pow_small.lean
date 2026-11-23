-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.pow_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:02.352802+00:00
-- url     : https://prove2.me/submissions/74818b1d-905a-42b0-974b-8721791e22f7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_eq_zero_of_forall_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R)
    (V : Set K) (hV : V ∈ 𝓝 (0 : K)) : ∃ N : ℕ, ∀ r ∈ R, (ϖ : K) ^ N * r ∈ V := by
  have := hD.t2
  by_contra hcon
  push Not at hcon
  have hcomp : ∀ N : ℕ, IsCompact ((fun r => (ϖ : K) ^ N * r) '' (R : Set K)) := fun N =>
    hD.isCompact.image (continuous_const.mul continuous_id)
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun N : ℕ => ((fun r => (ϖ : K) ^ N * r) '' (R : Set K)) ∩ (interior V)ᶜ) ?_ ?_ ?_ ?_
  · obtain ⟨x, hx⟩ := hne
    rw [Set.mem_iInter] at hx
    have hx0 : x = 0 := by
      refine eq_zero_of_forall_pow hD hn ϖ hϖ x ?_
      intro N
      obtain ⟨r, hr, h⟩ := (hx N).1
      exact ⟨r, hr, h.symm⟩
    exact (hx 0).2 (hx0 ▸ mem_interior_iff_mem_nhds.2 hV)
  · intro N
    refine Set.inter_subset_inter_left _ ?_
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨(ϖ : K) * r, R.mul_mem hϖR hr, by simp only [pow_succ, mul_assoc]⟩
  · intro N
    obtain ⟨r, hr, h⟩ := hcon N
    exact ⟨_, ⟨r, hr, rfl⟩, fun h' => h (interior_subset h')⟩
  · exact (hcomp 0).inter_right isOpen_interior.isClosed_compl
  · intro N
    exact (hcomp N).isClosed.inter isOpen_interior.isClosed_compl
end Formalism.FourierDecayAlt.P.A6x5
