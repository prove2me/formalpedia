-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.exists_far
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:34.914849+00:00
-- url     : https://prove2.me/submissions/3cb71539-6589-4e3b-a79b-4a3f765844bd

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] (T : ℝ) :
    ∃ y ∈ La, ∀ v, T ≤ ‖y v‖ := by
  let b := Module.Free.chooseBasis ℤ La
  let bR := b.ofZLatticeBasis ℝ La
  set γ : ℝ := ∑ i, ‖bR i‖ with hγ
  have hγ0 : 0 ≤ γ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  let w : V f := fun _ => ((|T| + γ : ℝ) : ℂ)
  refine ⟨(ZSpan.floor bR w : V f), ?_, ?_⟩
  · have h := (ZSpan.floor bR w).2
    have hs : Submodule.span ℤ (Set.range bR) = La := Module.Basis.ofZLatticeBasis_span ℝ La b
    exact hs.le h
  · intro v
    have h1 := ZSpan.norm_fract_le bR w
    rw [ZSpan.fract_apply] at h1
    have h2 : ‖(w - (ZSpan.floor bR w : V f)) v‖ ≤ ‖w - (ZSpan.floor bR w : V f)‖ :=
      norm_le_pi_norm (w - (ZSpan.floor bR w : V f)) v
    have h3 : ‖w v‖ = |T| + γ := by
      simp only [w, Complex.norm_real]
      exact Real.norm_of_nonneg (by positivity)
    have h4 := norm_sub_norm_le (w v) ((ZSpan.floor bR w : V f) v)
    rw [Pi.sub_apply] at h2
    have h5 : T ≤ |T| := le_abs_self T
    linarith
end Formalism.FourierDecayAlt.P.BoxAverageLimits
