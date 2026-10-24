-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:56:29.824145+00:00
-- url     : https://prove2.me/submissions/45c3cb86-b752-44a0-8f87-9394338abeca

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
section
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.Semigroup.Generated in
/-- **`P8`**: `t ↦ P_t f` is continuous on `[0, ∞)`.  For `t₀ ≤ t` the semigroup law gives
`P_t f - P_{t₀} f = P_{t₀} (P_{t - t₀} f - f)`, which the contraction contraction bounds by
`‖P_{t - t₀} f - f‖`; for `t ≤ t₀` exchange the roles.  Then apply `P7`. -/
theorem solution (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) :
    ContinuousOn (fun t : ℝ => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, h⟩ := FunctionalInequalities.Analysis.Semigroup.Generated.continuous_at_zero T hT hd f hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht hdist
  simp only [Set.mem_Ici] at ht ht₀
  rw [Real.dist_eq] at hdist
  obtain ⟨hlow, hhigh⟩ := abs_lt.mp hdist
  simp only [dist_eq_norm]
  rcases le_total t₀ t with hle | hle
  · have hsum : t₀ + (t - t₀) = t := by ring
    have hsplit : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f
        = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t₀ (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t - t₀) f) := by
      rw [← FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd ht₀ (by linarith : (0 : ℝ) ≤ t - t₀), hsum]
    rw [hsplit, ← FunctionalInequalities.Analysis.Semigroup.Generated.map_sub T hT hd ht₀]
    exact lt_of_le_of_lt (FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le T hT hd ht₀ _)
      (h (t - t₀) (by linarith) (by linarith))
  · have hsum : t + (t₀ - t) = t₀ := by ring
    have hsplit : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t₀ f
        = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t₀ - t) f) := by
      rw [← FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd ht (by linarith : (0 : ℝ) ≤ t₀ - t), hsum]
    rw [hsplit, ← FunctionalInequalities.Analysis.Semigroup.Generated.map_sub T hT hd ht]
    refine lt_of_le_of_lt (FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le T hT hd ht _) ?_
    rw [norm_sub_rev]
    exact h (t₀ - t) (by linarith) (by linarith)
