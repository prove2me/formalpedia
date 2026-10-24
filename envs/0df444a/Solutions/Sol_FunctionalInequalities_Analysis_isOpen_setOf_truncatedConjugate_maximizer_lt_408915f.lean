-- Prove2me | solution 1 for FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:10:39.672404+00:00
-- url     : https://prove2.me/submissions/da8eb867-4d2e-42f1-b5fe-a65e671642f3

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_convexOn_truncatedConjugate_408915f

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F3TruncatedConjugateSubgradients
open Set Metric
open scoped RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.n7_isClosed_bad_maximizers [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) {C : Set E} (hC : IsClosed C) :
    IsClosed {p : E | ∃ x ∈ closedBall (0 : E) M,
      x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
  let B := closedBall (0 : E) M
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 M)
  have hT : Continuous (truncatedConjugate u M) :=
    continuousOn_univ.mp ((convexOn_truncatedConjugate_408915f hu hM).continuousOn isOpen_univ)
  let D : Set (B × E) :=
    {q | (q.1 : E) ∈ C ∧ truncatedConjugate u M q.2 = ⟪q.2, (q.1 : E)⟫ - u q.1}
  have hD : IsClosed D :=
    (hC.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isClosed_eq (hT.comp continuous_snd)
        ((continuous_snd.inner (continuous_subtype_val.comp continuous_fst)).sub
          (hu.comp (continuous_subtype_val.comp continuous_fst))))
  have he : Prod.snd '' D =
      {p : E | ∃ x ∈ closedBall (0 : E) M,
        x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hx, rfl⟩
      exact ⟨x, x.property, hx⟩
    · rintro ⟨x, hx, hc, he⟩
      exact ⟨(⟨x, hx⟩, p), ⟨hc, he⟩, rfl⟩
  rw [← he]
  exact isClosedMap_snd_of_compactSpace D hD
section FiniteDimensional
variable [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The set of slopes whose ball maximisers all lie in the open ball is open (weak Letwin route). -/
theorem solution {u : E → ℝ} (hu : Continuous u) {M : ℝ}
    (hM : 0 ≤ M) :
    IsOpen {p : E | ∀ x ∈ closedBall (0 : E) M,
      FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} := by
  classical
  have hc : IsClosed {x : E | M ≤ ‖x‖} :=
    isClosed_le continuous_const continuous_norm
  have he :
      {p : E | ∀ x ∈ closedBall (0 : E) M,
        FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} =
      {p : E | ∃ x ∈ closedBall (0 : E) M,
        x ∈ {x : E | M ≤ ‖x‖} ∧
          FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x}ᶜ := by
    ext p
    constructor
    · intro hp
      rintro ⟨x, hx, hn, heq⟩
      exact (not_lt_of_ge hn) (hp x hx heq)
    · intro hp x hx heq
      by_contra hn
      exact hp ⟨x, hx, le_of_not_gt hn, heq⟩
  rw [he]
  exact (n7_isClosed_bad_maximizers hu hM hc).isOpen_compl
