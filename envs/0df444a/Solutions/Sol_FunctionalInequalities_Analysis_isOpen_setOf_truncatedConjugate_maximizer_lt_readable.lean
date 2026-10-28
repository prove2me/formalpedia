-- Prove2me | solution 1 for FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:38.895976+00:00
-- url     : https://prove2.me/submissions/f788c305-827c-4344-9a96-7dc5b55d4e53

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_convexOn_truncatedConjugate_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F3TruncatedConjugateSubgradients
open scoped RealInnerProductSpace Topology
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
    continuousOn_univ.mp ((convexOn_truncatedConjugate_readable hu hM).continuousOn isOpen_univ)
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
  exact (FunctionalInequalities.Analysis.n7_isClosed_bad_maximizers hu hM hc).isOpen_compl
