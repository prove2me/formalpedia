-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.toFS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:40.210519+00:00
-- url     : https://prove2.me/submissions/c36f9962-6b2f-4922-9084-61e4e21a1784

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) {o κ : ℕ} :
    ∀ Θ : DiffOp k r Wp Wq, TermClause D fib L o κ Θ →
      ∃ Lf : FS k r nf, (∀ e ∈ Lf, Good L e ∧ e.1.q.totalDegree ≤ κ ∧ e.2.length + fo e.1.es ≤ o) ∧
        (∀ T ∈ Θ, ∃ e ∈ Lf, e.2 = T.word) ∧
        ∀ (H : Mat k r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL D L, opApply Θ H g = shape D fib H Lf g := by
  intro Θ hΘ
  induction Θ with
  | nil => exact ⟨[], by simp, by simp, fun H g _ => by simp [opApply, shape]⟩
  | cons T Θ ih =>
    obtain ⟨Lf, h1, h2, h3⟩ := ih (fun T' hT' => hΘ T' (List.mem_cons_of_mem _ hT'))
    obtain ⟨P, a, b, c, es, ⟨q, hqdeg, hq⟩, hab, hlen, hes, hcoef⟩ := hΘ T (by simp)
    refine ⟨((⟨q, a, b, c, es⟩ : CT k r nf), T.word) :: Lf, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · refine ⟨?_, hqdeg, hlen⟩
        unfold Good
        refine ⟨?_, hes, T.word_lie⟩
        intro l hl
        by_contra hcon
        push_neg at hcon
        obtain ⟨ha, hb⟩ := hab l hcon.1 hcon.2
        rcases hl with hl | hl
        · exact hl ha
        · exact hl hb
      · exact h1 e' he'
    · intro T' hT'
      rcases List.mem_cons.1 hT' with rfl | hT'
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨e', he', h⟩ := h2 T' hT'
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · intro H g hg
      have h3' := h3 H g hg
      simp only [opApply, shape, List.map_cons, List.sum_cons] at h3' ⊢
      rw [h3', hcoef g hg]
      congr 1
      simp only [cv, cvs]
      rw [hq g]
      rfl
end Formalism.FourierDecayAlt.P.MinorPolynomials
