-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.compFS_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:43.091434+00:00
-- url     : https://prove2.me/submissions/6b2dd3ed-3fad-423a-9720-00a6fd7fdbfe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_bound_steps
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_good_steps


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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {o₁ κ₁ o₂ κ₂ : ℕ}
    {L₁ L₂ : FS k r nf}
    (h₁ : ∀ e ∈ L₁, Good L e ∧ e.1.q.totalDegree ≤ κ₁ ∧ e.2.length + fo e.1.es ≤ o₁)
    (h₂ : ∀ e ∈ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₂ ∧ e.2.length + fo e.1.es ≤ o₂) :
    ∀ e ∈ compFS D L₁ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₁ + κ₂ + (2 * r + 2) * o₁ ∧
      e.2.length + fo e.1.es ≤ o₁ + o₂ := by
  intro e he
  simp only [compFS, List.mem_flatMap, List.mem_map] at he
  obtain ⟨e₁, he₁, e', he', rfl⟩ := he
  obtain ⟨hG₁, hq₁, ho₁⟩ := h₁ e₁ he₁
  obtain ⟨hG₁a, hG₁b, hG₁c⟩ := hG₁
  have hG' := (good_steps D e₁.2 hG₁c L₂ (fun e he => (h₂ e he).1) e' he').1
  obtain ⟨hG'a, hG'b, hG'c⟩ := hG'
  obtain ⟨e₂, he₂, hdeg, hlen⟩ := bound_steps D e₁.2 L₂ e' he'
  obtain ⟨-, hq₂, ho₂⟩ := h₂ e₂ he₂
  have hfo : ∀ (l₁ l₂ : List (Fin nf × List (Mat k r))), fo (l₁ ++ l₂) = fo l₁ + fo l₂ := by
    intro l₁ l₂
    simp [fo, List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold Good
    refine ⟨?_, ?_, hG'c⟩
    · intro l hl
      simp only [mulCT, Pi.add_apply] at hl
      by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
      · exact hG₁a l h1
      · apply hG'a l
        push_neg at h1
        rcases hl with hl | hl
        · left; omega
        · right; omega
    · intro x hx Y hY
      simp only [mulCT, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hG₁b x hx Y hY
      · exact hG'b x hx Y hY
  · simp only [mulCT]
    have hmul := MvPolynomial.totalDegree_mul e₁.1.q e'.1.q
    have hw : e₁.2.length ≤ o₁ := by omega
    have := Nat.mul_le_mul_left (2 * r + 2) hw
    omega
  · simp only [mulCT]
    rw [hfo]
    omega
end Formalism.FourierDecayAlt.P.MinorPolynomials
