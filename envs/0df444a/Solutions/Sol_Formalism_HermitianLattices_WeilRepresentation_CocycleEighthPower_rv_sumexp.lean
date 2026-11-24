-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower.rv_sumexp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:48.128587+00:00
-- url     : https://prove2.me/submissions/79e9ea7c-4984-4620-aa7f-ff2f94be0ebd

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
theorem _root_.solution : SumExpansion := by
  intro M Q _ _ φ hadd k
  have h00 : ∀ b, cob φ 0 b = 0 := by
    intro b; have := hadd 0 0 b; simpa using this
  have hφ0 : φ 0 = 0 := by
    have := h00 0; simpa [cob] using this
  have hsum : ∀ (n : ℕ) (c : Fin n → M) (b : M), cob φ (∑ j, c j) b = ∑ j, cob φ (c j) b := by
    intro n
    induction n with
    | zero => intro c b; simp [h00]
    | succ n ih => intro c b; rw [Fin.sum_univ_castSucc, hadd, ih, Fin.sum_univ_castSucc]
  induction k with
  | zero => intro a; simp [hφ0]
  | succ k ih =>
    intro a
    have e1 : φ (∑ j, a j) = φ (∑ j : Fin k, a j.castSucc) + φ (a (Fin.last k)) +
        ∑ j : Fin k, cob φ (a j.castSucc) (a (Fin.last k)) := by
      rw [Fin.sum_univ_castSucc, ← hsum]; simp [cob]
    rw [e1, ih (fun j => a j.castSucc)]
    simp only [Finset.sum_filter]
    rw [Fin.sum_univ_castSucc (f := fun j => φ (a j)),
      Fin.sum_univ_castSucc (f := fun j => ∑ j', if j < j' then cob φ (a j) (a j') else 0)]
    simp only [Fin.sum_univ_castSucc (n := k), Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
      if_true, Finset.sum_add_distrib]
    have : ∀ j : Fin k, ¬ (Fin.last k < j.castSucc) := fun j => by
      simp [Fin.le_last]
    simp [this]
    abel
end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
