-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:45.951722+00:00
-- url     : https://prove2.me/submissions/d19cad30-5d72-4449-9e29-c1efbeb909c6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_g_step
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (ν : Fin n → ℕ)
    (hν : Antitone ν) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = ν t) (k : ℤ) (hk1 : 1 ≤ k) :
    ∀ (d : ℕ) (p p' : Fin n), p'.val = p.val + d + 1 → k ≤ ν p' → qa_g m k p < qa_g m k p' := by
  intro d
  induction d with
  | zero =>
    intro p p' hpp hk
    have h1 : ν p' ≤ ν p := hν (by rw [Fin.le_def]; omega)
    exact qa_g_step m hint k hk1 p p' (by omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)
  | succ d ih =>
    intro p p' hpp hk
    have hlt : p.val + d + 1 < n := by have := p'.2; omega
    have h1 : ν p' ≤ ν ⟨p.val + d + 1, hlt⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    refine (ih p ⟨p.val + d + 1, hlt⟩ rfl (by omega)).trans ?_
    exact qa_g_step m hint k hk1 _ p' (by simp only; omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)
end Formalism.InvariantFactorPaths.ColumnFamilies
