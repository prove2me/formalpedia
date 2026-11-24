-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_fill_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:48.118171+00:00
-- url     : https://prove2.me/submissions/958ee808-459a-48d3-9707-2af92025cdd9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_nu_cast
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_nu_antitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_g_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_lt_colH
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
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hint : Formalism.GradedWeylDivisibility.Interlaced m) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) :
    ∃ I : TIdx mu, ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
  have hf : ∀ c : ↥(TCols mu), StrictMono fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
    intro c q q' hqq
    have hc := Finset.mem_Ioc.mp c.2
    rw [Fin.lt_def] at hqq
    refine qa_g_lt m hint (qa_nu mu) (qa_nu_antitone hmu) hcol _ (by omega) (q'.val - q.val - 1) _ _ ?_ ?_
    · simp only [Fin.val_castLE]; omega
    · rw [qa_nu_cast hmu]
      have := (qa_lt_colH hmu c (Fin.castLE (colH_le mu c) q')).mp q'.2
      omega
  refine ⟨fun c => ⟨univ.map ⟨_, (hf c).injective⟩, by simp⟩, fun c q => ?_⟩
  have := Finset.orderEmbOfFin_unique (s := univ.map ⟨_, (hf c).injective⟩) (by simp) (f := fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) (by simp) (hf c)
  exact (congrFun this q).symm
end Formalism.InvariantFactorPaths.ColumnFamilies
