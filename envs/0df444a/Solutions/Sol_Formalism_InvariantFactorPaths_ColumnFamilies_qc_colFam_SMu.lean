-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_colFam_SMu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:04.942871+00:00
-- url     : https://prove2.me/submissions/3d9e6c79-20af-4378-8d6a-a20ff38d0d8a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_prim
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_card_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_equiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) :
    Nonempty (ColFam M) := by
  classical
  have hex : ∀ I : TIdx mu, ∃ c : M.ι → ℤ, ∑ i, c i • β i = brk mu I := fun I =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (by rw [hβ.2.1]; exact Submodule.subset_span ⟨I, rfl⟩)
  choose c hc using hex
  let ph : Matrix M.ι (TIdx mu) ℤ := fun i I => c I i
  have hph : ∀ I, ∑ i, ph i I • β i = brk mu I := hc
  have hpr := qc_prim hS hmu hβ ph hph
  refine ⟨{ J := Unit, mu := fun _ => mu, dom := fun _ => hmu, ph := fun _ => ph,
            equiv := fun _ => qc_equiv hA hS hmu hβ ph hph, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro p hp nu
    have := Fact.mk hp
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    have h1 := hpr (p : ℤ) fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h0 i)
    have h2 : p ∣ 1 := by exact_mod_cast h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  · intro nu
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    have h1 := hpr 0 fun i => by
      have := congrFun h0 i
      simp only [Pi.zero_apply, Int.cast_eq_zero] at this
      rw [this]
    simp at h1
  · simp [qc_card_eq hS hmu hβ]
end Formalism.InvariantFactorPaths.ColumnFamilies
