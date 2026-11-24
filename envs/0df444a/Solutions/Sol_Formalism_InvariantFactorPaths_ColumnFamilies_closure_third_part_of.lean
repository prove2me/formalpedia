-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.closure_third_part_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:03.997883+00:00
-- url     : https://prove2.me/submissions/df1e4c2b-a938-4847-8114-03583332dfa3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBranching
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_prim
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_card_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_j_can_std


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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) (hS : SBasis) (hC : CntBranch) : ClosureBranching := by
  classical
  intro m _ M lam β hl hβ
  let Sg : Finset (Fin m → ℤ) :=
    (Fintype.piFinset fun a : Fin m => Finset.Icc (lam a.succ) (lam a.castSucc)).filter fun nu =>
      Dominant nu ∧ Interl lam nu
  have hSg : ∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu := by
    intro nu
    simp only [Sg, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
    rintro ⟨_, hi⟩ a
    exact ⟨(hi a).2, (hi a).1⟩
  have hex : ∀ I : TIdx lam, ∃ c : M.ι → ℤ, ∑ i, c i • β i = brk lam I := fun I =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (by rw [hβ.2.1]; exact Submodule.subset_span ⟨I, rfl⟩)
  choose c hc using hex
  let ph : Matrix M.ι (TIdx lam) ℤ := fun i I => c I i
  have hph : ∀ I, ∑ i, ph i I • β i = brk lam I := hc
  have hE := qc_equiv hA hS hl hβ ph hph
  refine ⟨Sg, fun nu i I' => ph i (qr_j ((hSg nu.1).1 nu.2).2 I'), hSg, ?_, ?_, ?_⟩
  · intro nu R _ h g1 t hb
    ext i I'
    exact qr_equiv hl ((hSg nu.1).1 nu.2).1 ((hSg nu.1).1 nu.2).2 ph hE hb i I'
  · intro nu
    have hpr := qr_prim hS hl hβ ph hph _ (qr_j_can_std (lam := lam) ((hSg nu.1).1 nu.2).2)
    constructor
    · intro p hp h0
      have h1 := hpr (p : ℤ) fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h0 i)
      have h2 : p ∣ 1 := by exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    · intro h0
      have h1 := hpr 0 fun i => by
        have := congrFun h0 i
        simp only [Pi.zero_apply, Int.cast_eq_zero] at this
        rw [this]
      simp at h1
  · rw [qc_card_eq hS hl hβ, hC m lam hl Sg hSg, Finset.sum_coe_sort Sg (fun nu => dMu nu)]
end Formalism.InvariantFactorPaths.ColumnFamilies
