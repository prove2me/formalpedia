-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.cnt_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:21.331407+00:00
-- url     : https://prove2.me/submissions/e5de742a-e44e-4137-8d2d-dc785f95d623

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_conj
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
open scoped Classical
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (h2 : Module.finrank K L = 2) (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K)
    (j : ℕ) (G : Matrix (Fin (j + 1)) (Fin (j + 1)) L) (hG : ∀ a b, G b a = G a b ^ Fintype.card K) :
    (univ.filter fun X : Fin (j + 1) → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card
      = ∑ X' ∈ univ.filter (fun X' : Fin j → Fin n → L => LinearIndependent L X' ∧
          ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ),
        (univ.filter fun x : Fin n → L => x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card := by
  have key : ∀ (x : Fin n → L) (X' : Fin j → Fin n → L),
      (LinearIndependent L (Fin.cons x X' : Fin (j + 1) → Fin n → L) ∧
        ∀ a b, hB K Ph ((Fin.cons x X' : Fin (j + 1) → Fin n → L) a)
          ((Fin.cons x X' : Fin (j + 1) → Fin n → L) b) = G a b) ↔
      ((LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ) ∧
        (x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0)) := by
    intro x X'
    rw [linearIndependent_finCons]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨h1, h3⟩, ⟨h4, h5⟩, h6⟩
      exact ⟨⟨h1, fun a b => (h6 a).2 b⟩, h3, h5, h4⟩
    · rintro ⟨⟨h1, h3⟩, h4, h5, h6⟩
      refine ⟨⟨h1, h4⟩, ⟨h6, h5⟩, fun a => ⟨?_, h3 a⟩⟩
      rw [← hB_conj Ph h2 hherm, h5, ← hG]
  rw [Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin n → L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun X' _ => ?_
  rw [Finset.card_filter]
  by_cases hV : LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ
  · rw [if_pos hV]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact if_congr ((key x X').trans (and_iff_right hV)) rfl rfl
  · rw [if_neg hV]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact if_neg fun h => hV ((key x X').1 h).1
end Formalism.HermitianLatticeCounting.P.S4aux
