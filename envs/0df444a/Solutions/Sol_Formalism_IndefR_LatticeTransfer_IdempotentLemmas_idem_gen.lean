-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.idem_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:04.080805+00:00
-- url     : https://prove2.me/submissions/4eec7514-5a46-4573-8312-fa996776f20c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.IndefR.LatticeTransfer.IdempotentLemmas
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {H : Type} [Group H] {_ : Fintype H}
    (a : H → K) (ha : ∀ h k, a h * a k = a (h * k)) (π : H →* Module.End K V)
    (hn : (Nat.card H : K) ≠ 0) :
    ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) * ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) =
      (Nat.card H : K)⁻¹ • ∑ h : H, a h • π h := by
  have key : (∑ h : H, a h • π h) * (∑ h : H, a h • π h) = (Nat.card H : K) • ∑ h : H, a h • π h := by
    rw [Finset.sum_mul]
    have e0 : ∀ h : H, (a h • π h) * ∑ k : H, a k • π k = ∑ m : H, a m • π m := by
      intro h
      rw [Finset.mul_sum]
      have e : ∀ k : H, (a h • π h) * (a k • π k) = a (h * k) • π (h * k) := by
        intro k
        rw [smul_mul_smul_comm, ha, map_mul]
      simp_rw [e]
      exact Equiv.sum_comp (Equiv.mulLeft h) (fun m => a m • π m)
    simp_rw [e0]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card]
  rw [smul_mul_smul_comm, key, smul_smul]
  congr 1
  field_simp
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
