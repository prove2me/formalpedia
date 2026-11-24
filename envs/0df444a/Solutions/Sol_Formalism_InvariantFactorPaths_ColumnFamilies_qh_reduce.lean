-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:19.801798+00:00
-- url     : https://prove2.me/submissions/5ecd7ce4-f8ef-4ab0-9016-ef1a46b09903

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_InducedSectionsSpanStatement
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qhDet_val
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_det_zpow_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mem_dualWeyl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mul_mem


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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [IsDomain R] (mu : Fin n → ℤ) (f : GLCoord R n) (hf : f ∈ inducedSections R mu) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin n × Fin n) R), (∀ a, 0 ≤ mu a + k) ∧
      f = ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
        algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∧
      Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n (fun a => (mu a + k).toNat) := by
  obtain ⟨N, P, hNP⟩ := IsLocalization.Away.surj (genMat R n).det f
  have hk : ∀ a, 0 ≤ mu a + ((N + (Finset.univ.sup fun b => (-mu b).toNat) : ℕ) : ℤ) := by
    intro a
    have h1 := Int.self_le_toNat (-mu a)
    have h2 : (-mu a).toNat ≤ Finset.univ.sup fun b => (-mu b).toNat :=
      Finset.le_sup (f := fun b => (-mu b).toNat) (Finset.mem_univ a)
    push_cast
    omega
  set M : ℕ := Finset.univ.sup fun b => (-mu b).toNat with hM
  have hswap : rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M)) = P * (genMat R n).det ^ M := by
    rw [rename_rename, Prod.swap_swap_eq, rename_id_apply]
  have hmain : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) =
      f * algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [hswap, map_mul, map_pow, pow_add, ← mul_assoc, hNP]
  have hunit : ((qhDet R n ^ ((N + M : ℕ) : ℤ) : (GLCoord R n)ˣ) : GLCoord R n) =
      algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, qhDet_val]
  refine ⟨N + M, rename Prod.swap (P * (genMat R n).det ^ M), hk, ?_, ?_⟩
  · rw [hmain, ← hunit, mul_comm f, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_mul]
  · have hmem : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) ∈
        inducedSections R (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) := by
      rw [hmain, mul_comm, ← hunit]
      have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) ((N + M : ℕ) : ℤ)) hf
      have e : (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) = (fun _ : Fin n => ((N + M : ℕ) : ℤ)) + mu := by
        funext a
        rw [Pi.add_apply, Int.toNat_of_nonneg (hk a), add_comm]
      rw [e]
      exact h
    exact qh_mem_dualWeyl _ _ hmem
end Formalism.InvariantFactorPaths.ColumnFamilies
