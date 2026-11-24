-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.dep_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:34.249978+00:00
-- url     : https://prove2.me/submissions/9e03959e-fcac-44be-bb78-9edbbe8decd9

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
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
variable {F : Type} [Field F] [Fintype F]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) (lam : Fin m → F) (j0 : Fin m) (hj0 : lam j0 ≠ 0) :
    ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card * c ≤ c ^ m := by
  have h1 : ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card
      ≤ (Fintype.piFinset (Function.update Fs j0 {0})).card := by
    refine Finset.card_le_card_of_injOn (fun Y => Function.update Y j0 0) ?_ ?_
    · intro Y hY
      have hY' := Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).1
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro j
      by_cases hj : j = j0
      · subst hj; simp
      · simp only [Function.update_of_ne hj]; exact hY' j
    · intro Y hY Y' hY' hYY
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).2
      have e2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY')).2
      have hne : ∀ j, j ≠ j0 → Y j = Y' j := by
        intro j hj
        have := congrFun hYY j
        simpa only [Function.update_of_ne hj] using this
      have e3 : ∑ j, lam j • (Y j - Y' j) = 0 := by
        simp only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]
      rw [Finset.sum_eq_single j0 (fun j _ hj => by rw [hne j hj, sub_self, smul_zero])
        (fun h => absurd (Finset.mem_univ _) h)] at e3
      have e4 : Y j0 = Y' j0 := by
        rcases smul_eq_zero.1 e3 with h | h
        · exact absurd h hj0
        · exact sub_eq_zero.1 h
      funext j
      by_cases hj : j = j0
      · rw [hj]; exact e4
      · exact hne j hj
  have h2 : (Fintype.piFinset (Function.update Fs j0 {0})).card * c = c ^ m := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j0)]
    have h3 : ∏ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c ^ (m - 1) := by
      rw [Finset.prod_congr rfl (fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), hc] :
          ∀ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c)]
      simp
    rw [h3]
    simp only [Function.update_self, Finset.card_singleton, one_mul]
    have : 1 ≤ m := by have := j0.2; omega
    rw [← pow_succ]; congr 1; omega
  calc _ ≤ (Fintype.piFinset (Function.update Fs j0 {0})).card * c := Nat.mul_le_mul_right _ h1
    _ = _ := h2
end Formalism.HermitianLatticeCounting.P.S4aux
