-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_core_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:35.718041+00:00
-- url     : https://prove2.me/submissions/f9e8e936-5e12-4a97-aacc-4bfae264b08a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_not
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_not
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_prod_split
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sum_choices
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_laplace_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (S D : Finset ℤ) (hD : D ⊆ S)
    (J K : ℤ → Finset (Fin n)) (a : ↥D → Fin n) :
    ∑ m : ↥D → Fin n, (if ∀ c : ↥D, m c ∉ K c.1 then
        (∏ c : ↥D, ((qs_sg (K c.1) (m c) : ℤ) : R)) * (∏ c ∈ S, qs_mn g (J c) (qs_add D K m c)) *
          ∏ c : ↥D, g' (m c) (a c) else 0) =
      if ∀ c : ↥D, a c ∈ J c.1 then
        (∏ c : ↥D, ((qs_sg ((J c.1).erase (a c)) (a c) : ℤ) : R)) * ∏ c ∈ S, qs_mn g (qs_rem D J a c) (K c)
      else 0 := by
  rw [qs_sum_choices S D hD (fun c => qs_mn g (J c) (K c)) (fun c x => x ∉ K c.1)
    (fun c x => ((qs_sg (K c.1) x : ℤ) : R)) (fun c x => qs_mn g (J c.1) (insert x (K c.1)))
    (fun m c => qs_mn g (J c) (qs_add D K m c))
    (fun m c hc => by rw [qs_add_not _ _ _ (Finset.mem_sdiff.1 hc).2]) (fun m c => by rw [qs_add_mem])
    (fun c x => g' x (a c))]
  rw [Finset.prod_congr rfl (fun c _ => qs_laplace_inv g g' hg (J c.1) (K c.1) (a c)), Fintype.prod_ite_zero]
  split_ifs with h
  · have e1 : ∏ c ∈ S \ D, qs_mn g (qs_rem D J a c) (K c) = ∏ c ∈ S \ D, qs_mn g (J c) (K c) :=
      Finset.prod_congr rfl (fun c hc => by rw [qs_rem_not _ _ _ (Finset.mem_sdiff.1 hc).2])
    have e2 : ∏ c : ↥D, qs_mn g (qs_rem D J a c.1) (K c.1) = ∏ c : ↥D, qs_mn g ((J c.1).erase (a c)) (K c.1) :=
      Finset.prod_congr rfl (fun c _ => by rw [qs_rem_mem])
    rw [qs_prod_split S D hD (fun c => qs_mn g (qs_rem D J a c) (K c)), e1, e2, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
