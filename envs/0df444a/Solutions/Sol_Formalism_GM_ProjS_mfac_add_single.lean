-- Prove2me | solution 1 for Formalism.GM.ProjS.mfac_add_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:44.575171+00:00
-- url     : https://prove2.me/submissions/327430f6-780b-434c-b2e2-5180eb10d3a4

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution (m : σ →₀ ℕ) (v : σ) :
    (mfac (m + Finsupp.single v 1) : k) = mfac m * ((m v : k) + 1) := by
  classical
  have key : ∀ n : σ →₀ ℕ, n.support ⊆ insert v m.support →
      (mfac n : k) = ∏ a ∈ insert v m.support, ((n a).factorial : k) := by
    intro n hn
    unfold mfac
    exact Finsupp.prod_of_support_subset n hn (fun _ j => (j.factorial : k)) (fun _ _ => by simp)
  have hsub : (m + Finsupp.single v 1).support ⊆ insert v m.support := by
    intro a ha
    rw [Finsupp.mem_support_iff] at ha
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hav : a = v
    · exact Or.inl hav
    · right
      simpa [Finsupp.single_apply, Ne.symm hav] using ha
  have hv : v ∈ insert v m.support := Finset.mem_insert_self v _
  have hrest : ∏ a ∈ (insert v m.support).erase v, (((m + Finsupp.single v 1 : σ →₀ ℕ) a).factorial : k)
      = ∏ a ∈ (insert v m.support).erase v, ((m a).factorial : k) := by
    refine Finset.prod_congr rfl (fun a ha => ?_)
    have hav : a ≠ v := Finset.ne_of_mem_erase ha
    simp [Ne.symm hav]
  rw [key _ hsub, key m (Finset.subset_insert v m.support),
    ← Finset.mul_prod_erase (insert v m.support) (fun a => (((m + Finsupp.single v 1 : σ →₀ ℕ) a).factorial : k)) hv,
    ← Finset.mul_prod_erase (insert v m.support) (fun a => ((m a).factorial : k)) hv, hrest]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring
end Formalism.GM.ProjS
