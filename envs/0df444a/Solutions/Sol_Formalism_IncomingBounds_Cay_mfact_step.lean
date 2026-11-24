-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.mfact_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:05.853135+00:00
-- url     : https://prove2.me/submissions/366c486d-0b3a-4feb-acb6-081c1e03e593

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {σ : Type} (b : σ →₀ ℕ) (x : σ) (hx : 0 < b x) :
    mfact b = b x * mfact (b - Finsupp.single x 1) := by
  classical
  have hxs : x ∈ b.support := Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hx)
  have hsub : (b - Finsupp.single x 1).support ⊆ b.support := by
    intro y hy
    rw [Finsupp.mem_support_iff] at hy ⊢
    intro hb
    apply hy
    rw [Finsupp.tsub_apply, hb, Nat.zero_sub]
  have key : ∀ e : σ →₀ ℕ, e.support ⊆ b.support →
      Formalism.IncomingBounds.mfact e = ∏ y ∈ b.support, (e y).factorial :=
    fun e he => Finsupp.prod_of_support_subset e he (fun _ k => k.factorial)
      (fun _ _ => Nat.factorial_zero)
  rw [key b (Finset.Subset.refl _), key _ hsub, ← Finset.mul_prod_erase _ _ hxs,
    ← Finset.mul_prod_erase _ _ hxs, ← mul_assoc]
  congr 1
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    exact (Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mp hx)).symm
  · refine Finset.prod_congr rfl fun y hy => ?_
    rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hy), Nat.sub_zero]
end Formalism.IncomingBounds.Cay
