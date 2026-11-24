-- Prove2me | solution 1 for Formalism.REAL.HWDiag_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:06.277701+00:00
-- url     : https://prove2.me/submissions/df74d6a0-a8f0-43b0-bb01-44853b4ff33a

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Theorems.Thm_Formalism_REAL_HWDiag_covApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.REAL
private theorem epow_zero_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin n) : epow E 0 a b = if a = b then 1 else 0 := by
  first | rfl | simp [epow]
private theorem epow_succ_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (k : ℕ) (a b : Fin n) : epow E (k + 1) a b = ∑ c, epow E k a c * E c b := by
  first | rfl | simp [epow]
private theorem module_end_mul_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f g : Module.End ℂ V) (v : V) : (f * g) v = f (g v) := rfl
private theorem module_end_finset_sum_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (s : Finset ι) (f : ι → Module.End ℂ V) (v : V) : (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  first
  | exact LinearMap.sum_apply s f v
  | simp
  | (classical
     induction s using Finset.induction_on with
     | empty => simp
     | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, LinearMap.add_apply, ih])
end Formalism.REAL
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hE : GlRel E)
    (hv : IsHW E ν v) : ∀ (k : ℕ) (a b : Fin n), a < b → epow E k a b v = 0 := by
  have hv' : (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0 := hv
  intro k
  induction k with
  | zero =>
    intro a b hab
    simp [epow_zero_apply, hab.ne]
  | succ k ih =>
    intro a b hab
    rw [epow_succ_apply, module_end_finset_sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [module_end_mul_apply]
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · rw [hv'.2 c b hcb, map_zero]
    · rw [hcb, hv'.1 b, map_smul, ih a b hab, smul_zero]
    · rw [HWDiag_covApply E hE k a c c b v, ih a c (hab.trans hcb), map_zero,
        ih a b hab]
      simp [hab.ne']
end Formalism.REAL
