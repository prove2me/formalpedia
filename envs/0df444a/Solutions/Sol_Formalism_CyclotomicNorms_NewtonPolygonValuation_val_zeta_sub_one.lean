-- Prove2me | solution 1 for Formalism.CyclotomicNorms.NewtonPolygonValuation.val_zeta_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:44.313369+00:00
-- url     : https://prove2.me/submissions/0dafbbd2-7aca-4205-a81b-47e71e0d0b91

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton
import Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_prod
import Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.NewtonPolygonValuation
variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))
namespace Formalism.CyclotomicNorms.NewtonPolygonValuation
theorem _root_.solution {ℓ j : ℕ} (hℓ : ℓ.Prime) (hj : 1 ≤ j) (hv : v (ℓ : L) = wt 1) {z : L}
    (hz : IsPrimitiveRoot z (ℓ ^ j)) :
    v (z - 1) = wt (1 / ((ℓ ^ j).totient : ℝ)) := by
  classical
  have := Fact.mk hℓ
  have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
  have : NeZero (ℓ ^ j) := ⟨hpos.ne'⟩
  have heq : ∀ μ ∈ primitiveRoots (ℓ ^ j) L, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    rw [mem_primitiveRoots hpos] at hμ
    rw [AddValuation.map_sub_swap]
    apply le_antisymm
    · obtain ⟨i, -, hi⟩ := hμ.eq_pow_of_pow_eq_one hz.pow_eq_one
      rw [← hi]
      exact val_sub_one_le v hpos hμ.pow_eq_one i
    · obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hμ.pow_eq_one
      rw [← hi]
      exact val_sub_one_le v hpos hz.pow_eq_one i
  have hcyc := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hz)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [eval_one_cyclotomic_prime_pow, eval_prod] at hcyc
  simp only [eval_sub, eval_X, eval_C] at hcyc
  have h2 := congrArg v hcyc
  rw [hv, val_prod, sum_congr rfl heq, sum_const, hz.card_primitiveRoots] at h2
  have hne1 : z ≠ 1 := hz.ne_one (Nat.one_lt_pow (by omega) hℓ.one_lt)
  have hne : v (z - 1) ≠ ⊤ := (AddValuation.ne_top_iff v).2 (sub_ne_zero.2 hne1)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr] at h2 ⊢
  rw [← WithTop.coe_nsmul] at h2
  have h3 : (1 : ℝ) = ((ℓ ^ (k + 1)).totient : ℝ) * r := by
    have := WithTop.coe_injective h2
    rw [nsmul_eq_mul] at this
    exact this
  have hφ : (0 : ℝ) < ((ℓ ^ (k + 1)).totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 hpos
  congr 1
  field_simp
  linarith
end Formalism.CyclotomicNorms.NewtonPolygonValuation
