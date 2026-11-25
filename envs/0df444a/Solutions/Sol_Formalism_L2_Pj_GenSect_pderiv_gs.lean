-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.pderiv_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:45:17.330777+00:00
-- url     : https://prove2.me/submissions/d7a82e7c-9e53-4c6a-bb99-507f474fcaf3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_pderiv_xv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p})
    (p : Fin (D + 1) × Fin m) :
    pderiv q (gs x j₀ p) = (if p = q.1 then 1 else 0) -
      if Zs j₀ p ∧ p.1 = q.1.1 then C (rr x j₀ q.1.2) else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [gs, if_pos hp, if_neg hne, zero_sub, map_neg]
    congr 1
    simp only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, smul_eq_mul, pderiv_xv, mul_zero, zero_add]
    rw [Finset.sum_eq_single q.1.2]
    · by_cases h1 : p.1 = q.1.1
      · have e : (p.1, q.1.2) = q.1 := Prod.ext h1 rfl
        rw [if_pos e, if_pos ⟨hp, h1⟩, mul_one]
      · have e : (p.1, q.1.2) ≠ q.1 := fun h => h1 (by have h' := congrArg Prod.fst h; exact h')
        have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => h1 h.2
        rw [if_neg e, if_neg hn, mul_zero]
    · intro k _ hk
      have e : (p.1, k) ≠ q.1 := fun h => hk (congrArg Prod.snd h)
      rw [if_neg e, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => hp h.1
    rw [gs, if_neg hp, pderiv_xv, if_neg hn, sub_zero]
end Formalism.L2.Pj.GenSect
