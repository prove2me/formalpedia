-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.quantumDet_neg_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:15.548835+00:00
-- url     : https://prove2.me/submissions/9bb98a13-7455-40c2-b1de-a86eaeb77a84

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_antisymmetrizedProduct_perm_invariant
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_antisymmetrizedProduct_eq_factorial_smul_qdet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_antisymmetrizedProduct_neg_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (x : ℂ) :
    qdet (fun a b => -E b a) x = ((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x) := by
  have hE' : GlRel (fun a b => -E b a) := by
    intro a b c d
    have h := hE b a d c
    simp only [neg_mul_neg]
    rw [h]
    by_cases h1 : a = d <;> by_cases h2 : c = b
    · subst h1 h2
      simp
      abel
    · subst h1
      simp [h2, Ne.symm h2]
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have h1 := antisymmetrizedProduct_eq_factorial_smul_qdet (fun a b => -E b a) hE' x
  have h2 := antisymmetrizedProduct_neg_transpose E (fun k => x - (k : ℂ))
  have h3 : (fun k : Fin n => -(x - (k : ℂ))) = (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ)) ∘ Fin.revPerm := by
    funext k
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [Nat.cast_sub (Nat.succ_le_of_lt k.isLt)]
    push_cast
    ring
  have h4 := antisymmetrizedProduct_perm_invariant E Fin.revPerm (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ))
  have h5 := antisymmetrizedProduct_eq_factorial_smul_qdet E hE ((n : ℂ) - 1 - x)
  refine smul_right_injective A (by exact_mod_cast n.factorial_ne_zero : ((n.factorial : ℕ) : ℂ) ≠ 0) ?_
  show ((n.factorial : ℕ) : ℂ) • qdet (fun a b => -E b a) x = ((n.factorial : ℕ) : ℂ) • (((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x))
  rw [← h1, h2, h3, h4, h5, smul_comm, Algebra.smul_def ((-1 : ℂ) ^ n)]
  simp
end Formalism.HermitianLatticeCounting.P
