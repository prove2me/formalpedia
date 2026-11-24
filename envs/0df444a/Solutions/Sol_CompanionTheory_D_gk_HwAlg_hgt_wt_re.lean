-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.hgt_wt_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:53.249802+00:00
-- url     : https://prove2.me/submissions/6954dbd1-c148-4abd-8efa-fdb89dac3494

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons

set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Qr
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.HwAlg
variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}
variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}
namespace CompanionTheory.D.gk.HwAlg
theorem _root_.solution (ν : Fin n → ℂ) :
    ∀ l : List (Fin n × Fin n), Lower l → (hgt (wt ν l)).re ≤ (hgt ν).re - l.length := by
  intro l
  induction l with
  | nil => intro; simp [wt]
  | cons p l ih =>
    intro hl
    have hl' : Lower l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp : p.2 < p.1 := hl p (by simp)
    have hsum : hgt (wt ν (p :: l)) = hgt (wt ν l) + (((p.2 : ℕ) : ℂ) - ((p.1 : ℕ) : ℂ)) := by
      simp only [hgt, wt, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [hsum, Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.natCast_re]
    have : ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp
    have := ih hl'
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith
end CompanionTheory.D.gk.HwAlg
