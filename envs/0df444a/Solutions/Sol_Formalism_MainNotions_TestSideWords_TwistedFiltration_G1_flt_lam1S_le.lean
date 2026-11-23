-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lam1S_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:18.481834+00:00
-- url     : https://prove2.me/submissions/80a59291-c3ae-4e29-98bd-33b1a1877a9b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_L_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lift_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_mem_sDegs

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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (M : ℤ) :
    lam1S LL S G ≤ (M : WithBot ℤ) ↔ twistSub LL S (0 : Fin n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-M) := by
  unfold lam1S
  rw [Finset.sup_le_iff, flt_lift_mem]
  constructor
  · intro h m
    rw [flt_L_mem]
    intro k hk
    have := WithBot.coe_le_coe.1 (h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩))
    simp only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff]
    exact this
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    have := (flt_L_mem.1 (h m)) k hm
    simp only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff] at this
    exact WithBot.coe_le_coe.2 this
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
