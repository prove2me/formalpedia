-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_le_valS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:11.572846+00:00
-- url     : https://prove2.me/submissions/943af5cc-29ea-4abc-9425-6f7301efdac3

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
    (G : MvPolynomial (ι × Fin n) R) (t : ℤ) :
    (t : WithTop ℤ) ≤ valS LL S G ↔ twistSub LL S (lastIdx n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F t := by
  unfold valS
  rw [Finset.le_inf_iff, flt_lift_mem]
  constructor
  · intro h m
    rw [flt_L_mem]
    intro k hk
    have := h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)
    simp only [AddMonoidHom.zero_apply, sub_zero, one_mul]
    exact WithTop.coe_le_coe.1 this
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    have := (flt_L_mem.1 (h m)) k hm
    simp only [AddMonoidHom.zero_apply, sub_zero, one_mul] at this
    exact WithTop.coe_le_coe.2 this
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
