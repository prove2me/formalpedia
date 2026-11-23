-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_mem_sDegs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:37.047828+00:00
-- url     : https://prove2.me/submissions/384672eb-14ce-4f16-9e79-ff09c423eceb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration

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
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∈ sDegs LL S j G ↔ ∃ m, ((twistSub LL S j G).coeff m).coeff k ≠ 0 := by
  classical
  unfold sDegs
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨m, -, hk⟩
    exact ⟨m, Finsupp.mem_support_iff.1 hk⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h]
    rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
