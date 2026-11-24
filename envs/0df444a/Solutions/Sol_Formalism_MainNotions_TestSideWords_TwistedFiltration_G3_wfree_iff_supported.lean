-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.wfree_iff_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:32.476267+00:00
-- url     : https://prove2.me/submissions/ab414641-1e49-4e69-a51f-560ee7723ab4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported

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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution {B : Type*} [CommRing B] (w : Set ι) (P : MvPolynomial (ι × Fin n) B) :
    WFree w P ↔ P ∈ supported B {v : ι × Fin n | v.1 ∉ w} := by
  classical
  rw [mem_supported]
  constructor
  · intro h v hv
    rw [Finset.mem_coe, mem_vars] at hv
    obtain ⟨d, hd, hvd⟩ := hv
    have h1 := h d hd
    intro hw
    have : (d.filter (fun v => v.1 ∈ w)) v = 0 := by rw [h1]; rfl
    rw [Finsupp.filter_apply, if_pos hw] at this
    exact (Finsupp.mem_support_iff.1 hvd) this
  · intro h ν hν
    ext x
    rw [Finsupp.filter_apply]
    split_ifs with hx
    · by_contra hne
      have hv : x ∈ (P.vars : Set (ι × Fin n)) := by
        rw [Finset.mem_coe, mem_vars]
        exact ⟨ν, hν, Finsupp.mem_support_iff.2 hne⟩
      exact (h hv) hx
    · rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
