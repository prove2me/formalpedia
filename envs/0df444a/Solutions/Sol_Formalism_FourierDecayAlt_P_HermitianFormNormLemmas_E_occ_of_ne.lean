-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.occ_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:23.148808+00:00
-- url     : https://prove2.me/submissions/1a8e448b-3574-4177-9020-1cadc4cffdfd

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
theorem _root_.solution {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
    {E : Type} [Field E] {r : ℕ} {Cl Nu : Type} (N : NGData τ E r Cl Nu) (c : Cl) (γ : Pts E r) (ν : Nu)
    (h : grp X N c γ ν ≠ 0) : Occ X N c γ ν := by
  by_contra hno
  apply h
  have hz : ∀ t, (X.ngSet ∩ {t | N.cls t = c ∧ N.pt t = γ ∧ N.nml t = ν}).indicator X.vec t = 0 := by
    intro t
    by_cases ht : t ∈ X.ngSet ∩ {t | N.cls t = c ∧ N.pt t = γ ∧ N.nml t = ν}
    · rw [Set.indicator_of_mem ht]
      by_contra hv
      exact hno ⟨t, ht.1, hv, ht.2.1, ht.2.2.1, ht.2.2.2⟩
    · simp [Set.indicator_apply, ht]
  unfold Formalism.FourierDecayAlt.PN.grp
  simp only [hz, tsum_zero]
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
