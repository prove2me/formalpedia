-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.img_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:38.902203+00:00
-- url     : https://prove2.me/submissions/99215229-2dc5-478d-b068-4ddfb8f749fd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.StarEntryOperators
theorem _root_.solution [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (t : TpV ν r1) :
    (∑ x, MvPolynomial.C (Amat TT ξ (Sum.inl t) x) * MvPolynomial.X x :
      MvPolynomial (ZV ν r0 r1) K) = if t.1 ∈ TT then topForm ξ t else 0 := by
  obtain ⟨s, b⟩ := t
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · rw [Fintype.sum_prod_type]
    have : ∀ a : Fin r0, (∑ b' : Fin r1, MvPolynomial.C (Amat TT ξ (Sum.inl (s, b)) (s, a, b')) *
        MvPolynomial.X (s, a, b') : MvPolynomial (ZV ν r0 r1) K) =
        if s ∈ TT then MvPolynomial.C (ξ s a) * MvPolynomial.X (s, a, b) else 0 := by
      intro a
      rw [Finset.sum_eq_single b]
      · simp only [Amat, if_true]
        split_ifs <;> simp
      · intro b' _ hb'
        simp [Amat, Ne.symm hb']
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [this, topForm]
    split_ifs <;> simp
  · intro s' _ hs'
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Amat, Ne.symm hs']
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
