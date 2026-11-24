-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.aeval_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:45:55.896492+00:00
-- url     : https://prove2.me/submissions/76575015-a405-4158-9dc5-f680fa98284a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_img_inr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_img_inl

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
theorem _root_.solution [NeZero ν] {C : ℕ} (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (he : ∀ x : TpV ν r1, x.1 ∉ TT → e x = 0)
    (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) :
    MvPolynomial.aeval (fun i : TpV ν r1 ⊕ ZV ν r0 r1 =>
        (∑ x, MvPolynomial.C (Amat TT ξ i x) * MvPolynomial.X x : MvPolynomial (ZV ν r0 r1) K))
      (topMonoP (Finsupp.equivFunOnFinite.symm e) * lowPoly (lowOp l sf T I)) =
      entryOp ξ e l sf T I := by
  rw [map_mul, entryOp]
  congr 1
  · rw [topMonoP, MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [img_inl, Finsupp.equivFunOnFinite_symm_apply_apply]
    split_ifs with h
    · rfl
    · rw [he x h, pow_zero, pow_zero]
  · rw [lowPoly, MvPolynomial.aeval_rename]
    have : ((fun i : TpV ν r1 ⊕ ZV ν r0 r1 =>
        (∑ x, MvPolynomial.C (Amat TT ξ i x) * MvPolynomial.X x : MvPolynomial (ZV ν r0 r1) K)) ∘
        Sum.inr) = MvPolynomial.X := by
      funext y
      exact img_inr TT ξ y
    rw [this, MvPolynomial.aeval_X_left_apply]
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
