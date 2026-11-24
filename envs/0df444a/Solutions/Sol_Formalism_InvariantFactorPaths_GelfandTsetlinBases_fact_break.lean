-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.fact_break
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:19.068266+00:00
-- url     : https://prove2.me/submissions/a22620b4-5ed3-4f64-acf2-e1f9e20037e8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_exists_bounds
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_brk_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_semi_colT
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_colT_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_det_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_path_basis_lemma


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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open SignTwistStarLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : FactBrk := by
  intro k _ n μ _
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := exists_bounds μ
  have hA := path_basis_lemma k n (hi - lo).toNat
  let e : {I : ℤ → Finset (Fin n) // IsStd μ I} →
      {T : Fin (hi - lo).toNat → Finset (Fin n) // SemiStd T} :=
    fun I => ⟨colT lo (hi - lo).toNat I.1, semi_colT I.2 lo _⟩
  have he : Function.Injective e := by
    intro I I' h
    exact Subtype.ext (colT_inj hlo hhi hb I.2.1 I'.2.1 (congrArg Subtype.val h))
  have h1 := hA.comp e he
  let φ : MvPolynomial (Fin n × Fin n) k →ₗ[k] GenField k n :=
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin n × Fin n) k) (GenField k n)).toLinearMap
  have hφ : LinearMap.ker φ = ⊥ := LinearMap.ker_eq_bot.2 (by
    intro a b h
    exact IsFractionRing.injective (MvPolynomial (Fin n × Fin n) k) (GenField k n) h)
  have h2 := h1.map' φ hφ
  set D : GenField k n :=
    ∏ c ∈ Finset.Ioc lo hi, if 1 ≤ c then (1 : GenField k n) else ((genMat k n).det)⁻¹ with hD
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro c _
    split_ifs
    · exact one_ne_zero
    · exact inv_ne_zero (genMat_det_ne k n)
  have h3 := h2.map' (LinearMap.mulLeft k D) (LinearMap.ker_eq_bot.2 (fun a b h => mul_left_cancel₀ hD0 h))
  have h4 := h3.units_smul (fun I => ∏ c ∈ Finset.Ioc lo hi, sgnU k μ I.1 c)
  have h5 : (fun I : {I : ℤ → Finset (Fin n) // IsStd μ I} => brk (genMat k n) (genMat k n)⁻¹ μ I.1) =
      (fun I : {I : ℤ → Finset (Fin n) // IsStd μ I} => ∏ c ∈ Finset.Ioc lo hi, sgnU k μ I.1 c) •
        (⇑(LinearMap.mulLeft k D) ∘ ⇑φ ∘ (fun T : {T : Fin (hi - lo).toNat → Finset (Fin n) // SemiStd T} =>
          tabMinors k T.1) ∘ e) := by
    funext I
    exact brk_eq hlo hhi hb I.2.1
  rw [h5]
  exact h4
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
