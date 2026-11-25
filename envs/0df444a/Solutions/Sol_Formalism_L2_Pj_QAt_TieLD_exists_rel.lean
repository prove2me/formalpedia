-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLD.exists_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:50.108073+00:00
-- url     : https://prove2.me/submissions/c25ca2a7-7cd1-4e70-9f5b-ea2136de0200

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_pow_maximalIdeal_inj
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_mapLaT_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
attribute [local instance] algCT
attribute [local instance] locT
attribute [local instance] dvrT
attribute [local instance] dvrLa
attribute [local instance] algLaK
attribute [local instance] towerLaK
attribute [local instance] fracLaK
namespace Formalism.L2.Pj.QAt.TieLD
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) :
    ∃ (ϖ : Localization.AtPrime la.asIdeal) (ϖ₁ : Tw w) (u : (Tw w)ˣ), Irreducible ϖ ∧
      Irreducible ϖ₁ ∧ mapLaT la w hw ϖ = u * ϖ₁ ^ (w.asIdeal.ramificationIdx (𝓞 K)) := by
  have : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime la.asIdeal)
  obtain ⟨ϖ₁, hϖ₁⟩ := IsDiscreteValuationRing.exists_irreducible (Tw w)
  have hinj : Function.Injective (mapLaT la w hw) := by
    intro x y hxy
    have h := congrArg (fun t : Tw w => (t : K₁)) hxy
    simp only [mapLaT_coe] at h
    exact IsFractionRing.injective (Localization.AtPrime la.asIdeal) K
      ((algebraMap K K₁).injective h)
  have h0 : mapLaT la w hw ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ₁
  have hmap0 : la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot la.ne_bot
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 w.asIdeal
  generalize hc : Multiset.count w.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)))) = c
    at hfac
  have hQw : ¬ Q ≤ w.asIdeal := fun hle => by
    rw [sup_eq_left.2 hle] at hQ
    exact w.isPrime.ne_top hQ
  have h1 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) =
      IsLocalRing.maximalIdeal (Tw w) ^ c := by
    rw [hfac, Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_maximalIdeal (p := w.asIdeal) (Rₚ := Tw w),
      IsLocalization.AtPrime.map_eq_top_of_not_le (S := Tw w) hQw, Ideal.mul_top]
  have hcomp : (mapLaT la w hw).comp (algebraMap (𝓞 K) (Localization.AtPrime la.asIdeal)) =
      (algebraMap (𝓞 K₁) (Tw w)).comp (algebraMap (𝓞 K) (𝓞 K₁)) :=
    IsLocalization.map_comp _
  have h2 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) =
      Ideal.span {mapLaT la w hw ϖ} := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map,
      IsLocalization.AtPrime.map_eq_maximalIdeal (p := la.asIdeal)
        (Rₚ := Localization.AtPrime la.asIdeal),
      hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have h3 : Ideal.span {mapLaT la w hw ϖ} = IsLocalRing.maximalIdeal (Tw w) ^ n := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ₁.maximalIdeal_eq]
  have hn : n = c := pow_maximalIdeal_inj (h3.symm.trans (h2.symm.trans h1))
  have he : n = w.asIdeal.ramificationIdx (𝓞 K) := by
    rw [hn, ← hc, ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0
      w.isPrime w.ne_bot, Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]
  exact ⟨ϖ, ϖ₁, u, hϖ, hϖ₁, by rw [hu, he]⟩
end Formalism.L2.Pj.QAt.TieLD
