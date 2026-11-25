-- Prove2me | solution 1 for CompanionTheory.FamInh.res_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:45.126889+00:00
-- url     : https://prove2.me/submissions/68974a6f-7917-4020-931e-838e35ce2adb

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA
import Theorems.Thm_CompanionTheory_FamInh_coe_res_smul
import Theorems.Thm_CompanionTheory_FamInh_val_int_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open CompanionTheory CompanionTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
omit [IsAlgClosure K Ω] [IsAlgClosure L Ω]
namespace CompanionTheory.FamInh
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)} (hw : IsPlaceOver A w) [h : w.asIdeal.LiesOver v.asIdeal]
    {σ : G K Ω} (hσ : IsFrob (F := K) A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) w.asIdeal := by
  intro x
  rw [← hw, ← h.over]
  have := hσ.2 _ (val_int_le_one A x)
  rw [← coe_res_smul, ← map_pow, ← map_sub] at this
  exact this
end CompanionTheory.FamInh
