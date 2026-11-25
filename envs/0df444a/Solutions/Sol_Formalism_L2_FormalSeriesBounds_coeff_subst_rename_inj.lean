-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_subst_rename_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:14.474952+00:00
-- url     : https://prove2.me/submissions/0f572a28-30a3-4645-badc-35581e15632c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_prod_X_rename
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ τ : Type} [Finite σ] (φ : σ → τ) (hφ : Function.Injective φ)
    (F : MvPowerSeries σ C) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e.mapDomain φ)
      (MvPowerSeries.subst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) F) = MvPowerSeries.coeff e F := by
  have hA : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)
  rw [MvPowerSeries.coeff_subst hA, finsum_eq_single _ e]
  · rw [prod_X_rename, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    intro h
    exact hd (Finsupp.mapDomain_injective hφ h).symm
end Formalism.L2.FormalSeriesBounds
