-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.unV_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:27.812833+00:00
-- url     : https://prove2.me/submissions/ef33284d-55e7-4045-a2e1-8dcc1a9a90d6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_dnL
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_eq_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inL_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_X_pow_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_smul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_Vpow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inL_of_rescale
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_rescale
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_lg_inj
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_smul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_repar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero


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
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {ζ : C} (hζ : IsPrimitiveRoot ζ V.l) (z : ℕ → I g ⊕ JJ I g → C) (hz : Vpow 1 z ∈ X.TySet V g) :
    z ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hz
  have hXl : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ V.l) = 0 := by simp [hl0.ne']
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hXl
  have hty : ∀ n, tyS V.l (fun s => Vpow 1 z s n) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (tyS V.l fun s => z s n) :=
    fun n => tyS_Vpow hl2 (fun s => z s n)

  have hLin : ∀ i, InL V.l (alongCv γ (X.lg i)) := by
    intro i
    rw [h1 i]
    refine InL.sum _ _ fun c _ => InL.smul ?_ _
    rw [hty]
    exact inL_subst hl0 _

  have hζX : PowerSeries.constantCoeff (ζ • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  have hγζ : (fun i => PowerSeries.subst (ζ • (PowerSeries.X : PowerSeries C)) (γ i)) = γ := by
    apply X.lg_inj hlg0 hexlg
    · intro i
      exact constantCoeff_subst_zero (σ := Unit) (fun _ => hζX) (hγ i).1
    · exact fun i => (hγ i).1
    · intro i
      rw [alongCv_repar (fun i => (hγ i).1) hζX, ← PowerSeries.rescale_eq_subst]
      exact (hLin i).rescale hζ.pow_eq_one
  have hγL : ∀ i, InL V.l (γ i) := by
    intro i
    apply inL_of_rescale hζ
    rw [PowerSeries.rescale_eq_subst]
    exact congrFun hγζ i
  have hδ : IsCv V fun i => dnL V.l (γ i) := by
    intro i
    refine ⟨?_, fun n => ?_⟩
    · show PowerSeries.constantCoeff (dnL V.l _) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_dnL, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hγ i).1
    · show V.Ge 0 (PowerSeries.coeff n (dnL V.l _))
      rw [coeff_dnL]
      exact (hγ i).2 _
  have hγδ : γ = fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (dnL V.l (γ i)) :=
    funext fun i => (hγL i).eq_subst hl0
  have hal : ∀ f : MvPowerSeries κ C, alongCv γ f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (alongCv (fun i => dnL V.l (γ i)) f) := by
    intro f
    rw [← alongCv_repar (fun i => (hδ i).1) hXl, ← hγδ]

  have hlamEq : ∀ q, lam q = tyS V.l (fun s => Vpow 1 z s (Sum.inr q)) + alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => Vpow 1 z s (Sum.inl c)) else 0) := by
    intro q
    rw [h2 q]
    abel
  have hlamL : ∀ q, InL V.l (lam q) := by
    intro q
    rw [hlamEq q]
    refine InL.sub (InL.add ?_ ?_) (InL.sum _ _ fun c _ => ?_)
    · rw [hty]; exact inL_subst hl0 _
    · rw [hal]; exact inL_subst hl0 _
    · split_ifs
      · rw [hty]; exact (inL_subst hl0 _).smul _
      · exact InL.zero
  have hlam' : IsCv V fun q => dnL V.l (lam q) := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · show PowerSeries.constantCoeff (dnL V.l _) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_dnL, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlam q).1
    · show V.Ge 0 (PowerSeries.coeff n (dnL V.l _))
      rw [coeff_dnL]
      exact (hlam q).2 _
  refine ⟨fun i => dnL V.l (γ i), fun q => dnL V.l (lam q), hδ, hlam', ?_, ?_⟩
  · intro i
    apply subst_X_pow_inj hl0
    rw [← hal, h1 i, ← PowerSeries.coe_substAlgHom hS, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, PowerSeries.coe_substAlgHom hS, hty]
  · intro q
    apply subst_X_pow_inj hl0
    rw [← hty, h2 q, ← PowerSeries.coe_substAlgHom hS, map_add, map_sub, map_sum,
      PowerSeries.coe_substAlgHom hS, ← hal, ← (hlamL q).eq_subst hl0]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [← PowerSeries.coe_substAlgHom hS, map_smul, PowerSeries.coe_substAlgHom hS, hty]
    · rw [← PowerSeries.coe_substAlgHom hS, map_zero]
end Formalism.L2.FormalSeriesBounds.RawChart
