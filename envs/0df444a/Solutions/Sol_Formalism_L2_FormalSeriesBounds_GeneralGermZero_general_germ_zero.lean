-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.general_germ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:19:50.896339+00:00
-- url     : https://prove2.me/submissions/2053ab99-050c-44ce-b2b4-7e398e8f3afe

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_sysK_P
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_abstract_germ_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
namespace GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
section Sum
variable {F : κ → MvPowerSeries (Fin 2 × κ) C} (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
include hF0
end Sum
section Sys1
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
  (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
  (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
  (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
  (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
include hF0 hFI hadd hlin hexlg
private theorem v_sum_lemma {K : Type} [Field K] (w : AddValuation K (WithTop ℝ)) {ι : Type} (s : Finset ι)
    (x : ι → K) (hx : ∀ i ∈ s, (0 : WithTop ℝ) ≤ w (x i)) : (0 : WithTop ℝ) ≤ w (∑ i ∈ s, x i) :=
  Finset.sum_induction x (fun y => (0 : WithTop ℝ) ≤ w y) (fun a b ha hb => le_trans (le_min ha hb) (AddValuation.map_add w a b))
    (by
      show (0 : WithTop ℝ) ≤ w 0
      rw [AddValuation.map_zero]
      exact le_top) hx
end Sys1
end GeneralGermZero
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
  (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
  (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
  (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
  (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
include hF0 hFI hadd hlin hexlg
namespace Formalism.L2.FormalSeriesBounds.GeneralGermZero
theorem _root_.solution
    (hsat : ∀ g, ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (H : ∀ g, X.CartHyp V g) : RawChart.IntegralGermIndependentOfSystem H := by
  intro S S₂ t t₂ hT hT₂
  choose w hw0 hw using hsat
  choose P hP0 hPI hPlin hPeq using fun g => sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S g)
  choose P₂ hP0₂ hPI₂ hPlin₂ hPeq₂ using fun g => sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S₂ g)
  refine AbstractGermZero.abstract_germ_zero V I t t₂ (fun g k => ∑ x, w g x k • P g x) (fun g k => ∑ x, w g x k • P₂ g x)
    (fun g c => (hT g).1 c) (fun g c => (hT₂ g).1 c) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g k
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
    simp [MvPowerSeries.coeff_smul, hP0]
  · intro g k μ
    show (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (∑ x, w g x k • P g x))
    rw [map_sum]
    refine v_sum_lemma X F hF0 hFI hadd hlin hexlg V.v _ _ (fun x _ => ?_)
    have h1 : (0 : WithTop ℝ) ≤ V.v (w g x k) := hw0 g x k
    have h2 : (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (P g x)) := hPI g x μ
    rw [MvPowerSeries.coeff_smul, AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro g
    have hm : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (∑ x, w g x k • P g x)) =
        (Matrix.of (S g).tan).transpose := by
      ext k c
      simp only [Matrix.of_apply, Matrix.transpose_apply, map_sum, MvPowerSeries.coeff_smul, hPlin, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hr : ∀ c' : I g, ∑ x, w g x k * (X.u g c' x * (S g).tan c c') =
          (∑ x, X.u g c' x * w g x k) * (S g).tan c c' := by
        intro c'
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      simp [hr, hw g]
    rw [hm, Matrix.det_transpose]
    exact (S g).unimod
  · intro g k
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
    simp [MvPowerSeries.coeff_smul, hP0₂]
  · intro g k μ
    show (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (∑ x, w g x k • P₂ g x))
    rw [map_sum]
    refine v_sum_lemma X F hF0 hFI hadd hlin hexlg V.v _ _ (fun x _ => ?_)
    have h1 : (0 : WithTop ℝ) ≤ V.v (w g x k) := hw0 g x k
    have h2 : (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (P₂ g x)) := hPI₂ g x μ
    rw [MvPowerSeries.coeff_smul, AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro g
    have hm : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (∑ x, w g x k • P₂ g x)) =
        (Matrix.of (S₂ g).tan).transpose := by
      ext k c
      simp only [Matrix.of_apply, Matrix.transpose_apply, map_sum, MvPowerSeries.coeff_smul, hPlin₂, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hr : ∀ c' : I g, ∑ x, w g x k * (X.u g c' x * (S₂ g).tan c c') =
          (∑ x, X.u g c' x * w g x k) * (S₂ g).tan c c' := by
        intro c'
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      simp [hr, hw g]
    rw [hm, Matrix.det_transpose]
    exact (S₂ g).unimod
  · intro g k
    have ht : MvPowerSeries.HasSubst (t g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hT g).1
    have ht₂ : MvPowerSeries.HasSubst (t₂ g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hT₂ g).1
    rw [← MvPowerSeries.coe_substAlgHom ht, ← MvPowerSeries.coe_substAlgHom ht₂]
    simp only [map_sum, map_smul]
    simp only [MvPowerSeries.coe_substAlgHom, hPeq g (t g) (hT g), hPeq₂ g (t₂ g) (hT₂ g)]
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
