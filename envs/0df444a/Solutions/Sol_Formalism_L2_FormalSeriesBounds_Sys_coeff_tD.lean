-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.coeff_tD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:15:01.305636+00:00
-- url     : https://prove2.me/submissions/a4236ee2-cd2f-49de-a164-deb8452228d8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_smul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_linS_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_det_ne_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_isT_partial
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
variable {τ : Type} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
namespace Sys
theorem _root_.solution (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t)
    (al' : I → ℕ → I → C) (zc : τ → I → C)
    (hal : ∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al' c k b * S.al b 0 x)
    (hW : ∀ β x, W β x = ∑ b, zc β b * S.al b 0 x) (b : I) (A : τ →₀ ℕ) :
    coeff A (subst (linS W) (t b)) =
      coeff A (∑ β, MvPowerSeries.C (zc β b) * (X β : MvPowerSeries τ C)) -
        ∑ c, ∑ j ∈ Finset.Icc 1 A.degree,
          al' c j b * coeff A (subst (linS W) (t c) ^ (V.l ^ j)) := by
  obtain ⟨tD, htD⟩ : ∃ tD : I → MvPowerSeries τ C, tD = fun c => subst (linS W) (t c) := ⟨_, rfl⟩
  have htD' : ∀ c, subst (linS W) (t c) = tD c := fun c => by rw [htD]
  simp only [htD']
  obtain ⟨N, hN⟩ : ∃ N, N = A.degree := ⟨_, rfl⟩
  rw [← hN]

  have key : ∀ x, ∑ s ∈ Finset.range (N + 1), ∑ c : I, S.al c s x * coeff A (tD c ^ (V.l ^ s)) =
      ∑ β, W β x * coeff A (X β : MvPowerSeries τ C) := by
    intro x
    have h := coeff_subst_linS_congr W (fun μ hμ => S.isT_partial ht x N μ hμ) A (le_of_eq hN.symm)
    rw [subst_linS_X, subst_linS_sum, map_sum] at h
    have hR : coeff A (linS W x) = ∑ β, W β x * coeff A (X β : MvPowerSeries τ C) := by
      unfold linS
      rw [map_sum]
      exact Finset.sum_congr rfl fun β _ => by rw [map_smul, smul_eq_mul]
    rw [← hR, ← h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [subst_linS_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [subst_linS_smul, subst_linS_pow, map_smul, smul_eq_mul, htD']

  have hsplit : ∀ f : ℕ → C, ∑ s ∈ Finset.range (N + 1), f s = f 0 + ∑ s ∈ Finset.Icc 1 N, f s := by
    intro f
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    refine Finset.sum_bij (fun s _ => s + 1) ?_ ?_ ?_ ?_
    · intro s hs
      have := Finset.mem_range.1 hs
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · intro s _ s' _ h
      omega
    · intro s hs
      have := Finset.mem_Icc.1 hs
      exact ⟨s - 1, Finset.mem_range.2 (by omega), by omega⟩
    · intro s _
      rfl
  obtain ⟨y, hy⟩ : ∃ y : I → C, y = fun b => coeff A (tD b) +
      (∑ c, ∑ j ∈ Finset.Icc 1 N, al' c j b * coeff A (tD c ^ (V.l ^ j))) -
        ∑ β, zc β b * coeff A (X β : MvPowerSeries τ C) := ⟨_, rfl⟩
  have hvec : Matrix.vecMul y (Matrix.of fun c k : I => S.al c 0 k) = 0 := by
    funext x
    show ∑ b, y b * S.al b 0 x = 0
    have k1 := key x
    rw [hsplit] at k1
    have e0 : ∑ c : I, S.al c 0 x * coeff A (tD c ^ (V.l ^ 0)) =
        ∑ b, coeff A (tD b) * S.al b 0 x := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [pow_zero, pow_one, mul_comm]
    have e1 : ∑ s ∈ Finset.Icc 1 N, ∑ c : I, S.al c s x * coeff A (tD c ^ (V.l ^ s)) =
        ∑ b, (∑ c, ∑ j ∈ Finset.Icc 1 N, al' c j b * coeff A (tD c ^ (V.l ^ j))) * S.al b 0 x := by
      have step1 : ∑ s ∈ Finset.Icc 1 N, ∑ c : I, S.al c s x * coeff A (tD c ^ (V.l ^ s)) =
          ∑ s ∈ Finset.Icc 1 N, ∑ c : I, ∑ b : I,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x := by
        refine Finset.sum_congr rfl fun s hs => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hal c s x (Finset.mem_Icc.1 hs).1, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [step1]
      simp only [Finset.sum_mul]
      calc ∑ s ∈ Finset.Icc 1 N, ∑ c : I, ∑ b : I,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x
          = ∑ c : I, ∑ s ∈ Finset.Icc 1 N, ∑ b : I,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x := Finset.sum_comm
        _ = ∑ c : I, ∑ b : I, ∑ s ∈ Finset.Icc 1 N,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x :=
            Finset.sum_congr rfl fun c _ => Finset.sum_comm
        _ = ∑ b : I, ∑ c : I, ∑ s ∈ Finset.Icc 1 N,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x := Finset.sum_comm
    have e2 : ∑ β, W β x * coeff A (X β : MvPowerSeries τ C) =
        ∑ b, (∑ β, zc β b * coeff A (X β : MvPowerSeries τ C)) * S.al b 0 x := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [hW β x, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e0, e1, e2] at k1
    rw [hy]
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [k1, sub_self]
  have hy0 : y = 0 := Matrix.eq_zero_of_vecMul_eq_zero S.det_ne_zero hvec
  have hyb : y b = 0 := by rw [hy0]; rfl
  rw [hy] at hyb
  have hz : coeff A (∑ β, MvPowerSeries.C (zc β b) * (X β : MvPowerSeries τ C)) =
      ∑ β, zc β b * coeff A (X β : MvPowerSeries τ C) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun β _ => by rw [coeff_C_mul]
  rw [hz]
  linear_combination hyb
end Sys
end Formalism.L2.FormalSeriesBounds
