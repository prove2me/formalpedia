-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.cprod_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:48.873117+00:00
-- url     : https://prove2.me/submissions/7a27923e-bb85-4059-b8e9-448eedb9167a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


section
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
private theorem cas_wt_lemma_2 {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : G.Cas v - ((GlW.casI μ : ℤ) : K) • v ∈ U := by
  have hw := hv
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsWt at hw
  have hd : ∀ c, G.E c c v = ((μ c : ℤ) : K) • v := fun c => by
    have := G.diag c μ v
    rwa [hw] at this
  have hterm : ∀ a b, G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v ∈ U := by
    intro a b
    split_ifs with hab hlt
    · subst hab
      rw [hd, map_smul, hd, smul_smul, Int.cast_mul, sub_self]
      exact zero_mem _
    · have hc := G.comm a b b a v
      simp only [if_true, eq_self_iff_true] at hc
      have e : G.E a b (G.E b a v) - (((μ a - μ b : ℤ)) : K) • v = G.E b a (G.E a b v) := by
        rw [Int.cast_sub, sub_smul, ← hd a, ← hd b, ← hc]
        abel
      rw [e]
      exact hU b a _ (hr a b hlt)
    · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
      rw [Int.cast_zero, zero_smul, sub_zero]
      exact hU a b _ (hr b a hba)
  have e2 : G.Cas v - ((GlW.casI μ : ℤ) : K) • v = ∑ a, ∑ b, (G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v) := by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, Formalism.GM.DimensionMonotonicity.GlW.casI, LinearMap.sum_apply, LinearMap.comp_apply,
      Int.cast_sum, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [e2]
  exact sum_mem fun a _ => sum_mem fun b _ => hterm a b
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
section Proj
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
end Proj
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset
section Ext
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
end Ext
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
section OpsAux
variable {k σ : Type} [Field k]
end OpsAux
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)
include hadm
end Comparison₂
section Tie2
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Tie2
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Leib
variable {σ : Type} (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
  (hA : ∀ a b, A (a * b) = a * A b + b * A a)
include hA
end Leib
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
include hρ
omit hρ
omit hadm hS
end Comparison₂
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Gen
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
end Gen
section
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)
include hPi
include hφ
end
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})
include hPi hh hhC hli hsp
end
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames
end Formalism.CountingSumsFrames
end

set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.TO.GlX
theorem _root_.solution {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v ∈ U := by
  have hcas : ∀ y ∈ U, G.Cas y ∈ U := fun y hy => by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]
    exact sum_mem fun a _ => sum_mem fun b _ => hU a b _ (hU b a y hy)
  induction cs with
  | nil => simp [Formalism.GM.DimensionMonotonicity.GlW.cprod]
  | cons c cs ih =>
    have key : G.cprod (c :: cs) v - ((c :: cs).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v =
        (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • (G.Cas v - ((GlW.casI μ : ℤ) : K) • v) +
        (G.Cas (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v) -
          ((c : ℤ) : K) • (G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v)) := by
      simp only [Formalism.GM.DimensionMonotonicity.GlW.cprod, LinearMap.comp_apply, List.map_cons, List.prod_cons,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, Int.cast_sub]
      module
    rw [key]
    exact add_mem (U.smul_mem _ (cas_wt_lemma_2 G hU hv hr)) (sub_mem (hcas _ ih) (U.smul_mem _ ih))
end Formalism.CountingSumsFrames.TO.GlX
