-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.whc_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:14.204611+00:00
-- url     : https://prove2.me/submissions/bd9718a3-d294-41d1-b032-92297b423778

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
private theorem whc_same_lemma {σ M : Type} [AddCommMonoid M] (w : σ → M) {m : M} {φ : MvPolynomial σ ℚ_[p]}
    (h : φ ∈ weightedHomogeneousSubmodule ℚ_[p] w m) : weightedHomogeneousComponent w m φ = φ := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at h
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))
private theorem whc_ne_lemma_2 {σ M : Type} [AddCommMonoid M] (w : σ → M) {m n : M} {φ : MvPolynomial σ ℚ_[p]}
    (h : φ ∈ weightedHomogeneousSubmodule ℚ_[p] w m) (hnm : n ≠ m) : weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at h
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hd
  · by_contra hne
    exact hnm (hd.symm.trans (h hne))
  · rfl
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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {σ M : Type} [AddCommMonoid M] (w : σ → M) (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hA : ∀ D x, x ∈ weightedHomogeneousSubmodule ℚ_[p] w D → A x ∈ weightedHomogeneousSubmodule ℚ_[p] w D)
    (D : M) (x : MvPolynomial σ ℚ_[p]) :
    weightedHomogeneousComponent w D (A x) = A (weightedHomogeneousComponent w D x) := by
  classical
  refine MvPolynomial.induction_on' x (fun d a => ?_) (fun f g hf hg => ?_)
  · have h0 : monomial d a ∈ weightedHomogeneousSubmodule ℚ_[p] w (Finsupp.weight w d) :=
      (mem_weightedHomogeneousSubmodule ..).mpr (isWeightedHomogeneous_monomial w d a rfl)
    have h1 := hA _ _ h0
    by_cases h : Finsupp.weight w d = D
    · subst h
      rw [whc_same_lemma w h0, whc_same_lemma w h1]
    · rw [whc_ne_lemma_2 w h0 (Ne.symm h), whc_ne_lemma_2 w h1 (Ne.symm h), map_zero]
  · simp only [map_add, hf, hg]
end Formalism.CountingSumsFrames.TO
