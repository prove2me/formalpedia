-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.ycond_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:04.871894+00:00
-- url     : https://prove2.me/submissions/4ffc958e-f3ce-4ae5-8093-89b9bd11e66f

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
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
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
variable {r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section Ops
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ]
end Ops
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section W
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ] {M : Type} [AddCommGroup M]
end W
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
private theorem rM_of_wh_lemma [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ) (ν : Fin r → ℤ)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hz : z ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν)
    (hν : ((ν 0 : ℤ) : WithTop ℤ) ≤ M) :
    z ∈ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M} := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  rw [mem_weightedHomogeneousSubmodule] at hz
  have h1 := hz (mem_support_iff.mp hm)
  show ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M
  rw [← weight_wv, h1]
  exact hν
private theorem ycond_stable_lemma_2 [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ) :
    GlStable p LL J (YCond p (r := r) LL J M) := by
  intro c d x hx
  have hle : YCond p (r := r) LL J M ≤ (YCond p (r := r) LL J M).comap (glAct p LL J c d) := by
    unfold YCond
    apply sSup_le
    intro S hS y hy
    exact le_sSup hS (hS.2 c d y hy)
  exact hle hx
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Comparison₂
section Tie2
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Tie2
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d F, A (glAct p LL J c d F) = glAct p LL J c d (A F))
    (hw : ∀ ν F, F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν →
      A F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    ∀ F ∈ YCond p LL J M, A F ∈ YCond p LL J M := by
  intro F hF
  have hYR : YCond p (r := r) LL J M ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M} :=
    sSup_le fun S hS => hS.1
  have hYst : GlStable p LL J (YCond p (r := r) LL J M) := ycond_stable_lemma_2 LL J M
  have hmap : (YCond p (r := r) LL J M).map A ≤ YCond p (r := r) LL J M := by
    apply le_sSup
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have hyR := hYR hy
      rw [MvPolynomial.mem_restrictSupport_iff] at hyR
      classical
      have hsum : y = ∑ ν ∈ y.support.image (Finsupp.weight (wv LL J)),
          weightedHomogeneousComponent (wv LL J) ν y := by
        ext d
        rw [coeff_sum]
        simp only [coeff_weightedHomogeneousComponent]
        rw [Finset.sum_ite_eq]
        split_ifs with h
        · rfl
        · by_contra hne
          exact h (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hne, rfl⟩)
      rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun ν hν => ?_
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hν
      apply rM_of_wh_lemma LL J M
      · exact hw _ _ (weightedHomogeneousComponent_mem _ y _)
      · have h2 : ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M := hyR hm
        rw [← weight_wv] at h2
        exact h2
    · intro c d x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      rw [← hc]
      exact Submodule.mem_map_of_mem (hYst c d y hy)
  exact hmap (Submodule.mem_map_of_mem hF)
end Formalism.GM.DimensionMonotonicity
