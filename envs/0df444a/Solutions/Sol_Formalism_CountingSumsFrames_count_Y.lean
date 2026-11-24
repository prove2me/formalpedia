-- Prove2me | solution 1 for Formalism.CountingSumsFrames.count_Y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:37.656072+00:00
-- url     : https://prove2.me/submissions/d9da1b34-cee2-4a13-808c-e8e53bab3b23

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_comp_comm_of
import Theorems.Thm_Formalism_CountingSumsFrames_ext_eq_sum
import Theorems.Thm_Formalism_CountingSumsFrames_eq_sum_sl
import Theorems.Thm_Formalism_CountingSumsFrames_slc_pol
import Theorems.Thm_Formalism_CountingSumsFrames_slc_C
import Theorems.Thm_Formalism_CountingSumsFrames_ext_Y
import Theorems.Thm_Formalism_CountingSumsFrames_psi_id
import Theorems.Thm_Formalism_CountingSumsFrames_phi_props
import Theorems.Thm_Formalism_CountingSumsFrames_C_stable
import Theorems.Thm_Formalism_CountingSumsFrames_polynomial_finite_weights
import Theorems.Thm_Formalism_CountingSumsFrames_exists_pi
import Theorems.Thm_Formalism_CountingSumsFrames_finrank_of_proj
import Theorems.Thm_Formalism_CountingSumsFrames_ext_mem_span
import Theorems.Thm_Formalism_CountingSumsFrames_ext_rep
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_exists_theta
import Theorems.Thm_Formalism_CountingSumsFrames_Y_fd
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_stable
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



set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhP : ∀ i, h i ∈ Pol p r (Lz L j0))
    (hli : LinearIndependent ℚ_[p] h)
    (hsp : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ∈ Submodule.span ℚ_[p] (Set.range h))
    (hspC : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (h '' {i | h i ∈ Cset p L j0 J M})) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) = ∑ i, Module.finrank ℚ_[p] (YYs p L j0 J M (h i)) ∧
    (∀ i, h i ∉ Cset p L j0 J M → YYs p L j0 J M (h i) = ⊥) ∧
    (∀ i j, h i ∈ Cset p L j0 J M → h j ∈ Cset p L j0 J M → la i = la j →
      Module.finrank ℚ_[p] (YYs p L j0 J M (h i)) ≤ Module.finrank ℚ_[p] (YYs p L j0 J M (h j))) := by
  classical
  obtain ⟨π, h1, h2, h3, hsum, hC, hC0, hE, hc⟩ := exists_pi L j0 J M h la hh hhP hli hsp hspC
  have hP1s : (GA p L j0).Stable (Pol p r (Lz L j0)) := pol_stable L (Lz L j0) j0
  have hCs := C_stable (p := p) (r := r) L j0 J M
  have hCW : Cset p L j0 J M ≤ Pol p r (Lz L j0) := inf_le_left
  have hRW : ∀ i, (GA p L j0).gS {h i} ≤ Pol p r (Lz L j0) := fun i =>
    (GA p L j0).gS_le (by simpa using hhP i) hP1s
  haveI := Y_fd (p := p) (r := r) L J M
  have hPY : ∀ i, ∀ x ∈ Y p L J M, ext (fsj N r j0) (π i ∘ₗ psi p L j0) x ∈ Y p L J M := by
    intro i
    obtain ⟨a1, a2, a3⟩ := phi_props L j0 (π i) (fun x _ => hRW i (h1 i x)) (hE i) (hc i)
    refine ext_Y L j0 J M _ a1 a2 a3 (fun x hx => ?_)
    rw [LinearMap.comp_apply, psi_id L j0 (hCW hx)]; exact hC i x hx
  have c2 : ∀ i, ∀ x ∈ YYs p L j0 J M (h i), ext (fsj N r j0) (π i ∘ₗ psi p L j0) x = x := by
    intro i x hx
    obtain ⟨s, a, ha, hxs, hext⟩ := ext_rep L j0 _ (hRW i) hx.2
    conv_lhs => rw [hxs]
    rw [hext a (fun b => hRW i (ha b))]
    conv_rhs => rw [hxs]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [LinearMap.comp_apply, psi_id L j0 (hRW i (ha b)), h2 i _ (ha b)]
  have hslsum : ∀ (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
      (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), ext (fsj N r j0) φ x =
      ∑ m ∈ x.support.image (ltr (fsj N r j0)), φ (slc (fsj N r j0) m x) * monomial m 1 := fun φ x =>
    ext_eq_sum (fsj N r j0) φ x _ (fun m hm => Finset.mem_image_of_mem _ hm)
  refine ⟨?_, ?_, ?_⟩
  · refine finrank_of_proj (Y p L J M) (fun i => YYs p L j0 J M (h i))
      (fun i => ext (fsj N r j0) (π i ∘ₗ psi p L j0)) (fun i => inf_le_left) (fun i x hx => ?_) c2
      (fun i j hij x hx => ?_) (fun x hx => ?_)
    · exact ⟨hPY i x hx, ext_mem_span j0 _ (π i ∘ₗ psi p L j0) (fun y => h1 i _) x⟩
    · obtain ⟨s, a, ha, hxs, hext⟩ := ext_rep L j0 _ (hRW j) hx.2
      rw [hxs, hext a (fun b => hRW j (ha b))]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [LinearMap.comp_apply, psi_id L j0 (hRW j (ha b)), h3 i j (Ne.symm hij) _ (ha b), zero_mul]
    · simp_rw [hslsum]
      rw [Finset.sum_comm]
      conv_rhs => rw [eq_sum_sl (fsj N r j0) x (x.support.image (ltr (fsj N r j0)))
        (fun m hm => Finset.mem_image_of_mem _ hm)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      have hP := slc_pol L j0 m (Submodule.mem_inf.mp hx).1
      simp only [LinearMap.comp_apply, psi_id L j0 hP]
      exact hsum _ hP
  · intro i hi
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot, ← c2 i x hx, hslsum]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hCm := slc_C L j0 J M hx.1 m
    rw [LinearMap.comp_apply, psi_id L j0 (hCW hCm), hC0 i hi _ hCm, zero_mul]
  · intro i j hi hj hij
    obtain ⟨θ, θ', t1, t2, t3, t4, t5⟩ := GlX.exists_theta (GA p L j0) hP1s (polynomial_finite_weights L j0) (hh i) (hij ▸ hh j)
      (hhP i) (hhP j) (hli.ne_zero i) (hli.ne_zero j) (π i) (π j) (h1 i) (h2 i) (hE i) (h1 j) (h2 j) (hE j)
    have hRC : (GA p L j0).gS {h j} ≤ Cset p L j0 J M := (GA p L j0).gS_le (by simpa using hj) hCs
    have hTY : ∀ x ∈ Y p L J M, ext (fsj N r j0) (θ ∘ₗ psi p L j0) x ∈ Y p L J M := by
      obtain ⟨a1, a2, a3⟩ := phi_props L j0 θ (fun x _ => hRW j (t1 x)) t2
        (GlX.comp_comm_of (GA p L j0) ((GA p L j0).graded_of hP1s) θ (fun x hx c => t2 x hx c c))
      exact ext_Y L j0 J M _ a1 a2 a3 (fun x _ => hRC (t1 _))
    let f : YYs p L j0 J M (h i) →ₗ[ℚ_[p]] YYs p L j0 J M (h j) :=
      ((ext (fsj N r j0) (θ ∘ₗ psi p L j0)).comp (YYs p L j0 J M (h i)).subtype).codRestrict _
        (fun x => ⟨hTY x x.2.1, ext_mem_span j0 _ (θ ∘ₗ psi p L j0) (fun y => t1 _) _⟩)
    have hf : Function.Injective f := by
      have hl : ∀ x : YYs p L j0 J M (h i), ext (fsj N r j0) (θ' ∘ₗ psi p L j0) (f x : MvPolynomial (Fin N × Fin r) ℚ_[p]) = x := by
        intro x
        obtain ⟨s, a, ha, hxs, hext⟩ := ext_rep L j0 _ (hRW i) x.2.2
        show ext (fsj N r j0) (θ' ∘ₗ psi p L j0) (ext (fsj N r j0) (θ ∘ₗ psi p L j0) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])) = x
        conv_lhs => rw [hxs]
        rw [hext a (fun b => hRW i (ha b)), hext (fun b => (θ ∘ₗ psi p L j0) (a b)) (fun b => hRW j (t1 _))]
        conv_rhs => rw [hxs]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [LinearMap.comp_apply]
        rw [psi_id L j0 (hRW i (ha b)), psi_id L j0 (hRW j (t1 _)), t5 _ (ha b)]
      intro x y hxy
      apply Subtype.ext
      rw [← hl x, ← hl y, hxy]
    haveI : FiniteDimensional ℚ_[p] (YYs p L j0 J M (h j)) :=
      Submodule.finiteDimensional_of_le (inf_le_left : YYs p L j0 J M (h j) ≤ Y p L J M)
    exact LinearMap.finrank_le_finrank_of_injective hf
end Formalism.CountingSumsFrames
