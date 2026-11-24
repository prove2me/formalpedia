-- Prove2me | solution 1 for Formalism.CountingSumsFrames.count_HW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:49.125741+00:00
-- url     : https://prove2.me/submissions/00173f2a-8b7f-46e6-bff3-d13e7bbad6e4

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_count_Y
import Theorems.Thm_Formalism_CountingSumsFrames_basis_chain
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_of_isWt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_fd
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
    (S : Finset (Fin r → ℤ)) (hS : ∀ x ∈ Pol p r (Lz L j0), ∀ μ ∉ S, (GA p L j0).comp μ x = 0)
    (e : (Fin r → ℤ) → MvPolynomial (Fin N × Fin r) ℚ_[p])
    (he : ∀ μ, e μ ∈ GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M)
    (he0 : ∀ μ, GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M ≠ ⊥ → e μ ≠ 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) =
      ∑ μ ∈ S, Module.finrank ℚ_[p] (GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p L j0 J M (e μ)) := by
  classical
  have hCW : Cset p L j0 J M ≤ Pol p r (Lz L j0) := inf_le_left
  haveI := pol_fd (p := p) (r := r) (Lz L j0)
  haveI : ∀ μ, FiniteDimensional ℚ_[p] (GlX.HWs (GA p L j0) μ ⊓ Pol p r (Lz L j0) : Submodule ℚ_[p] _) :=
    fun μ => Submodule.finiteDimensional_of_le inf_le_right
  choose b hbB hbli hbsp hbe hbA hbcard using fun μ => basis_chain
    (GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M) (GlX.HWs (GA p L j0) μ ⊓ Pol p r (Lz L j0))
    (inf_le_inf_left _ hCW) (e μ) (he μ)
  have hbHW : ∀ μ x, x ∈ b μ → (GA p L j0).IsHW μ x := fun μ x hx => (hbB μ hx).1
  have hbP : ∀ μ x, x ∈ b μ → x ∈ Pol p r (Lz L j0) := fun μ x hx => (hbB μ hx).2
  have hμS : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ≠ 0 → μ ∈ S := by
    intro μ v hv hvh hv0
    by_contra hn
    exact hv0 (by have := hS v hv μ hn; rwa [hvh.1] at this)
  let h : ((μ : {μ // μ ∈ S}) × {x // x ∈ b μ.1}) → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun i => i.2.1
  let la : ((μ : {μ // μ ∈ S}) × {x // x ∈ b μ.1}) → Fin r → ℤ := fun i => i.1.1
  have hli : LinearIndependent ℚ_[p] h := by
    rw [Fintype.linearIndependent_iff]
    rintro g hg ⟨ν, x⟩
    have h1 : ∑ y : {y // y ∈ b ν.1}, g ⟨ν, y⟩ • (y.1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) = 0 := by
      have h0 := congrArg ((GA p L j0).comp ν.1) hg
      rw [map_zero, Fintype.sum_sigma, map_sum, Finset.sum_eq_single ν] at h0
      · rw [map_sum] at h0
        rw [← h0]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [map_smul]
        show _ = g ⟨ν, y⟩ • (GA p L j0).comp ν.1 y.1
        rw [(hbHW ν.1 y.1 y.2).1]
      · intro μ _ hμ
        rw [map_sum]
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [map_smul]
        show g ⟨μ, y⟩ • (GA p L j0).comp ν.1 y.1 = 0
        rw [(GA p L j0).comp_of_isWt (hbHW μ.1 y.1 y.2).1, if_neg (fun hh => hμ (Subtype.ext hh.symm)), smul_zero]
      · simp
    have h2 := (linearIndepOn_finset_iff.mp (hbli ν.1)) (fun y => if hy : y ∈ b ν.1 then g ⟨ν, ⟨y, hy⟩⟩ else 0) (by
      rw [← Finset.sum_attach, ← h1, Finset.univ_eq_attach]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [dif_pos y.2]; rfl) x.1 x.2
    simpa [x.2] using h2
  obtain ⟨k1, k2, k3⟩ := count_Y L j0 J M h la (fun i => hbHW _ _ i.2.2) (fun i => hbP _ _ i.2.2) hli
    (by
      intro μ v hv hvh
      by_cases hv0 : v = 0
      · rw [hv0]; exact Submodule.zero_mem _
      · have hμ := hμS μ v hv hvh hv0
        refine Submodule.span_mono ?_ (hbsp μ ⟨hvh, hv⟩)
        intro x hx
        exact ⟨⟨⟨μ, hμ⟩, ⟨x, hx⟩⟩, rfl⟩)
    (by
      intro μ v hv hvh
      by_cases hv0 : v = 0
      · rw [hv0]; exact Submodule.zero_mem _
      · have hμ := hμS μ v (hCW hv) hvh hv0
        refine Submodule.span_mono ?_ (hbA μ ⟨hvh, hv⟩)
        rintro x ⟨hx, hxA⟩
        exact ⟨⟨⟨μ, hμ⟩, ⟨x, hx⟩⟩, hxA.2, rfl⟩)
  rw [k1, Fintype.sum_sigma, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun μ _ => ?_
  show ∑ y : {y // y ∈ b μ.1}, Module.finrank ℚ_[p] (YYs p L j0 J M y.1) = _
  rw [Finset.sum_coe_sort (b μ.1) (fun y => Module.finrank ℚ_[p] (YYs p L j0 J M y)),
    ← Finset.sum_filter_add_sum_filter_not (b μ.1) (· ∈ GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M)]
  have z2 : ∑ x ∈ (b μ.1).filter (fun x => ¬ x ∈ GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M),
      Module.finrank ℚ_[p] (YYs p L j0 J M x) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxb, hxA⟩ := Finset.mem_filter.mp hx
    have := k2 ⟨μ, ⟨x, hxb⟩⟩ (fun hC => hxA ⟨hbHW _ _ hxb, hC⟩)
    show Module.finrank ℚ_[p] (YYs p L j0 J M x) = 0
    have e1 : YYs p L j0 J M x = ⊥ := this
    rw [e1]; exact finrank_bot _ _
  have z1 : ∀ x ∈ (b μ.1).filter (· ∈ GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M),
      Module.finrank ℚ_[p] (YYs p L j0 J M x) = Module.finrank ℚ_[p] (YYs p L j0 J M (e μ.1)) := by
    intro x hx
    obtain ⟨hxb, hxA⟩ := Finset.mem_filter.mp hx
    have hx0 : x ≠ 0 := (hli.ne_zero ⟨μ, ⟨x, hxb⟩⟩ : h ⟨μ, ⟨x, hxb⟩⟩ ≠ 0)
    have hne : GlX.HWs (GA p L j0) μ.1 ⊓ Cset p L j0 J M ≠ ⊥ := fun hb => hx0 (by
      rw [hb] at hxA; exact (Submodule.mem_bot _).mp hxA)
    have heb := hbe μ.1 (he0 μ.1 hne)
    exact le_antisymm (k3 ⟨μ, ⟨x, hxb⟩⟩ ⟨μ, ⟨e μ.1, heb⟩⟩ hxA.2 (he μ.1).2 rfl)
      (k3 ⟨μ, ⟨e μ.1, heb⟩⟩ ⟨μ, ⟨x, hxb⟩⟩ (he μ.1).2 hxA.2 rfl)
  rw [z2, add_zero, Finset.sum_congr rfl z1, Finset.sum_const, hbcard, smul_eq_mul]
end Formalism.CountingSumsFrames
