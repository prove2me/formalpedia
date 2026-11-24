-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.projC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:56.250867+00:00
-- url     : https://prove2.me/submissions/1e882fd1-9919-463e-880f-dd4596e0974d

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_wtsp_iff_wh
import Theorems.Thm_Formalism_CountingSumsFrames_TO_iso_keep_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_iso_keep_mul
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isTypeProj_congr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ycond_congr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_lcomp_fixed
import Theorems.Thm_Formalism_CountingSumsFrames_TO_lcomp_commQ
import Theorems.Thm_Formalism_CountingSumsFrames_comm_wtsp
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_CountingSumsFrames_isoC_le_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_fix
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_int
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_keep
import Theorems.Thm_Formalism_CountingSumsFrames_proj_fix
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_comm
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_pol
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_top
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_top
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
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution [NeZero r] (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    ∃ Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsProjC L j0 (e1 * j0) J M Pi := by
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin j0 → Set (Fin r → ℤ) := fun j => {la | ∀ k, J k = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin j0, ∃ P, IsTypeProj p L j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (le_trans (le_of_lt j.isLt) hj0) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt _hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ L' : Letters N, L'.vec = L.vec → ∀ j, ∀ x ∈ Pol p r L', P j x ∈ Pol p r L' := fun L' hL' j =>
    typeProj_pol L' j (Tj j) (P j) (isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j))
  have hgl : ∀ c d x, lcomp P (List.finRange j0) (glAct p L j0 c d x) =
      glAct p L j0 c d (lcomp P (List.finRange j0) x) := fun c d x =>
    lcomp_commQ P (glAct p L j0 c d) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j) (glAct p L j0 c d)
      (fun la => iso_keep_glAct L (le_of_lt j.isLt) c d la) y) _ x
  refine ⟨lcomp P (List.finRange j0), hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν x hx
    rw [← wtsp_iff_wh] at hx ⊢
    exact comm_wtsp L j0 _ (fun c y => hgl c c y) ν x hx
  · intro L' hL' x hx
    exact lcomp_keep P (Pol p r L' : Set _) _ (fun j _ u hu => hPpol L' hL' j u hu) x hx
  · intro x k
    by_cases hk : J k < j0
    · rw [Mup, if_pos hk]
      have hfix : P ⟨J k, hk⟩ (lcomp P (List.finRange j0) x) = lcomp P (List.finRange j0) x :=
        lcomp_fix P hPP hcomm _ ⟨J k, hk⟩ (List.mem_finRange _) x
      have h1 : lcomp P (List.finRange j0) x ∈ LinearMap.range (P ⟨J k, hk⟩) := ⟨_, hfix⟩
      rw [(hPt ⟨J k, hk⟩).2.1] at h1
      exact (iSup₂_le fun la hla => isoC_le_ycond L (J k) la (M k) (hla k rfl)) h1
    · rw [Mup, if_neg hk, Formalism.GM.DimensionMonotonicity.ycond_top]; exact Submodule.mem_top
  · intro L' hL' x hxP hxY
    refine lcomp_fixed P x (fun j => ?_) _
    have hPt' := isTypeProj_congr L L' hL' j univ (Tj j) (P j) (hPt j)
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r L' ⊓ ⨅ (k : Fin q) (_ : J k = (j : ℕ)), YCond p (r := r) L' j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r L' ∧ ∀ k, J k = (j : ℕ) → x ∈ YCond p (r := r) L' j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix L' j (Tj j) (P j) hPt' S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨Formalism.CountingSumsFrames.glAct_pol L' j c d x hx.1, fun k hk => ycond_glStable L' j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol L' hL' j x hx.1, fun k hk => typeProj_ycond L' j (Tj j) (P j) hPt' (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp L' j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    apply hfix
    rw [hmemS]
    refine ⟨hxP, fun k hk => ?_⟩
    have := hxY k
    rw [Mup, if_pos (by rw [hk]; exact j.isLt), hk] at this
    rw [ycond_congr L L' hL']
    exact this
  · intro x hx
    have := lcomp_int L e1 P (hPpol L rfl) hPint (List.finRange j0) x hx
    rw [List.length_finRange] at this
    exact (Submodule.mem_inf.mp this).2
  · intro g q hq
    have := lcomp_commQ P (LinearMap.mulRight ℚ_[p] q) (fun j y => typeProj_comm L j (Tj j) (P j) (hPt j)
      (LinearMap.mulRight ℚ_[p] q) (fun la => iso_keep_mul L (le_of_lt j.isLt) hq la) y) (List.finRange j0) g
    simpa only [LinearMap.mulRight_apply] using this
end Formalism.CountingSumsFrames.TO
