-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.tieOps_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:50.295384+00:00
-- url     : https://prove2.me/submissions/5ceba4ee-5914-4c87-a4f1-635550425d7a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fockB_apply
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_Ffull
import Theorems.Thm_Formalism_CountingSumsFrames_TO_gam_eq
import Theorems.Thm_Formalism_CountingSumsFrames_TO_gamma_zero_integral_alt
import Theorems.Thm_Formalism_CountingSumsFrames_TO_FfL_apply
import Theorems.Thm_Formalism_CountingSumsFrames_TO_Ffull_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_Ffull_C
import Theorems.Thm_Formalism_CountingSumsFrames_TO_hw_is_Ffull
import Theorems.Thm_Formalism_CountingSumsFrames_TO_Ffull_indep
import Theorems.Thm_Formalism_CountingSumsFrames_TO_mmw_finite
import Theorems.Thm_Formalism_CountingSumsFrames_TO_smith_bases
import Theorems.Thm_Formalism_CountingSumsFrames_TO_K_bound
import Theorems.Thm_Formalism_CountingSumsFrames_TO_S_eq_total
import Theorems.Thm_Formalism_CountingSumsFrames_TO_YYsp_eq
import Theorems.Thm_Formalism_CountingSumsFrames_TO_tie_core
import Theorems.Thm_Formalism_CountingSumsFrames_TO_mmwZ_mmw
import Theorems.Thm_Formalism_CountingSumsFrames_TO_mmwZ_polZ
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_hw
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_ne
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_setTies_deg_eta
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
import Theorems.Thm_Formalism_GM_TM_setTies_deg_eta
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution : Formalism.CountingSumsFrames.TieOps := by
  refine ⟨3, by norm_num, ?_⟩
  intro p _ N r _ _ LL T a E κ n ρ _hp2 hr hρ hadm hE hSn hdeg _hz hκ hHP hHW _hL4 nb f U V dg fw hf hUV hfw i
  classical
  have hK : T.pos i + 1 + 1 ≤ N := hK_of_adm LL T hadm i
  have hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i := by
    rw [S_eq_total (LL.setTies T n) T i (by omega)]; exact hSn i
  have hni : n i ≤ 2 * a := by
    have := hdeg ⟨T.pos i + 1, by omega⟩
    rwa [setTies_deg_eta LL T hadm i n (by omega)] at this
  obtain ⟨coef, hcoef⟩ : ∃ coef : ℕ, coef =
      (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) := ⟨_, rfl⟩
  obtain ⟨NN, hNN⟩ : ∃ NN : ℚ_[p], NN =
      ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ cst : ℚ_[p], cst = (p : ℚ_[p]) ^ ⌈κ⌉₊ * (coef : ℚ_[p]) / NN := ⟨_, rfl⟩
  have hgam : ∀ g g', (p : ℚ_[p]) ^ ⌈κ⌉₊ * tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) g g' =
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    rw [gam_eq LL T hadm i ρ n g g', ← hcoef, ← hNN, hcst]
    ring
  let B : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
      MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
    cst • ((fockB p (Fin N × Fin r)).compl₁₂ ((T.phi p (LL.setTies T n) i) ∘ₗ FfL p (LL.setTies T n) T i ρ (n i))
      (FfL p (LL.setTies T n) T i ρ (n i)))
  have hB : ∀ g g', B g g' = cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    simp [B, fockB_apply, FfL_apply]
  have hsm : ∀ w, ∃ f' f'' : Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
      (∀ a, f' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      (∀ a, f'' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      LinearIndependent ℚ_[p] f' ∧
      MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg i w a else 0 := by
    intro w
    obtain ⟨hU1, hV1, hU2, hV2, hfac⟩ := hUV i w
    refine smith_bases (nb i w) (f i w) _ (hf i w).1 (hf i w).2 B (U i w) (V i w) (dg i w) hU1 hV1 hU2 hV2 ?_
    rw [← hfac]
    ext x y
    simp only [Matrix.of_apply]
    rw [hB, hgam]
  choose f' f'' hf'1 hf''1 hf'li hf'sp hf'diag using hsm
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset (Fin r → ℤ), ∀ w, w ∈ Ω ↔
      MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ :=
    ⟨(mmw_finite (p := p) LL T i ρ n).toFinset, fun w => by simp⟩
  have hnb0 : ∀ w, w ∉ Ω → nb i w = 0 := by
    intro w hw
    by_contra h0
    have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w = ⊥ := by
      by_contra h; exact hw ((hΩ w).mpr h)
    have hmem : f i w ⟨0, Nat.pos_of_ne_zero h0⟩ ∈
        MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w := by
      rw [← (hf i w).2]; exact Submodule.subset_span ⟨_, rfl⟩
    have h1 := mmwZ_mmw _ _ _ _ _ hmem
    rw [hbot, Submodule.mem_bot] at h1
    exact (hf i w).1.ne_zero _ h1
  have hκ' : ((T.pos i + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ := by
    refine le_trans ?_ hκ
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hlg : 0 ≤ lgV2 p a r := by
      unfold lgV2
      have : (1 : ℝ) ≤ 8 * (a : ℝ) + r := by
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr
        have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        linarith
      have := Real.logb_nonneg hp1 this
      linarith
    have h1 : ((T.pos i : ℝ) + 3) ≤ (N : ℝ) + 2 := by
      have : ((T.pos i + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK
      push_cast at this; linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hlg
  have hspZ : ∀ μ v, v ∈ Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr →
      (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      v ∈ Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)) := by
    intro μ v hv hw hvi
    obtain ⟨g, hg, rfl⟩ := hw_is_Ffull LL T hadm i ρ hρ n hS μ v hv hw hvi
    by_cases hwΩ : (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ∈ Ω
    · have hg' := hf'sp _ hg
      refine Submodule.span_induction (p := fun g _ => T.Ffull p (LL.setTies T n) i ρ (n i) g ∈
        Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))) ?_ ?_ ?_ ?_ hg'
      · rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨⟨⟨_, hwΩ⟩, b⟩, rfl⟩
      · rw [← FfL_apply, map_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [← FfL_apply, map_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [← FfL_apply, LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx
    · have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
          (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) = ⊥ := by
        by_contra h; exact hwΩ ((hΩ _).mpr h)
      have h1 := mmwZ_mmw _ _ _ _ _ hg
      rw [hbot, Submodule.mem_bot] at h1
      rw [h1, ← FfL_apply, map_zero]; exact Submodule.zero_mem _
  have hdiag : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      x.1.1 - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) = y.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1 →
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f'' y.1.1 y.2)) = if x = y then dg i x.1.1 x.2 else 0 := by
    rintro ⟨⟨w, hw⟩, b⟩ ⟨⟨w', hw'⟩, b'⟩ hla
    have hww : w = w' := sub_left_injective hla
    subst hww
    have := hf'diag w b b'
    rw [hB] at this
    simp only
    rw [this]
    by_cases hbb : b = b'
    · subst hbb; simp
    · rw [if_neg hbb, if_neg]
      intro h
      apply hbb
      simpa using h
  have hG0 : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      ‖cst * fock p (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f' y.1.1 y.2))‖ ≤ 1 := by
    intro x y
    rw [fock_Ffull LL T hadm i ρ n]
    have hg := gamma_zero_integral_alt (p := p) (T.pos i) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) a κ hS hni hκ'
      (f' x.1.1 x.2) (f' y.1.1 y.2) (mmwZ_polZ _ _ _ _ _ (hf'1 x.1.1 x.2)) (mmwZ_polZ _ _ _ _ _ (hf'1 y.1.1 y.2))
    rw [← hNN] at hg
    have e : cst * fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) =
        (coef : ℚ_[p]) * ((p : ℚ_[p]) ^ ⌈κ⌉₊ *
          (fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) / NN)) := by
      rw [hcst]; ring
    rw [e, norm_mul]
    exact mul_le_one₀ (gammaIntegralityLemmas.norm_natCast_le_one' coef) (norm_nonneg _) hg
  obtain ⟨Tm, πm, h1, h2, h3, h4, h5⟩ := tie_core (LL.setTies T n) T hadm i ρ ⌈κ / (N + 2)⌉₊ hK hHP hHW E (by linarith)
    (ι := Σ w : Ω, Fin (nb i w.1))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f'' x.1.1 x.2))
    (fun x => x.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1)
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)))
    (Ffull_indep LL T hadm i ρ n hS Ω (nb i) f' (fun w a => mmwZ_mmw _ _ _ _ _ (hf'1 w a)) hf'li)
    hspZ
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => Ffull_int LL T hadm i ρ n hS _ (mmwZ_polZ _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => dg i x.1.1 x.2) cst hdiag hG0
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (hfw i x.1.1).1 hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (hfw i x.1.1).1)
    (fun x => Ffull_ne LL T hadm i ρ n x.1.1 _ (hfw i x.1.1).1 ((hfw i x.1.1).2 ((hΩ _).mp x.1.2)) hS)
  refine ⟨Tm, πm, ⌈κ / (N + 2)⌉₊ * (T.pos i + 1 + 1) + 2 * ⌈κ / (N + 2)⌉₊,
    K_bound N r a (T.pos i + 1 + 1) κ hr hK hκ, h1, h2, h3, fun j hij u _ => h4 j hij u, ?_⟩
  have hsumN : ∑ x ∈ univ.filter (fun x : (Σ w : Ω, Fin (nb i w.1)) => ‖dg i x.1.1 x.2‖ < (p : ℝ) ^ (-E)),
      Module.finrank ℚ_[p] (YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
        (T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))) =
      ∑ w ∈ Ω, (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card *
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) := by
    rw [Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort Ω]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_filter, YYsp_eq]
    exact Finset.sum_const_nat (fun _ _ => rfl)
  have hfs : ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) =
      ∑ w ∈ Ω, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    rw [Finset.mem_coe]
    by_contra hwΩ
    refine hw ?_
    have hle : (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card ≤ nb i w :=
      (Finset.card_le_univ _).trans (by simp)
    have hle0 := Nat.le_zero.mp (hle.trans (hnb0 w hwΩ).le)
    simp only [hle0, Nat.cast_zero, zero_mul]
  rw [hfs]
  rw [hsumN] at h5
  exact_mod_cast h5
end Formalism.CountingSumsFrames.TO
