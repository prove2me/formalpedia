-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.tie_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:23:54.926272+00:00
-- url     : https://prove2.me/submissions/836bff2c-5cd7-4aea-9dd6-9b026ec56a23

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_span_hw
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_C
import Theorems.Thm_Formalism_CountingSumsFrames_TO_C_stable
import Theorems.Thm_Formalism_CountingSumsFrames_TO_polynomial_finite_weights
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_eqExt
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_form_zero
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_iff
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fockB_apply
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_ext_reduce
import Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_mul_later
import Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_isF
import Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_ext_comm
import Theorems.Thm_Formalism_CountingSumsFrames_TO_projC
import Theorems.Thm_Formalism_CountingSumsFrames_TO_int_main
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_C
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_isF
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_Y
import Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_count_le
import Theorems.Thm_Formalism_CountingSumsFrames_TO_transport_le
import Theorems.Thm_Formalism_CountingSumsFrames_TO_good_norm
import Theorems.Thm_Formalism_CountingSumsFrames_TO_smul_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_exists_pow_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_Cset_thrUpTo
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_smul
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_isHW_zero__e607ce74737d
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_right
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_right
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_zero_left
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
theorem _root_.solution [NeZero r] (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t) (ρ : Fin r) (e1 : ℕ)
    (hK : T.pos i + 1 + 1 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1) (E : ℝ) (hE : 0 ≤ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h' h'' : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h' x))
    (hhC : ∀ x, h' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hli : LinearIndependent ℚ_[p] h')
    (hspZ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ IntPol p (Fin N × Fin r) → v ∈ Submodule.span ℤ_[p] (Set.range h'))
    (hh2 : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (h'' x))
    (hh2C : ∀ x, h'' x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr)
    (hh2i : ∀ x, h'' x ∈ IntPol p (Fin N × Fin r))
    (d : ι → ℚ_[p]) (cst : ℚ_[p])
    (hdiag : ∀ x y, la x = la y → cst * fock p (T.phi p L i (h' x)) (h'' y) = if x = y then d x else 0)
    (hG0 : ∀ x y, ‖cst * fock p (h' x) (h' y)‖ ≤ 1)
    (vv : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (hvv : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (vv x))
    (hvvC : ∀ x, vv x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr) (hvv0 : ∀ x, vv x ≠ 0) :
    ∃ Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ y ∈ Y p (r := r) L T.J T.thr, Tm y ∈ Y p (r := r) L T.J T.thr) ∧
      (∀ y ∈ YZ p (r := r) L T.J T.thr,
        ((p : ℚ_[p]) ^ (e1 * (T.pos i + 1 + 1) + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
      (∀ u ∈ Y p (r := r) L T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) L T.J T.thr,
        fockN p L (T.phi p L i u) (Tm u') = (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p L (πm u) u') ∧
      (∀ j : Fin T.t, i < j → ∀ u, πm (T.phi p L j u) = T.phi p L j (πm u)) ∧
      Module.finrank ℚ_[p] (Y p (r := r) L T.J T.thr) -
        Module.finrank ℚ_[p] ((Y p (r := r) L T.J T.thr ⊓ LinearMap.ker (πm - LinearMap.id) :
          Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
        ∑ x ∈ univ.filter (fun x => ‖d x‖ < (p : ℝ) ^ (-E)),
          Module.finrank ℚ_[p] (YYs L (T.pos i + 1 + 1) T.J T.thr (vv x)) := by
  classical
  obtain ⟨Pi, hPi⟩ := projC L ρ e1 (T.pos i + 1 + 1) hK hHP T.J T.thr
  have hCst := C_stable (p := p) (r := r) L (T.pos i + 1 + 1) T.J T.thr
  have hCf : (GA p L (T.pos i + 1 + 1)).FinW (Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr) := by
    obtain ⟨S, hS⟩ := polynomial_finite_weights (p := p) (r := r) L (T.pos i + 1 + 1)
    exact ⟨S, fun x hx => hS x (Submodule.mem_inf.mp hx).1⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hspQ : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (Set.range h') := by
    intro μ v hv hw
    obtain ⟨k, hk⟩ := exists_pow_int v
    have h1 := hspZ μ (((p : ℚ_[p]) ^ k) • v) (Submodule.smul_mem _ _ hv) (isHW_smul L _ μ _ hw) hk
    have h2 : ((p : ℚ_[p]) ^ k) • v ∈ Submodule.span ℚ_[p] (Set.range h') :=
      Submodule.span_le_restrictScalars ℤ_[p] ℚ_[p] _ h1
    exact (Submodule.smul_mem_iff _ (pow_ne_zero _ hp0)).mp h2
  have hsp : Cset p (r := r) L (T.pos i + 1 + 1) T.J T.thr ≤ ⨆ x, (GA p L (T.pos i + 1 + 1)).gS {h' x} := by
    obtain ⟨S, hS⟩ := hCf
    exact GlX.span_hw (GA p L (T.pos i + 1 + 1)) hCst hS h' la hh hhC (fun x => hli.ne_zero x) hspQ
  set c : ℚ_[p] := (p : ℚ_[p]) ^ ⌊E⌋₊ with hc
  let gϖ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun x => if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else h' x
  let tc : ι → ι → ℚ_[p] := fun z y =>
    if la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E) then (c / d z) * (cst * fock p (h' z) (h' y)) else 0
  let gτ : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] := fun y => ∑ z, tc z y • h'' z
  have hgϖ : ∀ x, (GA p L (T.pos i + 1 + 1)).IsHW (la x) (gϖ x) := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact isHW_zero' L _ _
    · simp only [gϖ, if_neg hx]; exact hh x
  have hgϖC : ∀ x, gϖ x ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr := by
    intro x
    by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
    · simp only [gϖ, if_pos hx]; exact Submodule.zero_mem _
    · simp only [gϖ, if_neg hx]; exact hhC x
  have hgτ : ∀ y, (GA p L (T.pos i + 1 + 1)).IsHW (la y) (gτ y) := by
    intro y
    rw [isHW_iff]
    refine Submodule.sum_mem _ fun z _ => ?_
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · refine Submodule.smul_mem _ _ ?_
      rw [← isHW_iff, ← hz.1]; exact hh2 z
    · simp only [tc, if_neg hz, zero_smul]; exact Submodule.zero_mem _
  have hgτC : ∀ y, gτ y ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr :=
    fun y => Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hh2C z)
  have htc : ∀ z y, ‖tc z y‖ ≤ 1 := by
    intro z y
    by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
    · simp only [tc, if_pos hz, norm_mul]
      exact mul_le_one₀ (good_norm E hE (d z) hz.2).1 (by positivity) (by rw [← norm_mul]; exact hG0 z y)
    · simp only [tc, if_neg hz, norm_zero]; exact zero_le_one
  have hgτi : ∀ y, gτ y ∈ IntPol p (Fin N × Fin r) :=
    fun y => Submodule.sum_mem _ fun z _ => smul_int (htc z y) (hh2i z)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3, -, -, hϖ6, hϖ7⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gϖ la hh hhC hli hsp hgϖ hgϖC
  obtain ⟨τ, hτ1, hτ2, hτ3, -, -, -, -⟩ :=
    GlX.eqExt (GA p L (T.pos i + 1 + 1)) hCst hCf h' gτ la hh hhC hli hsp hgτ hgτC
  have hEϖ : IsEqC L (T.pos i + 1 + 1) T.J T.thr ϖ := ⟨hϖ2, hϖ3⟩
  have hEτ : IsEqC L (T.pos i + 1 + 1) T.J T.thr τ := ⟨hτ2, hτ3⟩
  refine ⟨bigOp L (T.pos i + 1 + 1) Pi τ, bigOp L (T.pos i + 1 + 1) Pi ϖ,
    bigOp_Y L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    have hint : ∀ μ v, v ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr → (GA p L (T.pos i + 1 + 1)).IsHW μ v →
        v ∈ IntPol p (Fin N × Fin r) → τ v ∈ IntPol p (Fin N × Fin r) := by
      intro μ v hv hw hvi
      have h1 := hspZ μ v hv hw hvi
      refine Submodule.span_induction (p := fun v _ => τ v ∈ IntPol p (Fin N × Fin r)) ?_ ?_ ?_ ?_ h1
      · rintro _ ⟨x, rfl⟩
        rw [hτ1]; exact hgτi x
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro a b _ hb
        rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hb
    exact int_main L ρ e1 (T.pos i + 1 + 1) hK hHP hHW (bigOp L (T.pos i + 1 + 1) Pi τ) (e1 * (T.pos i + 1 + 1))
      (bigOp_glAct L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ)
      (fun la0 x hx hxi => bigOp_int L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ hint la0 x hx hxi)
      y (Submodule.mem_inf.mp hy).2
  ·
    intro u hu u' hu'
    have hcore : ∀ g ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr, ∀ g' ∈ Cset p L (T.pos i + 1 + 1) T.J T.thr,
        fock p (T.phi p L i g) (inOp L (T.pos i + 1 + 1) Pi τ g') =
          c * fock p (inOp L (T.pos i + 1 + 1) Pi ϖ g) g' := by
      intro g hg g' hg'
      rw [inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi g' hg', inOp_C L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi g hg]
      let B : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
        (fockB p (Fin N × Fin r)).compl₁₂ (T.phi p L i) τ - c • (fockB p (Fin N × Fin r)).compl₁₂ ϖ LinearMap.id
      have hBa : ∀ x y, B x y = fock p (T.phi p L i x) (τ y) - c * fock p (ϖ x) y := by
        intro x y
        simp [B, fockB_apply]
      have hBz := GlX.form_zero (GA p L (T.pos i + 1 + 1)) hCst h' la hh hhC hsp B ?_ ?_ g hg g' hg'
      · rw [hBa] at hBz; exact sub_eq_zero.mp hBz
      · intro x hx y hy a b
        rw [hBa, hBa]
        change fock p (T.phi p L i (glAct p L (T.pos i + 1 + 1) a b x)) (τ y) -
          c * fock p (ϖ (glAct p L (T.pos i + 1 + 1) a b x)) y =
          fock p (T.phi p L i x) (τ (glAct p L (T.pos i + 1 + 1) b a y)) -
          c * fock p (ϖ x) (glAct p L (T.pos i + 1 + 1) b a y)
        rw [phi_glAct L T hadm i a b x, fock_glAct, hEτ.comm y hy b a, hEϖ.comm x hx a b, fock_glAct]
      · intro x y hxy
        rw [hBa, hτ1, hϖ1]
        have hterm : ∀ z, tc z y * fock p (T.phi p L i (h' x)) (h'' z) =
            if z = x then (if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y)) else 0 := by
          intro z
          by_cases hz : la z = la y ∧ ¬ ‖d z‖ < (p : ℝ) ^ (-E)
          · have h1 := hdiag x z (hxy.trans hz.1.symm)
            simp only [tc, if_pos hz]
            have h2 : c / d z * (cst * fock p (h' z) (h' y)) * fock p (T.phi p L i (h' x)) (h'' z) =
                c / d z * fock p (h' z) (h' y) * (cst * fock p (T.phi p L i (h' x)) (h'' z)) := by ring
            rw [h2, h1]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl, if_pos rfl, if_neg hz.2]
              have hd0 := (good_norm E hE (d z) hz.2).2
              field_simp
            · rw [if_neg (Ne.symm hzx), if_neg hzx, mul_zero]
          · simp only [tc, if_neg hz, zero_mul]
            by_cases hzx : z = x
            · subst hzx
              rw [if_pos rfl]
              have : ‖d z‖ < (p : ℝ) ^ (-E) := by
                by_contra h; exact hz ⟨hxy, h⟩
              rw [if_pos this]
            · rw [if_neg hzx]
        have hsum : fock p (T.phi p L i (h' x)) (gτ y) =
            if ‖d x‖ < (p : ℝ) ^ (-E) then 0 else c * fock p (h' x) (h' y) := by
          simp only [gτ]
          rw [gammaIntegralityLemmas.fock_sum_right]
          simp only [gammaIntegralityLemmas.fock_smul_right, hterm]
          rw [Finset.sum_ite_eq']
          simp
        rw [hsum]
        by_cases hx : ‖d x‖ < (p : ℝ) ^ (-E)
        · simp only [gϖ, if_pos hx]
          rw [gammaIntegralityLemmas.fock_zero_left]; ring
        · simp only [gϖ, if_neg hx]
          ring
    have key := fock_ext_reduce (T.pos i + 1 + 1) (T.phi p L i) (inOp L (T.pos i + 1 + 1) Pi τ)
      (inOp L (T.pos i + 1 + 1) Pi ϖ) c (Cset p L (T.pos i + 1 + 1) T.J T.thr)
      (phi_mul_later L T hadm i) (phi_isF L T hadm i)
      (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi τ hPi hEτ) (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ)
      hcore u u'
      (fun m => by rw [← Cset_thrUpTo]; exact slc_C L (T.pos i + 1 + 1) T.J (T.thrUpTo i) hu m)
      (fun m => slc_C L (T.pos i + 1 + 1) T.J T.thr hu' m)
    unfold fockN
    change fock p (T.phi p L i u) (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi τ) u') / _ =
      c * (fock p (ext (fsj N r (T.pos i + 1 + 1)) (inOp L (T.pos i + 1 + 1) Pi ϖ) u) u' / _)
    rw [key, mul_div_assoc]
  · intro j hij u
    exact phi_ext_comm L T hadm i j hij _ (inOp_isF L (T.pos i + 1 + 1) _ T.J T.thr Pi ϖ hPi hEϖ) u
  · exact (count_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp
      (fun x => ‖d x‖ < (p : ℝ) ^ (-E)) ϖ hEϖ
      (fun x hx => hϖ6 x (by simp only [gϖ, if_neg hx]))
      (fun x hx => hϖ7 x (by simp only [gϖ, if_pos hx]))).trans
      (Finset.sum_le_sum fun x _ => transport_le L (T.pos i + 1 + 1) _ T.J T.thr Pi hPi h' la hh hhC hli hsp x (vv x)
        (hvv x) (hvvC x) (hvv0 x))
end Formalism.CountingSumsFrames.TO
