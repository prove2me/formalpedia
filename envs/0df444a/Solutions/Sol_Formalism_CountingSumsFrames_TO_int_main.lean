-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.int_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:25.993848+00:00
-- url     : https://prove2.me/submissions/db062dd3-7aec-4521-9adc-34b92d199035

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_divpow_int
import Theorems.Thm_Formalism_CountingSumsFrames_TO_comm_pow
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_pol
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum
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
theorem _root_.solution (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (K0 : ℕ)
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x))
    (hhw : ∀ la : Fin r → ℤ, ∀ h ∈ HWC p L j0 univ la ⊓ Pol p r L, h ∈ IntPol p (Fin N × Fin r) →
      ((p : ℚ_[p]) ^ K0) • Tm h ∈ IntPol p (Fin N × Fin r)) :
    ∀ y ∈ PolZ p r L, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r) := by
  classical
  obtain ⟨hP1, -⟩ := hHP
  have hsat : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T := fun T la la' h => by
    rw [show la = la' from funext fun c => h c (mem_univ c)]

  have htop : (⨆ la : Fin r → ℤ, IsoC p L j0 univ la) = ⊤ := by
    obtain ⟨P0, ⟨hPP, hran, hker⟩, -, -⟩ := hP1 j0 hj0 univ (Or.inl rfl) Set.univ (hsat _)
    have hk : LinearMap.ker P0 = ⊥ := by
      rw [hker]; simp
    have hid : ∀ x, P0 x = x := by
      intro x
      have : P0 x - x ∈ LinearMap.ker P0 := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact LinearMap.congr_fun hPP x
      rw [hk, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have hr : LinearMap.range P0 = ⊤ := by
      rw [eq_top_iff]; intro x _; exact ⟨x, hid x⟩
    rw [← hr, hran]; simp
  have hex : ∀ la : Fin r → ℤ, ∃ P, IsTypeProj p L j0 univ {la} P ∧
      ∀ F ∈ PolZ p r L, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) := fun la => by
    obtain ⟨P, h1, -, h3⟩ := hP1 j0 hj0 univ (Or.inl rfl) {la} (hsat _)
    exact ⟨P, h1, h3⟩
  choose P hPt hPint using hex

  set S : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    (IntPol p (Fin N × Fin r)).comap ((((p : ℚ_[p]) ^ K0) • Tm).restrictScalars ℤ_[p]) with hS
  have hmemS : ∀ x, x ∈ S ↔ ((p : ℚ_[p]) ^ K0) • Tm x ∈ IntPol p (Fin N × Fin r) := fun x => Iff.rfl
  have hWeyl : ∀ la : Fin r → ℤ, ∀ h, (h ∈ HWC p L j0 univ la ⊓ Pol p r L ∧ h ∈ IntPol p (Fin N × Fin r)) →
      WeylLat p L j0 h ≤ S := by
    intro la h hh
    refine sInf_le ⟨(hmemS h).mpr (hhw la h hh.1 hh.2), ?_⟩
    intro c d hcd k x hx
    rw [hmemS] at hx ⊢
    rw [map_smul, comm_pow L j0 Tm hcomm c d k x, smul_comm, ← map_smul]
    exact divpow_int L j0 c d hcd k _ hx
  intro y hy
  have hyP : y ∈ Pol p r L := (Submodule.mem_inf.mp hy).1
  have hyT : y ∈ ⨆ la : Fin r → ℤ, IsoC p L j0 univ la := by rw [htop]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hyT
  have hPfix : ∀ la, ∀ x ∈ IsoC p L j0 univ la, P la x = x := by
    intro la x hx
    have : x ∈ LinearMap.range (P la) := by
      rw [(hPt la).2.1]
      exact (le_iSup₂ (f := fun la' (_ : la' ∈ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') la rfl) hx
    obtain ⟨z, rfl⟩ := this
    exact LinearMap.congr_fun (hPt la).1 z
  have hPkill : ∀ la mu, mu ≠ la → ∀ x ∈ IsoC p L j0 univ mu, P la x = 0 := by
    intro la mu hne x hx
    have : x ∈ LinearMap.ker (P la) := by
      rw [(hPt la).2.2]
      exact (le_iSup₂ (f := fun la' (_ : la' ∉ ({la} : Set (Fin r → ℤ))) => IsoC p L j0 univ la') mu hne) hx
    exact this
  have hPy : ∀ la, P la y = f la := by
    intro la
    rw [← hsum, Finsupp.sum, map_sum]
    rw [Finset.sum_eq_single la]
    · exact hPfix la _ (hf la)
    · intro mu _ hne; exact hPkill la mu hne _ (hf mu)
    · intro hla
      rw [Finsupp.notMem_support_iff.mp hla, map_zero]
  have hterm : ∀ la, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm (P la y) ∈ IntPol p (Fin N × Fin r) := by
    intro la
    have h1 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IntPol p (Fin N × Fin r) := hPint la y hy
    have h2 : ((p : ℚ_[p]) ^ e1) • P la y ∈ IsoC p L j0 univ la ⊓ Pol p r L :=
      Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨by rw [hPy]; exact hf la,
        typeProj_pol L j0 {la} (P la) (hPt la) y hyP⟩)
    have h3 := hHW j0 hj0 la _ h2 h1
    have h4 : ((p : ℚ_[p]) ^ e1) • ((p : ℚ_[p]) ^ e1) • P la y ∈ S :=
      (iSup₂_le fun h hh => hWeyl la h hh) h3
    rw [hmemS, map_smul, map_smul, smul_smul, smul_smul] at h4
    have e : (p : ℚ_[p]) ^ (K0 + 2 * e1) = (p : ℚ_[p]) ^ K0 * (p : ℚ_[p]) ^ e1 * (p : ℚ_[p]) ^ e1 := by
      rw [pow_add, two_mul, pow_add, mul_assoc]
    rw [e]; exact h4
  have hy2 : y = ∑ la ∈ f.support, P la y := by
    conv_lhs => rw [← hsum, Finsupp.sum]
    exact Finset.sum_congr rfl fun la _ => (hPy la).symm
  rw [hy2, map_sum, Finset.smul_sum]
  exact Submodule.sum_mem _ fun la _ => hterm la
end Formalism.CountingSumsFrames.TO
