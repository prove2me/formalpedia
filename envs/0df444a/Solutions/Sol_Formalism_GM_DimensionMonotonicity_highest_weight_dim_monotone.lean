-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.highest_weight_dim_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:00:43.061161+00:00
-- url     : https://prove2.me/submissions/ce50b076-9308-4ca2-ad7d-0ef6fdd064ac

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cas_lt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_bot_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_cprod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_cprod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_chain
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_inj_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_X_gen
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_supp_of_supported
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_indep_B
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_mul_B
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_glAct_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_cprod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_lw
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_mul_cov
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_fd
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_finW
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pow_zero
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_eta
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_setTies_deg_eta
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_takeD_update
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_hw
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_ne
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_ycond
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_step
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_comp_mul_hom
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_eig
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_ne
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_mul_B
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_gSpan_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_rep_span
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_zero_span_highest
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_setTies_deg_ne
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_eta_wL
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_eta_wOut
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_eta_wv
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_eta
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
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution : WeightSpaceDimMonotone := by
  intro p _ N r _ _ LL T hadm ρ hρ hr i n w f hf hf0 hS n' hn
  classical
  have hK := hK_of_adm LL T hadm i
  have hiKN : T.pos i + 1 < N := by omega
  set nU := Function.update n i n' with hnU
  set G := GA p LL (T.pos i + 1 + 1) with hG
  set iK : Fin N := ⟨T.pos i + 1, hiKN⟩ with hiK
  set u := n' - n i with hu
  set eta : MvPolynomial (Fin N × Fin r) ℚ_[p] := X (iK, ρ) ^ u with heta
  set F := T.Ffull p (LL.setTies T n) i ρ (n i) f with hFdef
  set F' := T.Ffull p (LL.setTies T nU) i ρ n' f with hF'def
  set la := w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) with hla
  set la' := w - ((n' : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) with hla'
  have hvK : LL.vec iK = false := vec_eta LL T hadm i hiKN
  have hiKlt : (iK : ℕ) < T.pos i + 1 + 1 := by simp [hiK]
  have hρa : ∀ a b : Fin r, a < b → a ≠ ρ := by
    intro a b hab h; subst h
    have : (a : ℕ) < b := hab
    have := b.isLt; omega

  have hfU : f ∈ MMw p ((LL.setTies T nU).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w := by
    rw [hnU, takeD_update LL T hadm i n n']; exact hf
  have hSU : ((LL.setTies T nU).takeD (T.pos i + 1)).total ≤ nU i := by
    rw [hnU, takeD_update LL T hadm i n n', Function.update_self]; omega
  have hnUi : nU i = n' := by rw [hnU, Function.update_self]
  have hFhw : G.IsHW la F := Ffull_hw LL T hadm i ρ hρ n w f hf hS
  have hF'hw : G.IsHW la' F' := by
    have := Ffull_hw LL T hadm i ρ hρ nU w f hfU hSU
    rw [hnUi] at this; exact this
  have hF0 : F ≠ 0 := Ffull_ne LL T hadm i ρ n w f hf hf0 hS
  have hF'0 : F' ≠ 0 := by
    have := Ffull_ne LL T hadm i ρ nU w f hfU hf0 hSU
    rw [hnUi] at this; exact this
  have hstep : F' = eta * F := Ffull_step LL T hadm i ρ n n' hn f hS
  have hfP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  have hlala : la' = la - (u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) := by
    rw [hla', hla, hu, Nat.cast_sub hn]; rw [sub_smul]; abel

  set L0 := Lz (LL.setTies T n) (T.pos i + 1 + 1) with hL0
  set L1 := Lz (LL.setTies T nU) (T.pos i + 1 + 1) with hL1
  have hFpol : F ∈ Pol p r L0 := Ffull_pol LL T hadm i ρ n f hfP hS
  have hVF : G.gS {F} ≤ Pol p r L0 := G.gS_le (by simpa using hFpol) (pol_stable LL L0 _)
  have hL01a : ∀ b : Fin N, (b : ℕ) ≠ T.pos i + 1 → L1.deg b = L0.deg b := by
    intro b hb
    simp only [hL0, hL1, Lz]
    split_ifs
    · exact setTies_deg_ne LL T hadm i n n' b hb
    · rfl
  have hL01b : ∀ b : Fin N, (b : ℕ) = T.pos i + 1 → L0.deg b = n i ∧ L1.deg b = n' := by
    intro b hb
    have hb' : b = iK := Fin.ext hb
    subst hb'
    simp only [hL0, hL1, Lz, hiKlt, if_true]
    exact ⟨setTies_deg_eta LL T hadm i n hiKN, by rw [setTies_deg_eta LL T hadm i nU hiKN, hnUi]⟩

  set Hu := weightedHomogeneousSubmodule ℚ_[p] (wOut N r iK) 0 ⊓
    weightedHomogeneousSubmodule ℚ_[p] (wL N r) (Pi.single iK (u : ℤ)) with hHu
  set W0 := Submodule.span ℚ_[p] {x | ∃ g ∈ G.gS {F}, ∃ s ∈ Hu, x = g * s} with hW0
  have hetaHu : eta ∈ Hu := Submodule.mem_inf.mpr ⟨eta_wOut iK ρ u, eta_wL iK ρ u⟩
  have hHu_st : ∀ a b, ∀ s ∈ Hu, glAct p LL (T.pos i + 1 + 1) a b s ∈ Hu := by
    intro a b s hs
    exact Submodule.mem_inf.mpr ⟨glAct_lw LL _ a b _ (fun _ _ _ => rfl) (Submodule.mem_inf.mp hs).1,
      glAct_lw LL _ a b _ (fun _ _ _ => rfl) (Submodule.mem_inf.mp hs).2⟩
  have hW0st : G.Stable W0 := by
    intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, s, hs, rfl⟩ := hx
      show glAct p LL (T.pos i + 1 + 1) a b (g * s) ∈ W0
      rw [Formalism.GM.M.FB.glAct_mul]
      refine W0.add_mem (Submodule.subset_span ⟨g, hg, _, hHu_st a b s hs, rfl⟩) ?_
      rw [mul_comm]
      exact Submodule.subset_span ⟨_, G.gS_stable _ a b g hg, s, hs, rfl⟩
    | zero => rw [map_zero]; exact W0.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W0.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W0.smul_mem c hx
  have hW0pol : W0 ≤ Pol p r L1 := by
    rw [hW0, Submodule.span_le]
    rintro _ ⟨g, hg, s, hs, rfl⟩
    rw [mul_comm]
    have hgp := hVF hg
    rw [SetLike.mem_coe, pol_iff]
    rw [pol_iff] at hgp
    have := ((Submodule.mem_inf.mp hs).2).mul hgp
    convert this using 1
    funext b
    simp only [Pi.add_apply, Pi.single_apply]
    by_cases hb : (b : ℕ) = T.pos i + 1
    · have hb' : b = iK := Fin.ext hb
      rw [if_pos hb', (hL01b b hb).1, (hL01b b hb).2, hu]; push_cast [Nat.cast_sub hn]; ring
    · have hb' : b ≠ iK := fun h => hb (by rw [h])
      rw [if_neg hb', hL01a b hb, zero_add]
  haveI : FiniteDimensional ℚ_[p] (Pol p r L1) := pol_fd L1
  haveI hW0fd : FiniteDimensional ℚ_[p] W0 := Submodule.finiteDimensional_of_le hW0pol
  have hW0f : G.FinW W0 := by
    obtain ⟨S, hS'⟩ := pol_finW (p := p) (r := r) L1 (T.pos i + 1 + 1)
    exact ⟨S, fun x hx => hS' x (hW0pol hx)⟩
  have hF'W0 : F' ∈ W0 := by
    rw [hstep, mul_comm]; exact Submodule.subset_span ⟨F, G.subset_gS _ (Set.mem_singleton F), eta, hetaHu, rfl⟩
  have hVF'W0 : G.gS {F'} ≤ W0 := G.gS_le (by simpa using hF'W0) hW0st
  have hwts := weight_zero_span_highest LL (T.pos i + 1 + 1) iK hiKlt hvK ρ hρ la F hFhw u
  rw [← hlala, ← hstep] at hwts

  obtain ⟨cs, hcs, hP⟩ := G.chain (W := W0) (V0 := G.gS {F'}) hW0st hW0f (G.gS_stable _) hVF'W0 (GlW.casI la') (by
    intro U hU hVU hUW μ v hvW hvU hvw hr hc
    have hdμ := G.dom_of_hwmod hU hW0st hW0f hvW hvU hvw hr
    have hdla' := G.dom_of_hwmod G.bot_stable hW0st hW0f hF'W0 (by rwa [Submodule.mem_bot]) hF'hw.1
      (fun a b h => by rw [hF'hw.2 a b h]; exact Submodule.zero_mem _)
    have hv0 : v ≠ 0 := fun h => hvU (h ▸ U.zero_mem)
    have hle : Dle μ la' := by
      by_contra hn'
      apply hv0; rw [← hvw]; exact (hwts v hvW).1 μ hn'
    by_cases hμ : μ = la'
    · subst hμ
      apply hvU
      have h2 := (hwts v hvW).2
      rw [hvw] at h2
      exact hVU ((Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (G.subset_gS _ (Set.mem_singleton F')))) h2)
    · exact absurd hc (ne_of_lt (cas_lt hdμ hdla' hle hμ)))
  set P := G.cprod cs with hPdef
  have hCasF' : G.Cas F' = ((GlW.casI la' : ℤ) : ℚ_[p]) • F' := G.Cas_gS hF'hw (G.subset_gS _ (Set.mem_singleton F'))
  have hPF' : P F' = (cs.map (fun c => (((GlW.casI la' - c : ℤ)) : ℚ_[p]))).prod • F' := cprod_eig G hCasF' cs
  have hκ : (cs.map (fun c => (((GlW.casI la' - c : ℤ)) : ℚ_[p]))).prod ≠ 0 := cprod_ne (V := ℚ_[p]) _ cs hcs
  set Φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    P ∘ₗ LinearMap.mulLeft ℚ_[p] eta with hΦdef
  have hΦapp : ∀ x, Φ x = P (eta * x) := fun x => rfl
  have hEeta : ∀ a b : Fin r, a < b → glAct p LL (T.pos i + 1 + 1) a b eta = 0 := by
    intro a b hab
    apply glAct_pow_zero
    rw [glAct_X_gen, if_pos hiKlt, hvK]
    simp [Ne.symm (hρa a b hab)]
  have hΦE : ∀ x ∈ G.gS {F}, ∀ a b, a < b → Φ (G.E a b x) = G.E a b (Φ x) := by
    intro x _ a b hab
    rw [hΦapp, hΦapp, G.E_cprod]
    congr 1
    show eta * glAct p LL (T.pos i + 1 + 1) a b x = glAct p LL (T.pos i + 1 + 1) a b (eta * x)
    rw [Formalism.GM.M.FB.glAct_mul, hEeta a b hab, mul_zero, add_zero]
  have hetawv := eta_wv (p := p) LL (T.pos i + 1 + 1) iK hiKlt hvK ρ u
  have hΦc : ∀ x ∈ G.gS {F}, ∀ ν, Φ (G.comp ν x) = G.comp (ν + (-(u : ℤ) • Pi.single ρ 1)) (Φ x) := by
    intro x _ ν
    rw [hΦapp, hΦapp, G.comp_cprod]
    congr 1
    exact (comp_mul_hom (wv LL _) hetawv ν x).symm
  have hΦv : Φ F ≠ 0 := by rw [hΦapp, ← hstep, hPF']; exact smul_ne_zero hκ hF'0
  have hinjF := G.inj_of hFhw (pol_stable LL L0 _) (pol_finW L0 _) hFpol Φ _ hΦE hΦc hΦv
  have hΦg : ∀ g ∈ G.gS {F}, Φ g ∈ G.gS {F'} := by
    intro g hg
    rw [hΦapp]
    apply hP
    rw [mul_comm]; exact Submodule.subset_span ⟨g, hg, eta, hetaHu, rfl⟩
  have hΦB : ∀ y q : MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < T.pos i + 1 + 1 → m v = 0) → Φ (y * q) = Φ y * q := by
    intro y q hq
    rw [hΦapp, hΦapp, ← mul_assoc]
    exact cprod_mul_B LL _ cs _ q hq
  have hBsupp : ∀ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)},
      ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < T.pos i + 1 + 1 → m v = 0 := by
    intro q hq m hm v hv
    by_contra hne
    have := supp_of_supported hq m hm v hne
    simp only [Set.mem_setOf_eq] at this
    omega
  have hspan : ∀ z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T n) (T.pos i + 2) F,
        ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q},
      Φ z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T nU) (T.pos i + 2)
        (T.Ffull p (LL.setTies T nU) i ρ (nU i) f),
        ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q} := by
    intro z hz
    rw [hnUi]
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, q, hq, rfl⟩ := hx
      rw [hΦB g q (hBsupp q hq)]
      refine Submodule.subset_span ⟨Φ g, ?_, q, hq, rfl⟩
      rw [gSpan_eq]; rw [gSpan_eq] at hg; exact hΦg g hg
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hmaps : ∀ z ∈ T.YYsp p LL i ρ n f, Φ z ∈ T.YYsp p LL i ρ nU f := by
    intro z hz
    obtain ⟨hzY, hzS⟩ := Submodule.mem_inf.mp hz
    have hzS' := hspan z hzS
    refine Submodule.mem_inf.mpr ⟨?_, hzS'⟩
    obtain ⟨hzP, hzC⟩ := Submodule.mem_inf.mp hzY
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hΦapp]
      refine G.cprod_mem (pol_stable LL _ _) cs ?_
      exact pol_eta LL T hadm i n n' hn ρ (LL.setTies T n) (LL.setTies T nU)
        (fun b hb => setTies_deg_ne LL T hadm i n n' b hb)
        (fun b hb => by
          have hb' : b = iK := Fin.ext hb
          subst hb'
          exact ⟨setTies_deg_eta LL T hadm i n hiKN, by rw [setTies_deg_eta LL T hadm i nU hiKN, hnUi]⟩) hzP
    · rw [Submodule.mem_iInf]; intro k
      have hzk : z ∈ YCond p LL (T.J k) (T.thr k) := (Submodule.mem_iInf _).mp hzC k
      show Φ z ∈ YCond p LL (T.J k) (T.thr k)
      by_cases hk : T.J k ≤ T.pos i + 1
      · have hF'Y : F' ∈ YCond p LL (T.J k) (T.thr k) := by
          have := Ffull_ycond LL T hadm i ρ nU w f hfU hSU k hk
          rw [hnUi] at this; exact this
        have hle : Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T nU) (T.pos i + 2)
            (T.Ffull p (LL.setTies T nU) i ρ (nU i) f),
            ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q} ≤
            YCond p LL (T.J k) (T.thr k) := by
          rw [Submodule.span_le]
          rintro _ ⟨g, hg, q, hq, rfl⟩
          rw [hnUi, gSpan_eq] at hg
          have hgY : g ∈ YCond p LL (T.J k) (T.thr k) :=
            (G.gS_le (by simpa using hF'Y) (fun a b x hx => ycond_glAct_le LL (by omega : T.J k ≤ T.pos i + 1 + 1) _ a b hx)) hg
          rw [SetLike.mem_coe, mul_comm]
          exact ycond_mul_B LL (by omega : T.J k ≤ T.pos i + 1 + 1) _ (hBsupp q hq) g hgY
        exact hle hzS'
      · push Not at hk
        rw [hΦapp]
        refine ycond_cprod LL (by omega : T.pos i + 1 + 1 ≤ T.J k) _ cs ?_
        exact ycond_mul_cov LL (T.J k) (T.thr k) iK (by simp only [hiK]; omega) hvK (eta_wOut iK ρ u) z hzk
  have hinjY : ∀ z ∈ T.YYsp p LL i ρ n f, Φ z = 0 → z = 0 := by
    intro z hz h0
    have hzS := (Submodule.mem_inf.mp hz).2
    simp only [gSpan_eq] at hzS
    obtain ⟨s, a, hs, ha, rfl⟩ := rep_span (G.gS {F}) (T.pos i + 1 + 1) hzS
    have hsum : ∑ b ∈ s, Φ (a b) * monomial b 1 = 0 := by
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [hΦB _ _ ?_]
      intro m hm v hv
      rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
      subst hm; exact hs _ hb v hv
    have hA : ∀ b ∈ s, ∀ m ∈ (Φ (a b)).support, ∀ v : Fin N × Fin r, T.pos i + 1 + 1 ≤ (v.1 : ℕ) → m v = 0 := by
      intro b _ m hm v hv
      have hp := hW0pol (hVF'W0 (hΦg (a b) (ha b)))
      have h1 := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hp hm v.1
      have h2 : L1.deg v.1 = 0 := by simp only [hL1, Lz]; rw [if_neg (by omega)]
      rw [h2] at h1
      exact (Finset.sum_eq_zero_iff.mp h1) v.2 (Finset.mem_univ _)
    have hz0 := indep_B (T.pos i + 1 + 1) s (fun b => Φ (a b)) hs hA hsum
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [hinjF (a b) (ha b) (hz0 b hb), zero_mul]
  haveI : FiniteDimensional ℚ_[p] (Pol p r (LL.setTies T nU)) := pol_fd _
  haveI : FiniteDimensional ℚ_[p] (T.YYsp p LL i ρ nU f) :=
    Submodule.finiteDimensional_of_le (le_trans inf_le_left inf_le_left)
  let Φ' : (T.YYsp p LL i ρ n f) →ₗ[ℚ_[p]] (T.YYsp p LL i ρ nU f) :=
    (Φ.domRestrict _).codRestrict _ (fun z => hmaps z z.2)
  apply LinearMap.finrank_le_finrank_of_injective (f := Φ')
  intro z1 z2 h12
  have h3 : Φ (z1 - z2) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr (congrArg Subtype.val h12)
  have := hinjY _ (Submodule.sub_mem _ z1.2 z2.2) h3
  exact Subtype.ext (sub_eq_zero.mp this)
end Formalism.GM.DimensionMonotonicity
