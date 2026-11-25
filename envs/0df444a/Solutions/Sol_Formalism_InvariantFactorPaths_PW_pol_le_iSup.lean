-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.pol_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:49.567697+00:00
-- url     : https://prove2.me/submissions/762caed7-0718-4ad3-b8f2-689b5263ef99

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_iSup_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_antisymm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_raise
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_trans
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_cprod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_bot_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_cons
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_raising_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cas_lt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_eig
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_ne
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_dl_ne_zero
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_finW
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_eq
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
namespace Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
section perp
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end perp
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
private theorem cprod_sub_prod_smul_mem_of_cas_sub_smul_mem {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
    (G : GlW K V n) {U : Submodule K V} (hU : G.Stable U) {v : V} {c0 : ℤ}
    (hv : G.Cas v - ((c0 : ℤ) : K) • v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v ∈ U := by
  induction cs with
  | nil =>
    simp only [List.map_nil, List.prod_nil, one_smul]
    rw [show G.cprod [] v = v from rfl, sub_self]
    exact U.zero_mem
  | cons c cs ih =>
    have key : G.cprod (c :: cs) v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) (c :: cs)).prod • v
        = (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • (G.Cas v - ((c0 : ℤ) : K) • v)
          + (G.Cas (G.cprod cs v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v)
            - ((c : ℤ) : K) • (G.cprod cs v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v)) := by
      rw [G.cprod_cons, List.map_cons, List.prod_cons, map_sub, map_smul]
      push_cast
      module
    rw [key]
    exact U.add_mem (U.smul_mem _ hv) (U.sub_mem (G.Cas_mem hU ih) (U.smul_mem _ ih))
private theorem le_iSup_gS_highestWeight_of_stable_of_finW {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
    (G : GlW K V n) (W : Submodule K V) (hW : G.Stable W) (hF : G.FinW W) :
    W ≤ ⨆ i : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h}, G.gS {i.1} := by
  set S := ⨆ i : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h}, G.gS {i.1} with hS
  have hSst : G.Stable S := CountingSumsFrames.GlX.iSup_stable G (fun i => G.gS_stable _)
  by_contra hWS
  obtain ⟨v, hvW, hvS, μ, hvμ, hraise⟩ :=
    G.exists_hwmod (G.graded_of hW) (G.raising_of hW) hF hWS
  have hdomμ : DomW μ := G.dom_of_hwmod hSst hW hF hvW hvS hvμ hraise
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = GlW.casI μ := ⟨_, rfl⟩
  have hCas : G.Cas v - ((c0 : ℤ) : K) • v ∈ S := by
    rw [hc0]
    exact G.Cas_hwmod hSst hvμ hraise
  have hdec : ∀ a b : Fin n, ∃ f : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h} →₀ V,
      (∀ i, f i ∈ G.gS {i.1}) ∧ (a < b → (f.sum fun _ x => x) = G.E a b v) := by
    intro a b
    by_cases hab : a < b
    · obtain ⟨f, hf1, hf2⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp (hraise a b hab)
      exact ⟨f, hf1, fun _ => hf2⟩
    · exact ⟨0, fun i => by simp, fun h => absurd h hab⟩
  choose f hf1 hf2 using hdec
  obtain ⟨cs, hcs⟩ : ∃ cs : List ℤ, cs = ((Finset.univ.biUnion fun a => Finset.univ.biUnion fun b =>
      (f a b).support.image fun i => GlW.casI i.2.2.2.choose).filter (fun c => c ≠ c0)).toList := ⟨_, rfl⟩
  have hcs_ne : ∀ c ∈ cs, c ≠ c0 := by
    intro c hc
    rw [hcs, Finset.mem_toList, Finset.mem_filter] at hc
    exact hc.2
  have hcs_mem : ∀ a b i, i ∈ (f a b).support → GlW.casI i.2.2.2.choose ≠ c0 →
      GlW.casI i.2.2.2.choose ∈ cs := by
    intro a b i hi hne
    rw [hcs, Finset.mem_toList, Finset.mem_filter]
    refine ⟨?_, hne⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨a, b, i, hi, rfl⟩
  have hP : (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod ≠ 0 :=
    cprod_ne (K := K) (V := V) c0 cs hcs_ne
  have hmod := cprod_sub_prod_smul_mem_of_cas_sub_smul_mem G hSst hCas cs
  have hv2mod : G.comp μ (G.cprod cs v) - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v ∈ S := by
    have h := G.graded_of hSst μ _ hmod
    rwa [map_sub, map_smul, show G.comp μ v = v from hvμ] at h
  have hv2W : G.comp μ (G.cprod cs v) ∈ W := G.graded_of hW μ _ (G.cprod_mem hW cs hvW)
  have hv2wt : G.IsWt μ (G.comp μ (G.cprod cs v)) := by
    show G.comp μ (G.comp μ _) = _
    rw [G.idem, if_pos rfl]
  have hv2hw : ∀ a b, a < b → G.E a b (G.comp μ (G.cprod cs v)) = 0 := by
    intro a b hab
    have hsh := G.shift a b (μ + dl a b) (G.cprod cs v)
    rw [add_sub_cancel_right] at hsh
    rw [← hsh, G.E_cprod, ← hf2 a b hab, Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi1 := hf1 a b i
    have hCasi : G.Cas (f a b i) = ((GlW.casI i.2.2.2.choose : ℤ) : K) • f a b i :=
      G.Cas_gS i.2.2.2.choose_spec hi1
    rw [cprod_eig G hCasi cs]
    by_cases hc : GlW.casI i.2.2.2.choose = c0
    · have hz : G.comp (μ + dl a b) (f a b i) = 0 := by
        by_contra hne0
        have hle := G.wt_le_of_mem i.2.2.2.choose_spec hi1 hne0
        have hdomν : DomW i.2.2.2.choose :=
          G.dom_of_hwmod G.bot_stable hW hF i.2.1 (by simpa using i.2.2.1) i.2.2.2.choose_spec.1
            (fun a' b' hab' => by rw [i.2.2.2.choose_spec.2 a' b' hab']; exact Submodule.zero_mem _)
        have hμν : Dle μ i.2.2.2.choose := Dle_trans (Dle_raise μ hab) hle
        have hneμ : μ ≠ i.2.2.2.choose := by
          intro heq
          rw [← heq] at hle
          have h2 := Dle_antisymm hle (Dle_raise μ hab)
          exact dl_ne_zero (ne_of_lt hab) (by simpa using h2)
        have hlt := cas_lt hdomμ hdomν hμν hneμ
        rw [hc, ← hc0] at hlt
        exact lt_irrefl _ hlt
      rw [map_smul, hz, smul_zero]
    · have hmem := hcs_mem a b i hi hc
      rw [List.prod_eq_zero (List.mem_map.mpr ⟨_, hmem, by simp⟩), zero_smul, map_zero]
  have hv2S : G.comp μ (G.cprod cs v) ∈ S := by
    by_cases h0 : G.comp μ (G.cprod cs v) = 0
    · rw [h0]
      exact S.zero_mem
    · exact Submodule.mem_iSup_of_mem
        (⟨_, hv2W, h0, μ, hv2wt, hv2hw⟩ : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h})
        (G.subset_gS _ (Set.mem_singleton _))
  have hPv := S.sub_mem hv2S hv2mod
  rw [sub_sub_cancel] at hPv
  exact hvS ((Submodule.smul_mem_iff _ hP).mp hPv)
end Formalism.InvariantFactorPaths.PW
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    Pol p r L2 ≤ ⨆ la : Fin r → ℤ, IsoC p LL j Cs la := by
  have hW := GAe_pol_stable (p := p) LL L2 j (enumC Cs)
  have hF := GAe_pol_finW (p := p) LL L2 j (enumC Cs)
  refine le_trans (le_iSup_gS_highestWeight_of_stable_of_finW (GAe p LL j (enumC Cs)) (Pol p r L2) hW hF) ?_
  refine iSup_le fun i => ?_
  refine le_iSup_of_le (Function.extend (⇑(enumC Cs)) i.2.2.2.choose 0) ?_
  rw [isoC_eq]
  have hcomp : Function.extend (⇑(enumC Cs)) i.2.2.2.choose 0 ∘ ⇑(enumC Cs) = i.2.2.2.choose := by
    funext a
    exact (enumC Cs).injective.extend_apply _ _ a
  rw [hcomp]
  refine (GAe p LL j (enumC Cs)).gS_le ?_ ((GAe p LL j (enumC Cs)).gS_stable _)
  rw [Set.singleton_subset_iff]
  exact (GAe p LL j (enumC Cs)).subset_gS _ i.2.2.2.choose_spec
end Formalism.InvariantFactorPaths.PW
