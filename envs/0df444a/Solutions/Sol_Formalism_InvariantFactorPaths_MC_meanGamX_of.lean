-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.meanGamX_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:55.230896+00:00
-- url     : https://prove2.me/submissions/4eea082b-94ca-4ecb-bd14-88e739b91cd5

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMXB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_NatLogLeOfLe
import Theorems.Thm_Formalism_InvariantFactorPaths_MC_per_rowX
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
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_betaT_ne_zero
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_binMatK_map
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_lead_bound
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_lead_part
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_split_det
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_splits_form
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC
open Polynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.MC
theorem _root_.solution (hDeg : GamDeg) (hLead : GamLead) (hC : GamIntC) (hW : Formalism.GM.WindowFullAP) :
    MeanGamX := by
  intro p hp K r hr LLw q J M ρ z w n₀ f ord s d Yw Xb E κ κ4 lgv U V dg hρ hr2 hv hli hspan hord hfil hE hYw hd
    hcop hSs h2S hzo hYX hrX hL hκ hL4 hsmith
  classical
  have hr1 : 1 ≤ r := by omega
  have hmem : ∀ b, f b ∈ MMwZ p LLw J M ρ w := fun b => hspan ▸ Submodule.subset_span ⟨b, rfl⟩
  have hPol : ∀ b, f b ∈ Pol p r LLw := fun b =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
      (Submodule.mem_inf.mp (hmem b)).1).1).1).1
  have hPolZ : ∀ b, f b ∈ PolZ p r LLw := fun b =>
    Submodule.mem_inf.mpr ⟨hPol b, (Submodule.mem_inf.mp (hmem b)).2⟩
  have hCI := fun x y => hC p K r LLw ρ z (f x) (f y) hr1 hv (hPolZ x) (hPolZ y)
  choose cc hcc using hCI
  set S := LLw.total with hSdef
  set o := LLw.deg (Fin.last K) with hodef
  set cI := (K + 4) * (r * Nat.log p (S + o + r)) + 6 * Nat.log p (S + o + r) with hcIdef

  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlgv1 : 1 ≤ lgv := by
    have : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    linarith
  have hκ0 : 0 ≤ κ := by
    refine le_trans ?_ hκ
    positivity
  have hoS0 : o ≤ S := Finset.single_le_sum (f := LLw.deg) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hS2a : S ≤ Xb := by omega
  have ho2a : o ≤ Xb := by omega
  have hcI : (cI : ℝ) ≤ κ := by
    have hX1 : Xb ≠ 0 := by omega
    have hl : Nat.log p (S + o + r) ≤ Nat.log p Xb + 1 := by
      rw [← Nat.log_mul_base hp.out.one_lt hX1]
      apply Nat.log_mono_right
      have : 2 ≤ p := hp.out.two_le
      nlinarith
    have hl' : (Nat.log p (S + o + r) : ℝ) ≤ lgv := by
      have : (Nat.log p (S + o + r) : ℝ) ≤ (Nat.log p Xb : ℝ) + 1 := by exact_mod_cast hl
      linarith
    have hK0 : (0 : ℝ) ≤ ((K : ℝ) + 4) * (r : ℝ) + 6 := by positivity
    calc (cI : ℝ) = (((K : ℝ) + 4) * (r : ℝ) + 6) * (Nat.log p (S + o + r) : ℝ) := by
          rw [hcIdef]; push_cast; ring
      _ ≤ (((K : ℝ) + 4) * (r : ℝ) + 6) * lgv := mul_le_mul_of_nonneg_left hl' hK0
      _ ≤ κ := hκ
  have hcIc : cI ≤ ⌈κ⌉₊ := by
    have : (cI : ℝ) ≤ (⌈κ⌉₊ : ℝ) := hcI.trans (Nat.le_ceil κ)
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + cI = ⌈κ⌉₊ := ⟨⌈κ⌉₊ - cI, Nat.sub_add_cancel hcIc⟩
  obtain ⟨hAeval, hnat, hlead, hord_le, hoS⟩ := lead_part hDeg hLead LLw J M ρ z w n₀ f ord κ4 m cI cc
    hr1 hv hli hspan hord hfil hL4 (fun x y n hn => hcc x y n hn)
  set Aq := binMatK ℚ_[p] (2 * S) (coefT p (S + o) m cc) with hAqdef
  have hLB := lead_bound p (fun b => ‖betaT p (m + cI) z o S (ord b)‖) (fun b => S + o - ord b) κ4
    (κ + 3 * lgv + κ4) ‖Aq.det.leadingCoeff‖ (fun b => norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) hlead
    (fun b => per_rowX p Xb S o z (ord b) (m + cI) κ κ4 lgv (hord_le b) ho2a hS2a hzo hL hκ0 hm)

  set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg
  set c' : Fin n₀ → Fin n₀ → ℕ → PadicAlgCl p := fun i j k => alg (coefT p (S + o) m cc i j k) with hc'
  have hAK : binMatK (PadicAlgCl p) (2 * S) c' = Aq.map (Polynomial.map alg) :=
    binMatK_map ℚ_[p] (PadicAlgCl p) alg (2 * S) _
  have hDk : (binMatK (PadicAlgCl p) (2 * S) c').det = Aq.det.map alg := by
    rw [hAK]; exact split_det p Aq
  obtain ⟨hsplit, hcard⟩ := splits_form (binMatK (PadicAlgCl p) (2 * S) c').det
  have hlc : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff = alg Aq.det.leadingCoeff := by
    rw [hDk, leadingCoeff_map]
  have hnd : (binMatK (PadicAlgCl p) (2 * S) c').det.natDegree = Aq.det.natDegree := by
    rw [hDk, natDegree_map]
  have hlcnorm : ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖ := by
    rw [hlc, halg, norm_algebraMap']
  have hprod_pos : 0 < ∏ b, (‖betaT p (m + cI) z o S (ord b)‖ * (p : ℝ) ^ (-κ4)) := by
    apply Finset.prod_pos
    intro b _
    exact mul_pos (norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) (Real.rpow_pos_of_pos (by linarith) _)
  have hleadne : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff ≠ 0 := by
    rw [← norm_pos_iff, hlcnorm]; exact lt_of_lt_of_le hprod_pos hlead
  have hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ +
      ((binMatK (PadicAlgCl p) (2 * S) c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * (κ + 3 * lgv + κ4) := by
    rw [hlcnorm, hcard, hnd, hnat]; exact hLB
  have hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1 := by
    intro i j k
    simp only [hc', halg, norm_algebraMap', coefT]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := by
        rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _
      have h2 : ((p : ℝ)⁻¹) ^ m ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
      calc ((p : ℝ)⁻¹) ^ m * ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 * 1 :=
            mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · simp

  set h := Nat.log p Xb + 1 with hhdef
  have hph : Xb ≤ p ^ h := (Nat.lt_pow_succ_log_self hp.out.one_lt Xb).le
  have hhl : (h : ℝ) ≤ lgv := by rw [hhdef]; push_cast; exact hL
  have hYh : Yw ≤ p ^ h := by omega
  have hdelh : 2 * S ≤ p ^ h := by omega

  set idx : ℤ → ℕ := fun t => ((t - (s : ℤ)) / (d : ℤ)).toNat with hidxdef
  have hidx : ∀ j : ℕ, idx (progr (s : ℤ) (d : ℤ) j) = j := by
    intro j
    simp only [hidxdef, progr, add_sub_cancel_left]
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hd.ne')]
    simp
  set U' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (U (idx t)).map alg with hU'
  set V' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (V (idx t)).map alg with hV'
  set dg' : ℤ → Fin n₀ → PadicAlgCl p := fun t b => alg (dg (idx t) b) with hdg'
  have hsm : ∀ j ∈ range Yw, (∀ x y, ‖U' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      (∀ x y, ‖V' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      ‖(U' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧ ‖(V' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧
      (binMatK (PadicAlgCl p) (2 * S) c').map (Polynomial.eval ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p)) =
        U' (progr (s : ℤ) (d : ℤ) j) * Matrix.diagonal (dg' (progr (s : ℤ) (d : ℤ) j)) *
          V' (progr (s : ℤ) (d : ℤ) j) := by
    intro j hj
    obtain ⟨hU1, hV1, hUd, hVd, hfac⟩ := hsmith j (Finset.mem_range.mp hj)
    simp only [hU', hV', hdg', hidx]
    refine ⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hU1 x y
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hV1 x y
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hUd
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hVd
    · rw [hAK]
      ext x y
      have hpt : ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p) = ((s + d * j : ℕ) : PadicAlgCl p) := by
        simp [progr]
      have hfe := congrFun (congrFun hfac x) y
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_diagonal] at hfe
      simp only [Matrix.map_apply, hpt, eval_natCast_map, Matrix.mul_apply, Matrix.mul_diagonal]
      rw [hAeval x y (s + d * j) (le_trans hSs (Nat.le_add_right _ _)), hm, hfe, map_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp [Matrix.diagonal_apply, map_sum]
  have hcop' : IsCoprime (d : ℤ) (p : ℤ) := hcop
  have hE0 : (0 : ℝ) < E := by linarith
  have key := hW p (PadicAlgCl p) n₀ (2 * S) h E c' (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff
    (binMatK (PadicAlgCl p) (2 * S) c').det.roots (s : ℤ) (d : ℤ) Yw (κ + 3 * lgv + κ4) U' V' dg' hcop'
    (by omega) hYh hdelh hE0 hleadne hc'norm hsplit hsm hLB'

  have hcnt : ∀ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ) ≤
      ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) := by
    intro j _
    have hsub : univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E)) ⊆
        univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E)) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp only [hdg', hidx, halg, norm_algebraMap']
      exact hb.le
    exact_mod_cast Finset.card_le_card hsub
  have hYpos : (0 : ℝ) < Yw := by exact_mod_cast hYw
  calc (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw
      ≤ (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) /
          Yw := div_le_div_of_nonneg_right (Finset.sum_le_sum hcnt) hYpos.le
    _ ≤ (n₀ : ℝ) * (((2 * S : ℕ) : ℝ) / Yw + ((κ + 3 * lgv + κ4) + ((2 * S : ℕ) : ℝ) * h / Yw) / E) := key
    _ ≤ n₀ * (2 * (LLw.total : ℝ) / Yw + ((κ + 3 * lgv + κ4) + 2 * (LLw.total : ℝ) * lgv / Yw) / E) := by
      rw [← hSdef]
      push_cast
      have h1 : 2 * (S : ℝ) * h / Yw ≤ 2 * (S : ℝ) * lgv / Yw := by
        apply div_le_div_of_nonneg_right _ hYpos.le
        exact mul_le_mul_of_nonneg_left hhl (by positivity)
      have h2 : (κ + 3 * lgv + κ4) + 2 * (S : ℝ) * h / Yw ≤ (κ + 3 * lgv + κ4) + 2 * (S : ℝ) * lgv / Yw := by
        linarith
      have h3 := div_le_div_of_nonneg_right h2 hE0.le
      have hn0 : (0 : ℝ) ≤ n₀ := by positivity
      nlinarith
end Formalism.InvariantFactorPaths.MC
