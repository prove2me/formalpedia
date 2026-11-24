-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sz_sizesMain_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:40.431065+00:00
-- url     : https://prove2.me/submissions/6b57999a-b5bb-44ab-a0a4-1c5211f0d731

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_small_f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_vand_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_vand_word_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_sfac_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_tcrit_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_beta_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_sfac_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz9
set_option maxHeartbeats 1000000
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hCorA : CorA) (hBeta : BetaOnCut) (hAZ : AZeroBound)
    (hIL : Interlacing) (hLA : LamAnti) (hTP : ThresholdProducts) (hTL : ThetaLower) (hThP : ThetaPower)
    (hFS : FinalSmall) : SizesMain := by
  intro CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTCb
  have hc : 0 < cExp CDel cT Cb := by
    unfold cExp
    have : 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := lt_min (by linarith) (by linarith)
    positivity
  obtain ⟨Ct, hCt⟩ : ∃ Ct : ℝ, Ct = 2 * C0 * Real.exp (1 / 4) := ⟨_, rfl⟩
  have hCt1 : 1 ≤ Ct := by
    have : 1 ≤ Real.exp (1 / 4) := Real.one_le_exp (by norm_num)
    rw [hCt]; nlinarith
  obtain ⟨k1, hk1⟩ := hThP CA 160 Ct CDel cT Cb hCA (by norm_num) hCt1 hCDel hcT hCb hcTCb
  obtain ⟨k2, hk2⟩ := hFS CA (cExp CDel cT Cb) hCA hc
  refine ⟨max 7 (max k1 k2), ?_⟩
  intro ι _ G bb C' Cf Th de de' T T' du du' l hk H hde hde' hl1 hl2 hdl hT hT' hC' hkbig hMR hLB
    hCC hCC' hCh hCh' hFD hTh hGr
  have hk7 : 7 ≤ G.k := le_trans (le_max_left _ _) hk
  have hkk1 : k1 ≤ G.k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkk2 : k2 ≤ G.k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hkR : (7 : ℝ) ≤ G.k := by exact_mod_cast hk7
  have hm2 : 2 ≤ G.m := by unfold Glob.m; omega
  have hf2 : 2 ≤ G.f := le_trans hm2 H.hmf
  have hbb := H.hbb
  have hv := H.hv
  have hpi := Real.pi_pos
  have hne : Nonempty ι := by
    have : 0 < Fintype.card ι := lt_of_lt_of_le (by norm_num) hf2
    exact Fintype.card_pos_iff.1 this
  obtain ⟨w0⟩ := hne

  have hbbk : (G.k : ℝ) ^ (Cb / 2) ≤ bb := by
    have h1 : (G.k : ℝ) ^ Cb ≤ G.b w0 1 := H.hnode w0 1 le_rfl (by omega)
    have h2 : G.b w0 1 ≤ bb ^ 2 := (H.hsmall w0).hbj 1 le_rfl (by show 1 ≤ 2 * G.r + 2; omega)
    have h3 : ((G.k : ℝ) ^ (Cb / 2)) ^ 2 = (G.k : ℝ) ^ Cb := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast; ring
    have h4 : ((G.k : ℝ) ^ (Cb / 2)) ^ 2 ≤ bb ^ 2 := by rw [h3]; exact h1.trans h2
    exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).1 h4
  have hpw : 1 < bb ^ (cT * (G.m : ℝ)) := by
    apply Real.one_lt_rpow hbb
    have : (0 : ℝ) < G.m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm2)
    positivity
  have hTR : (1 : ℝ) < T := lt_of_lt_of_le hpw hT
  have hTR' : (1 : ℝ) < T' := lt_of_lt_of_le hpw hT'
  have hT2 : 2 ≤ T := by
    have : 1 < T := by exact_mod_cast hTR
    omega
  have hT2' : 2 ≤ T' := by
    have : 1 < T' := by exact_mod_cast hTR'
    omega
  have hTT : (bb ^ (cT * (G.m : ℝ))) ^ 2 ≤ (T : ℝ) * T' := by
    rw [sq]
    exact mul_le_mul hT hT' (by linarith) (by linarith)
  have hTTpos : (0 : ℝ) < (T : ℝ) * T' := mul_pos (by linarith) (by linarith)
  have hNm : G.N = 10 * (G.m : ℝ) := by
    unfold Glob.N Glob.m; push_cast; ring
  have hN20 : 20 ≤ G.N := by
    unfold Glob.N
    have : (0 : ℝ) ≤ G.r := Nat.cast_nonneg _
    linarith
  have hN : 0 < G.N := by linarith
  obtain ⟨hCpi, hmin⟩ := hk1 G.k G.m G.f bb G.N G.lenI G.Del ((T : ℝ) * T') hkk1 hm2 H.hmf H.hfk
    hNm rfl hbbk H.hDel hTT
  have hkc1 : 1 ≤ (G.k : ℝ) ^ cExp CDel cT Cb := Real.one_le_rpow (by linarith) hc.le

  have hDelBig : 160 ^ 2 * ((G.k : ℝ) * G.N ^ 3) ≤ G.Del := by
    have h1 : (G.k : ℝ) ^ cExp CDel cT Cb ≤
        Real.sqrt (G.Del / (G.k * G.N ^ 3)) / (Ct * CA * 160) :=
      le_trans hmin (le_trans (min_le_left _ _) (min_le_left _ _))
    have hpos : 0 < Ct * CA * 160 := by positivity
    have h2 : Ct * CA * 160 ≤ Real.sqrt (G.Del / (G.k * G.N ^ 3)) := by
      have := (le_div_iff₀ hpos).1 (le_trans hkc1 h1)
      linarith
    have h3 : (160 : ℝ) ≤ Real.sqrt (G.Del / (G.k * G.N ^ 3)) := by
      have : 1 ≤ Ct * CA := one_le_mul_of_one_le_of_one_le hCt1 hCA
      linarith
    have h4 := (Real.le_sqrt' (by norm_num : (0 : ℝ) < 160)).1 h3
    have hkN : 0 < (G.k : ℝ) * G.N ^ 3 := by positivity
    exact (le_div_iff₀ hkN).1 h4
  have hN3 : 1 ≤ G.N ^ 3 := one_le_pow₀ (by linarith)
  have hkN3 : G.N ^ 3 ≤ (G.k : ℝ) * G.N ^ 3 := le_mul_of_one_le_left (by linarith) (by linarith)
  have hN3Del : G.N ^ 3 ≤ G.Del / 2 := by linarith
  have hDelpos : 0 < G.Del := by linarith
  have hI : 0 < G.lenI := by unfold Glob.lenI; linarith

  have hkb : (4 : ℝ) ≤ ((G.k : ℝ) * bb) ^ 8 := by
    have h1 : (4 : ℝ) ≤ (G.k : ℝ) * bb := by
      have := mul_le_mul hkR hbb.le zero_le_one (by linarith)
      linarith
    exact le_trans h1 (le_self_pow₀ (by linarith) (by norm_num))
  have hg1R : (4 : ℝ) ≤ G.g1 := le_trans hkb H.hg1
  have hg2R : (4 : ℝ) ≤ G.g2 := le_trans hkb H.hg2
  have hg1N : 4 ≤ G.g1 := by exact_mod_cast hg1R
  have hg2N : 4 ≤ G.g2 := by exact_mod_cast hg2R
  have hg16 : 16 ≤ G.g := by
    have := mul_le_mul hg1R hg2R (by norm_num) (by linarith)
    unfold Glob.g; linarith
  have h2pig : 2 * Real.pi ≤ G.g := by linarith [Real.pi_le_four]
  have hgpos : 0 < G.g := by linarith
  have hka : G.ka = 2 * Real.pi / (2 * G.v) := by
    unfold Glob.ka; field_simp
  have hkapos : 0 < G.ka := by unfold Glob.ka; positivity
  have hkapi : G.ka ≤ Real.pi := by
    unfold Glob.ka
    exact div_le_self hpi.le hv

  have hVu : ∀ w, 0 < Vand G.k ((G.place w).u de) := fun w =>
    vand_word_pos hIL (G.place w) de (H.hplace w) hde
  have hVu' : ∀ w, 0 < Vand G.k ((G.place w).u de') := fun w =>
    vand_word_pos hIL (G.place w) de' (H.hplace w) hde'
  have hVV : ∀ w, 0 < (G.size de T du).VV w := by
    intro w
    have h1 : 0 < Vand ((G.place w).k + (G.place w).m - 1) (G.place w).lam :=
      vand_pos _ _ (hLA (G.place w) (H.hplace w))
    have h2 := hFD w
    unfold FormalDegreeLower at h2
    linarith
  have hdsig : ∀ w, 0 < G.dsig w := by
    intro w
    have h1 : 0 < G.dsig w * (sfac (G.size de T du).n : ℝ) := hVV w
    have h2 : (0 : ℝ) < (sfac (G.size de T du).n : ℝ) := by exact_mod_cast sfac_pos _
    exact (mul_pos_iff_of_pos_right h2).1 h1

  have hsm := small_f G.f G.k H.hfk hk7
  have hlogbb : 0 ≤ Real.log bb := Real.log_nonneg hbb.le
  have hOkS : (G.size de T du).Ok :=
    ⟨(by omega : 1 ≤ G.k), (by linarith : 0 < G.v), H.hdF, (by omega : 2 ≤ G.g1),
      (by omega : 2 ≤ G.g2), hT2, H.hvol, hVu⟩
  have hOkS' : (G.size de' T' du').Ok :=
    ⟨(by omega : 1 ≤ G.k), (by linarith : 0 < G.v), H.hdF, (by omega : 2 ≤ G.g1),
      (by omega : 2 ≤ G.g2), hT2', H.hvol, hVu'⟩
  have hA := hCorA ι (G.size de T du) C0 CG C' (Real.log bb) hOkS hMR hLB hCC hdsig
    (by omega : 2 ≤ G.k) hg1N hg2N hC0 hCG hlogbb hC' hkbig hsm hCh
  have hA' := hCorA ι (G.size de' T' du') C0 CG C' (Real.log bb) hOkS' hMR hLB hCC' hdsig
    (by omega : 2 ≤ G.k) hg1N hg2N hC0 hCG hlogbb hC' hkbig hsm hCh'
  have hP : ∏ w, ((G.size de T du).Tcrit w / (T : ℝ)) ≤ Ct := by
    rw [hCt]; exact le_trans hA.2.1 hA.2.2
  have hP' : ∏ w, ((G.size de' T' du').Tcrit w / (T' : ℝ)) ≤ Ct := by
    rw [hCt]; exact le_trans hA'.2.1 hA'.2.2
  have hTc : ∀ w, 0 ≤ (G.size de T du).Tcrit w := fun w =>
    tcrit_nonneg _ _ _ _ _ _ _ hkapos (by show 0 < 2 * G.v; linarith) hgpos (hVV w) (hVu w)
  have hTc' : ∀ w, 0 ≤ (G.size de' T' du').Tcrit w := fun w =>
    tcrit_nonneg _ _ _ _ _ _ _ hkapos (by show 0 < 2 * G.v; linarith) hgpos (hVV w) (hVu' w)
  obtain ⟨t, ht⟩ : ∃ t : ι → ℝ, t = fun w =>
      tv (G.place w) de de' G.ka (2 * G.v) G.g ((G.size de T du).VV w) T T' := ⟨_, rfl⟩
  have ht0 : ∀ w, 0 ≤ t w := by
    intro w; rw [ht]; exact Real.sqrt_nonneg _
  have htsq : ∀ w, t w ^ 2 =
      ((G.size de T du).Tcrit w / (T : ℝ)) * ((G.size de' T' du').Tcrit w / (T' : ℝ)) := by
    intro w
    rw [ht]
    show (Real.sqrt ((G.size de T du).Tcrit w * (G.size de' T' du').Tcrit w /
      ((T : ℝ) * T'))) ^ 2 = _
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (hTc w) (hTc' w)) hTTpos.le), div_mul_div_comm]
  have htprod : ∏ w, t w ≤ Ct := by
    have h1 : (∏ w, t w) ^ 2 ≤ Ct ^ 2 := by
      rw [← prod_pow, prod_congr rfl (fun w _ => htsq w), prod_mul_distrib, sq]
      apply mul_le_mul hP hP' _ (by linarith)
      exact prod_nonneg fun w _ => div_nonneg (hTc' w) (by linarith)
    exact (pow_le_pow_iff_left₀ (prod_nonneg fun w _ => ht0 w) (by linarith) (by norm_num)).1 h1

  have hbd : ∀ (w : ι) (D : ℝ), D ≤ G.Del / 2 → ∀ Y : ℝ, 5 / 2 ≤ (G.place w).v l + Y →
      (G.place w).v l + Y ≤ D →
      0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y ∧
        G.g ^ G.m * (G.place w).be G.ka de de' T T' Y ≤
          160 * t w * Real.sqrt G.k * Real.sqrt (D / G.Del) := by
    intro w D hD Y hY1 hY2
    rw [ht]
    exact beta_bound hBeta hAZ (G.place w) G.r bb de de' G.ka (2 * G.v) G.g
      ((G.size de T du).VV w) T T' l (H.hplace w) rfl (H.hsmall w) hde hde' (by linarith) hka h2pig
      (hFD w) (by linarith) (by linarith) hl1 hl2 hdl D hD Y hY1 hY2
  have hB1 : ∀ w, 0 ≤ G.cutSupLong de de' T T' l w ∧ G.cutSupLong de de' T T' l w ≤
      160 * t w * Real.sqrt G.k * Real.sqrt (G.N ^ 3 / G.Del) := by
    intro w
    unfold Glob.cutSupLong
    constructor
    · apply Real.sSup_nonneg
      rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
      exact (hbd w _ hN3Del Y hY1 hY2).1
    · apply Real.sSup_le
      · rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
        exact (hbd w _ hN3Del Y hY1 hY2).2
      · have := ht0 w
        positivity
  have hB : ∀ w, 0 ≤ G.supI de de' T T' l w ∧ G.supI de de' T T' l w ≤
      160 * t w * Real.sqrt G.k := by
    intro w
    have hs1 : Real.sqrt (G.Del / 2 / G.Del) ≤ 1 := by
      apply Real.sqrt_le_one.2
      rw [div_le_one hDelpos]; linarith
    have h0 : 0 ≤ 160 * t w * Real.sqrt G.k := by
      have := ht0 w
      positivity
    unfold Glob.supI
    constructor
    · apply Real.sSup_nonneg
      rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
      exact (hbd w _ le_rfl Y hY1 hY2).1
    · apply Real.sSup_le
      · rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
        exact le_trans (hbd w _ le_rfl Y hY1 hY2).2 (mul_le_of_le_one_right h0 hs1)
      · exact h0

  have key := fun i s : ℕ => hTP ι t (G.cutSupLong de de' T T' l) (G.supI de de' T T' l) G.k CA 160 Ct
    G.ka G.N G.lenI G.g G.Del ((T : ℝ) * T') i s hCA (by norm_num) (by linarith) hkapos hkapi hN hI
    (by linarith) hDelpos hTTpos hCpi ht0 htprod hB1 hB
  have hTheta : (G.k : ℝ) ^ cExp CDel cT Cb ≤ Th := by
    refine le_trans hmin ?_
    apply hTL G.f G.k CA 160 Ct G.N G.lenI G.Del ((T : ℝ) * T') Th (by omega) (by omega) hCA
      (by norm_num) hCt1 hN hI hDelpos hTTpos hTh hCpi
    obtain ⟨i, hi1, hi2, hcase⟩ := hGr.1
    rcases hcase with ⟨_, hx⟩ | ⟨h2i, hx⟩ | ⟨s, hs2, _, hx⟩ | hx
    · left; rw [hx]; exact (key 1 1 le_rfl).1
    · right; left; rw [hx]; exact (key i 1 hi1).2.1 h2i
    · right; right; left; rw [hx]; exact (key i s hi1).2.2.1 hs2
    · right; right; right; rw [hx]; exact (key i 1 hi1).2.2.2
  refine ⟨hTheta, ?_⟩
  intro h16 hCf
  exact hk2 G.k G.r G.f bb Cf Th hkk2 H.hmf hbb.le h16 hCf hTheta
end Formalism.FourierDecayAlt.P
