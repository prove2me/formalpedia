-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_MainRow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:25.565885+00:00
-- url     : https://prove2.me/submissions/f2b9da9f-ef2e-4dd2-9a93-31099bc5b36a

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_jn_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : MainRow := by
  intro hLC hGC _hLL hAx h13s C₄ Cthr h4
  have hLC2 := hLC
  obtain ⟨hA, hSch, hPD, hDS, hDP, hBD, hPL, hSO, hPh, hOS, hOD, hLP, hUH, hTP, hTU, hGL, hUM, hAS,
    hAF, hKL, hLK, hDM, hDA, hA2, hKG, hN0, hN1P, hTh1, h1, hNsS, hNsB, hLA⟩ := hLC
  obtain ⟨hTA, hRW, hDST, hSBM, hRST, hDSum, hDL2, hDSz, hDC, hPT, hPJ, hPSJ, hBox, hLat, hId, hNorm,
    hDeg, hFP, hX, hLSJ, hIS, hILS, hSz, hSR, hGP, hMT, hFM⟩ := hGC
  have hLem : A5.LemmaA := hLA hA2 hN1P hTh1 h1 h13s hN0 hNsS hNsB
  have h13 : ∀ s, 1 ≤ s → A5.A13 s := hLem.2.1
  obtain ⟨C₁, hC1, hIL⟩ := hILS hLSJ hIS hBox hLat hId hNorm hDeg hFP hX
  obtain ⟨CT, CT', hT⟩ := hRW hTA C₁ C₄ hC1 h4
  refine ⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k1, hk1⟩ := hSR hSz (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT'
    (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _)
    (le_max_right _ _)
  obtain ⟨k3, hk3⟩ := hGP CDel Cb hCDel hCb
  refine ⟨max k1 k3, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf hU hInst hLM jn H _ _ _ Vt c
    sd hReal hDens P _ B hRows hMassData hEL
  obtain ⟨hI, he1, hδ⟩ := hEL
  obtain ⟨hg1, hg2, hlen⟩ := hk3 (InfinitePlace E) G bb (le_trans (le_max_right _ _) hk) hyp.1
  obtain ⟨s1, s2, s3, s4, s5⟩ := hk1 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l
    (le_trans (le_max_left _ _) hk) hyp h16 hCf
  have hGr : IsGreatest (G.thrSet (max (max Cthr 1) |CT|) de de' T T' l) ((Th ^ G.f)⁻¹) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hyp
    exact h
  have hCA0 : 0 ≤ max (max Cthr 1) |CT| := le_trans (abs_nonneg _) (le_max_right _ _)
  obtain ⟨hSB, hLS⟩ := hIL E W D e G _ de de' T T' l Th hU hInst hg1 hg2 hCA0 hlen s2 hGr
  have hf : D.f = G.f := by
    have := Fintype.card_congr e
    rw [Fintype.card_fin] at this
    exact this
  have hr : D.r = G.r := hInst.1
  have hf1 : 1 ≤ D.f := by
    obtain ⟨_, d2, d3⟩ := hDeg E
    rw [hf]; unfold Sz.Glob.f; omega
  have hK : 4 ≤ D.K := by rw [hInst.2.1]; norm_num
  have hTh0 : 0 < Th := by linarith
  obtain ⟨hKr, hAxA2, hEB, hDomA⟩ := hAx hLC2 h13 E W D hLM
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hReal
  have hPS : D.PoissonStep := by
    obtain ⟨V, i1, i2, i3, i4, i5, ι, i6, π, Λ, i7, i8, emb, dmap, hb, hFr, hW⟩ := r4
    exact hPSJ hPT hPJ E W D V ι π hb Λ emb dmap hFr hW
  have hA4 : D.LeadingDomination Vt (fun _ _ => (0 : ℂ)) := by
    refine ⟨fun ρ p h => absurd rfl h, fun Y _ R => ?_, fun ρ => ?_⟩
    · exact Formalism.FourierDecayAlt.P.Jx7.psd_congr (fun x _ y _ => by simp) (hKr (D.r + 1) Y)
    · simp
  have hRec : TC.RecHypAfter D C₁ C₄ Th jn Vt (fun _ _ => (0 : ℂ)) :=
    ⟨hK, hf1, hTh0, hSB, r1, hKr, r2, hAxA2, hEB, hDomA, r3, hPS, r5, r6, hLS, r7, r8, hA4⟩
  obtain ⟨hk5, Pd, q, lq, hq, hcard, hx⟩ := hDens
  obtain ⟨hsdE, hsd2⟩ := hDC hDSum hDL2 hDSz Pd q lq G.k G.r G.f sd hk5 hq hcard hx
  have he0 : D.e (D.r + 1) = 0 := hLM.2.2.2 (D.r + 1) (by omega) le_rfl
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hRows
  obtain ⟨q1, q2, q3, q4, q5⟩ := hRST hDST hSBM E W D C₁ C₄ Th jn H Vt (fun _ _ => (0 : ℂ)) c sd hsd2
    he0 hRec w1 w2 w3
  have hjn := Formalism.FourierDecayAlt.P.Jx7.jn_nonneg D jn r1 r7
  have habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f := by
    calc (CT / Th) ^ D.f ≤ |(CT / Th) ^ D.f| := le_abs_self _
      _ = (|CT| / Th) ^ D.f := by rw [abs_pow, abs_div, abs_of_pos hTh0]
  have hr0 : (0 : ℝ) ≤ D.r := Nat.cast_nonneg _
  have hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_
    rw [hr, hf]; exact s3
  have he1p : 0 < B.e1 := by rw [he1]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbound : ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ (1 + B.δ) * B.e1 * B.IntN := by
    intro R
    have := hT E W (TC.scaleTop D (max sd 1)) Th jn H Vt c sd q1 s1 (by rw [q2, q3]; exact hsm)
      (fun i hi => by
        rw [q2] at hi
        rw [q5 i hi]
        exact hLM.2.2.2 i (Finset.mem_Icc.1 hi).1 (by have := (Finset.mem_Icc.1 hi).2; omega))
      (by rw [q2]; exact q4) R
    rw [q2, q3] at this
    refine le_trans this ?_
    rw [hδ, hI, he1]
    have h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤
        |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
      calc CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f
          ≤ |CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f| := le_abs_self _
        _ = |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
            rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos hTh0,
              abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]
    apply mul_le_mul_of_nonneg_right _ hjn
    apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (le_max_right _ _))
    linarith
  have key : B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.e1 * (B.n0c * B.IntN) := by
    calc B.c0 * B.c0' * B.KV ≤ B.n0c * ((1 + B.δ) * B.e1 * B.IntN) := w4 _ hbound
      _ = _ := by ring
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := hMassData
  have hmain := hFM hMT P { B with Kgs2 := B.tt * B.Gam1 * B.Sig } b1 he1p w5 (le_refl _) b2 b3 key b4
    b5 b6 b7 b8 b9 b10 b11 b12 b13
  have hGS : B.tt * B.Gam1 * B.Sig ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) := by
    have h1 := hmain.1
    have h2 := hmain.2.1
    rw [h1] at h2
    exact h2
  have htt : 0 < B.tt := by
    unfold S3.MassData.tt
    apply Finset.prod_pos
    intro p _
    have := (b1.1 p).1
    positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : B.tt * (B.Gam1 * B.Sig) ≤ B.tt * ((1 + B.δ) * B.e1 * (B.d * B.d' / B.Dstar)) := by
      calc B.tt * (B.Gam1 * B.Sig) = B.tt * B.Gam1 * B.Sig := by ring
        _ ≤ _ := hGS
        _ = _ := by ring
    exact le_of_mul_le_mul_left this htt
  · rw [hδ]; positivity
  · rw [hδ, hr, hf]; exact s5
  · rw [he1]; exact le_max_right _ _
  · rw [he1]; exact max_le hsdE (Real.one_le_exp (by positivity))
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
