-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.frameInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:32.202748+00:00
-- url     : https://prove2.me/submissions/7744e800-29ed-4d63-a90d-31057e7912f6

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_toStd_append__a71b1777b774
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_toStd_size__257163185415
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_isLocPt_toStd_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_bSt_append_one
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_rd_pos__cb5bba46fb5e
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_weight_product_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_weight_product_indep_of_real_parameter
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_lpt_value_nonneg_of_pos_of_size_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_cutWord_of_adm
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_scal_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_gamLev_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_gamLev_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_rrTop_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution : FrameInt := by
  intro Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB hC hstd v
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGr, -, -, -, -, hv⟩ := hB
  obtain ⟨hl0, -, hpd, -, -⟩ := hv v
  intro ε hε i hi1 hir w h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hjr : j ≤ S.G.r := by omega
  simp only [Nat.add_sub_cancel] at hsz hsz' ⊢
  have hgpos : (0 : ℝ) < (S.g : ℝ) := by unfold C.HidaSetting.g; exact_mod_cast Nat.mul_pos hg1 hg2
  have hrd := rd_pos' E
  have hκ : 0 < D.kapG (S.g : ℝ) (S6.rd E) := by unfold D.kapG; positivity
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  have hfr : ∀ b s, 0 < S.fr b s := fun b s => Real.rpow_pos_of_pos hrd _

  have hTT : Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' = S.T * S.T' := by
    have h := S.hT v
    rw [hpd] at h
    rw [← h.1, ← h.2]
    rfl

  set RRs : ℕ → C.LPt → C.LPt → ℂ := fun i P Q => D.RRplace (p v).T (M.sgn (D.parOf S v) (S.l + 1)) (p v).ν'
      (p v).m₀ (Top.topOf (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP)
      (D.cutF (p v).T.base χ (f v) ε) i (w.1 v) P Q with hRRs
  have hRR : ∀ i P Q, (p v).RR (D.cutF (p v).T.base χ (f v) ε) i (w.1 v) P Q = RRs i P Q := by
    intro i P Q
    simp only [KB.Pl.RR, hRRs, hl0]
  set nn : C.LPt → ℝ := fun P => C.nLoc S.G.k S.G.r S.fr
      (D.ptGG (Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z')) P with hnn
  set Γ : ℕ → ℝ := fun i => D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i with hΓ
  set bS : C.LPt → ℝ := fun P => D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P with hbS
  have hgram : ∀ i P Q, S.gramLoc v ε i (w.1 v) P Q =
      ((√(nn P) * √(nn Q) : ℝ) : ℂ) * (((1 / (bS P * bS Q * Γ i)) : ℝ) : ℂ) *
        RRs i (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q) := by
    intro i P Q
    unfold C.HidaSetting.gramLoc
    rw [hpd]
    simp only [D.componentFamilySetting_ofSetting, one_pow, mul_assoc, hnn, hΓ, hbS, hRRs]

  have hstd_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.toStd S.G.r (S.g : ℝ) 1 (H ++ [(1, c)]) =
      D.toStd S.G.r (S.g : ℝ) 1 H ++
        [(1, ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) * c)] := by
    intro H c hH
    rw [toStd_append', hH, show 1 + j = j + 1 by omega]
  set lam : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) with hlam
  have hlam_pos : 0 < lam := zpow_pos (by positivity) _
  set TT0 := Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' with hTT0
  set xw : ℂ → ℝ := fun c => C.nAux S.G.k S.G.r (Complex.normSq c - TT0) S.fr (j + 1) [(1, c)] with hxw
  have hn_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → nn (H ++ [(1, c)]) = nn H * xw c := by
    intro H c hH
    simp only [hnn, hxw, C.nLoc]
    rw [weight_product_append, hH, show 1 + j = j + 1 by omega]
    have hG : D.ptGG TT0 (H ++ [(1, c)]) = Complex.normSq c - TT0 := by simp [D.ptGG, D.ptLast]
    rw [hG, weight_product_indep_of_real_parameter _ _ _ (D.ptGG TT0 H) _ H 1 le_rfl (by omega)]
  have hn_nonneg : ∀ H, D.ptSize H = j → 0 ≤ nn H := fun H hH =>
    lpt_value_nonneg_of_pos_of_size_le _ _ _ _ hfr H 1 le_rfl (by omega)
  have hsq : ∀ c, √(nn (h ++ [(1, c)])) * √(nn (h' ++ [(1, c)])) = √(nn h) * √(nn h') * (√(xw c) * √(xw c)) := by
    intro c
    rw [hn_app h c hsz, hn_app h' c hsz', Real.sqrt_mul (hn_nonneg h hsz), Real.sqrt_mul (hn_nonneg h' hsz')]
    ring
  set Mj : ℤ := C.Mlev S.G.k S.G.r (j + 1) with hMj
  set ρ : ℝ := (S.fr (j + 1) 1 / lam) ^ (2 * (Mj - 2)) with hρ
  have hW : ∀ (H H' : C.LPt) (c : ℂ), D.ptSize H = j → c ≠ 0 →
      ((√(xw c) * √(xw c) : ℝ) : ℂ) * RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) =
        ((ρ * KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) : ℝ) : ℂ) *
          RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) := by
    intro H H' c hH hc
    by_cases hjt : j = S.G.r
    · have hnu : S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; rw [hjt]; push_cast; ring
      have hlam1 : lam = 1 := by rw [hlam, hnu, zpow_zero]
      have hfr1 : S.fr (j + 1) 1 = 1 := by
        unfold C.HidaSetting.fr
        have : ((S6.nuBlock (S.G.r : ℤ) (Nat.cast (j + 1)) (Nat.cast 1) : ℤ) : ℝ) = 0 := by
          unfold S6.nuBlock; rw [hjt]; push_cast; ring
        rw [this]; simp
      have hρ1 : ρ = 1 := by rw [hρ, hlam1, hfr1]; simp
      have hx : xw c = (Complex.normSq c - TT0) ^ (S.G.k - 1) := by
        simp only [hxw, C.nAux]
        rw [if_pos (by constructor <;> first | trivial | omega), mul_one]
      have hlev : KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) = B2.zWeight S.G.k S.T S.T' c := by
        rw [hlam1, Complex.ofReal_one, one_mul]
        unfold KB.levW
        rw [if_pos (by simp [hjt])]
      rw [hρ1, hlev, one_mul, hx]
      by_cases hc2 : S.T * S.T' ≤ Complex.normSq c
      · rw [Real.mul_self_sqrt (pow_nonneg (by rw [hTT]; linarith) _)]
        unfold B2.zWeight
        rw [if_pos hc2, hTT]
      · have h0 : RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) = 0 := by
          have := rrTop_zero (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
            (M.sgn (D.parOf S v) (S.l + 1)) (D.cutF (p v).T.base χ (f v) ε) (w.1 v) H (H' ++ [(1, (lam : ℂ) * c)])
            ((lam : ℂ) * c) (by rw [hH, hjt]) (by
              rw [hlam1, Complex.ofReal_one, one_mul]
              show Complex.normSq c ≤ TT0
              rw [hTT]; linarith)
          simp only [hRRs]
          rw [show j + 1 = (D.parOf S v).r + 1 by rw [hjt]]
          exact this
        rw [h0, mul_zero, mul_zero]
    · have hx : xw c = (S.fr (j + 1) 1 * ‖c‖) ^ (2 * (Mj - 2)) := by
        simp only [hxw, C.nAux]
        rw [if_neg (by omega), mul_one, hMj]
        congr 1
        simp only [Nat.add_sub_cancel, Nat.cast_one]
        ring
      have hxpos : 0 < xw c := by rw [hx]; exact zpow_pos (mul_pos (hfr _ _) (norm_pos_iff.2 hc)) _
      rw [Real.mul_self_sqrt hxpos.le]
      congr 2
      rw [hx, hρ]
      unfold KB.levW
      rw [if_neg (by simp only [D.parOf]; omega)]
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnorm, ← mul_zpow]
      congr 1
      field_simp

  have hloc_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.IsLocPt (H ++ [(1, c)]) (j + 1) → D.IsLocPt H j :=
    fun H c hH h1 => ⟨fun b hb => h1.1 b (List.mem_append_left _ hb), hH⟩
  have hRRnl : ∀ i P Q, ¬ (D.IsLocPt P i ∧ D.IsLocPt Q i) →
      RRs i (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q) = 0 := by
    intro i P Q hPQ
    simp only [hRRs]
    unfold D.RRplace
    rw [dif_neg]
    rwa [isLocPt_toStd_iff _ _ hgpos, isLocPt_toStd_iff _ _ hgpos]
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨φ, hφc, ⟨Cφ, hCφ⟩, hφ, hφint⟩ := hstd v ε hε j hjr (w.1 v)
      (by rw [hl0]; exact cutWord_of_adm S hGr hC w v) _ _ hH hH'
    set K : ℝ := √(nn h) * √(nn h') * (1 / (bS h * bS h' * Γ (j + 1))) * ρ with hK
    refine ⟨fun c => (K : ℂ) * φ ((lam : ℂ) * c), ?_, ?_, ?_, ?_⟩
    · exact continuous_const.mul (hφc.comp (continuous_const.mul continuous_id))
    · intro c hc
      have hlc : (lam : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
      have hWc := hW (D.toStd S.G.r (S.g : ℝ) 1 h) (D.toStd S.G.r (S.g : ℝ) 1 h') c
        (by rw [toStd_size']; exact hsz) hc
      simp only
      rw [hgram, hstd_app h c hsz, hstd_app h' c hsz', hsq, hφ _ hlc, hRR]
      simp only [hbS, bSt_append_one]
      simp only [← hbS]
      push_cast at hWc ⊢
      rw [hK]
      push_cast
      linear_combination (-((√(nn h) : ℂ) * (√(nn h') : ℂ) * (1 / ((bS h : ℂ) * (bS h' : ℂ) * (Γ (j + 1) : ℂ))))) * hWc
    · refine ⟨|K| * |Cφ| * (min 1 lam ^ 3)⁻¹, fun c => ?_⟩
      have hm : 0 < min 1 lam := lt_min one_pos hlam_pos
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      have h1 : min 1 lam * (1 + ‖c‖) ≤ 1 + ‖(lam : ℂ) * c‖ := by
        rw [hnorm]
        have := min_le_left 1 lam; have := min_le_right 1 lam
        nlinarith [norm_nonneg c]
      have h2 : ((1 + ‖(lam : ℂ) * c‖) ^ 3)⁻¹ ≤ (min 1 lam ^ 3)⁻¹ * ((1 + ‖c‖) ^ 3)⁻¹ := by
        rw [← mul_inv, ← mul_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 3)
      have h3 := hCφ ((lam : ℂ) * c)
      have h4 : 0 ≤ ((1 + ‖(lam : ℂ) * c‖) ^ 3)⁻¹ := by positivity
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |K| * ‖φ ((lam : ℂ) * c)‖ ≤ |K| * (|Cφ| * ((1 + ‖(lam : ℂ) * c‖) ^ 3)⁻¹) :=
            mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h4)) (abs_nonneg _)
        _ ≤ |K| * (|Cφ| * ((min 1 lam ^ 3)⁻¹ * ((1 + ‖c‖) ^ 3)⁻¹)) := by gcongr
        _ = |K| * |Cφ| * (min 1 lam ^ 3)⁻¹ * ((1 + ‖c‖) ^ 3)⁻¹ := by ring
    · have e1 : (fun c : ℂ => (K : ℂ) * φ ((lam : ℂ) * c)) = fun c => (K : ℂ) * φ (lam • c) := by
        funext c; rw [Complex.real_smul]
      rw [e1, integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex, hφint, hRR, hgram]

      have hfac := gamLev_succ S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) j hjr
      have hΓpos : 0 < Γ (j + 1) := gamLev_pos _ _ _ _ hκ hδ _
      have hbh : 0 < bS h := bSt_pos' _ hκ h
      have hbh' : 0 < bS h' := bSt_pos' _ hκ h'
      have hgl : (S.g : ℝ) / (2 * Real.pi) = (D.kapG (S.g : ℝ) (S6.rd E) * S6.rd E)⁻¹ := by
        unfold D.kapG; field_simp
      have hfrj : S.fr (j + 1) 1 = S6.rd E ^ (-(S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ))) := by
        unfold C.HidaSetting.fr
        rw [← Real.rpow_intCast]
        push_cast
        ring_nf
      have hkey : ρ * (lam ^ 2)⁻¹ = S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)) *
          D.kapG (S.g : ℝ) (S6.rd E) ^ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1)) := by
        rw [hρ, hfrj, hlam, hgl, ← div_eq_mul_inv, scal_id _ _ hκ hrd]
        congr 1
        congr 1
        unfold S6.nuBlock
        rw [hMj]
        push_cast
        ring
      have hscal : K * |(lam ^ 2)⁻¹| = KB.dlB S (j + 1) 1 * (√(nn h) * √(nn h') * (1 / (bS h * bS h' * Γ j))) := by
        rw [abs_of_pos (by positivity)]
        have hΓj : Γ j = _ := hfac
        rw [hΓj]
        have e2 : K * (lam ^ 2)⁻¹ = √(nn h) * √(nn h') * (1 / (bS h * bS h' * Γ (j + 1))) * (ρ * (lam ^ 2)⁻¹) := by
          rw [hK]; ring
        rw [e2, hkey]
        unfold KB.dlB
        have hΓ1 : Γ (j + 1) = D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (j + 1) :=
          rfl
        rw [← hΓ1, zpow_neg]
        have hκX := zpow_pos hκ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1))
        field_simp
      rw [Complex.real_smul]
      push_cast
      have hs := congrArg (fun x : ℝ => (x : ℂ)) hscal
      push_cast at hs
      linear_combination (RRs j (D.toStd S.G.r (S.g : ℝ) 1 h) (D.toStd S.G.r (S.g : ℝ) 1 h')) * hs
  · refine ⟨fun _ => 0, continuous_const, fun c hc => ?_, ⟨0, fun c => by simp⟩, ?_⟩
    · rw [hgram, hRRnl]
      · simp
      · rintro ⟨h1, h2⟩
        exact hloc ⟨hloc_app h c hsz h1, hloc_app h' c hsz' h2⟩
    · rw [hgram, hRRnl _ _ _ hloc]
      simp
end Formalism.FourierDecayAlt.P.PBD
