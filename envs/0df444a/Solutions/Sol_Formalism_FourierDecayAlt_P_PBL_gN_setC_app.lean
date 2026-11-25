-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.gN_setC_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:05.304065+00:00
-- url     : https://prove2.me/submissions/893955cd-8ae5-4508-a7c7-442a46e898de

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_g_pos_of_built
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_pdG_of_built
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_gN_setC
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_lamS_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_stdS_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_nnS_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_bSt_append_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_lpt_value_nonneg_of_pos_of_size_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_rrTop_zero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_rd_pos__cb5bba46fb5e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBL
theorem _root_.solution {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) (c : ℂ) (hc : c ≠ 0) :
    KB.gN (setC S p F) v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) =
      ((Kc S v j w h h' : ℝ) : ℂ) * ((KB.levW (D.parOf S v) (j + 1) ((lamS S j : ℂ) * c) : ℝ) : ℂ) *
        (p v).RR (F v ε) (j + 1) w (stdS S h ++ [(1, (lamS S j : ℂ) * c)])
          (stdS S h' ++ [(1, (lamS S j : ℂ) * c)]) := by
  have hgpos := g_pos_of_built hB
  have hTT := (pdG_of_built hB v).2
  have hrd := rd_pos' E
  have hfr : ∀ b s, 0 < S.fr b s := fun b s => Real.rpow_pos_of_pos hrd _
  set lam := lamS S j with hlam
  have hlam_pos : 0 < lam := lamS_pos S hgpos j
  set xw : ℂ → ℝ := fun c => C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] with hxw
  have hn_nonneg : ∀ H, D.ptSize H = j → 0 ≤ nnS S H := fun H hH =>
    lpt_value_nonneg_of_pos_of_size_le _ _ _ _ hfr H 1 le_rfl (by omega)
  have hsq : √(nnS S (h ++ [(1, c)])) * √(nnS S (h' ++ [(1, c)])) =
      √(nnS S h) * √(nnS S h') * (√(xw c) * √(xw c)) := by
    rw [nnS_app S j hj h c hsz, nnS_app S j hj h' c hsz', Real.sqrt_mul (hn_nonneg h hsz),
      Real.sqrt_mul (hn_nonneg h' hsz')]
    ring
  set RRs : ℕ → C.LPt → C.LPt → ℂ := fun i P Q => (p v).RR (F v ε) i w P Q with hRRs
  set Mj : ℤ := C.Mlev S.G.k S.G.r (j + 1) with hMj
  have hW : ∀ (H H' : C.LPt), D.ptSize H = j →
      ((√(xw c) * √(xw c) : ℝ) : ℂ) * RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) =
        ((rhoS S j * KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) : ℝ) : ℂ) *
          RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) := by
    intro H H' hH
    by_cases hjt : j = S.G.r
    · have hnu : S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; rw [hjt]; push_cast; ring
      have hlam1 : lam = 1 := by rw [hlam, lamS, hnu, zpow_zero]
      have hfr1 : S.fr (j + 1) 1 = 1 := by
        unfold C.HidaSetting.fr
        have : ((S6.nuBlock (S.G.r : ℤ) (Nat.cast (j + 1)) (Nat.cast 1) : ℤ) : ℝ) = 0 := by
          unfold S6.nuBlock; rw [hjt]; push_cast; ring
        rw [this]; simp
      have hρ1 : rhoS S j = 1 := by rw [rhoS, ← hlam, hlam1, hfr1]; simp
      have hx : xw c = (Complex.normSq c - S.T * S.T') ^ (S.G.k - 1) := by
        simp only [hxw, C.nAux]
        rw [if_pos (by constructor <;> first | trivial | omega), mul_one]
      have hlev : KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) = B2.zWeight S.G.k S.T S.T' c := by
        rw [hlam1, Complex.ofReal_one, one_mul]
        unfold KB.levW
        rw [if_pos (by simp [hjt])]
      rw [hρ1, hlev, one_mul, hx]
      by_cases hc2 : S.T * S.T' ≤ Complex.normSq c
      · rw [Real.mul_self_sqrt (pow_nonneg (by linarith) _)]
        unfold B2.zWeight
        rw [if_pos hc2]
      · have h0 : RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) = 0 := by
          have := rrTop_zero (D.parOf S v) (p v).l0 (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
            (M.sgn (D.parOf S v) (p v).l0) (F v ε) w H (H' ++ [(1, (lam : ℂ) * c)])
            ((lam : ℂ) * c) (by rw [hH, hjt]) (by
              rw [hlam1, Complex.ofReal_one, one_mul]
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
      rw [hx, rhoS, ← hlam, ← hMj]
      unfold KB.levW
      rw [if_neg (by show ¬ (j + 1 = S.G.r + 1); omega)]
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnorm, ← mul_zpow]
      congr 1
      field_simp
  rw [gN_setC hB, stdS_app S j h c hsz, stdS_app S j h' c hsz']
  have hWc := hW (stdS S h) (stdS S h') (by rw [stdS_size]; exact hsz)
  have hb1 : bS S (h ++ [(1, c)]) = bS S h := bSt_append_one _ _ _
  have hb2 : bS S (h' ++ [(1, c)]) = bS S h' := bSt_append_one _ _ _
  rw [hb1, hb2]
  rw [show √(nnS S (h ++ [(1, c)])) * √(nnS S (h' ++ [(1, c)])) /
      (bS S h * bS S h' * ΓS S (j + 1)) / S.sizeAt v w =
      (√(nnS S h) * √(nnS S h') / (bS S h * bS S h' * ΓS S (j + 1)) / S.sizeAt v w) * (√(xw c) * √(xw c)) by
    rw [hsq]; ring]
  simp only [hRRs] at hWc
  unfold Kc
  push_cast at hWc ⊢
  linear_combination ((√(nnS S h) : ℂ) * (√(nnS S h') : ℂ) / ((bS S h : ℂ) * (bS S h' : ℂ) * (ΓS S (j + 1) : ℂ)) /
    (S.sizeAt v w : ℂ)) * hWc
end Formalism.FourierDecayAlt.P.PBL
