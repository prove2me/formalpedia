-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_gives_one_letter_hyps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:06:56.593488+00:00
-- url     : https://prove2.me/submissions/17f5b861-3e65-4eac-8415-d6d2b781acd5

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_rtt_relation_entries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
namespace Formalism.FourierDecayAlt.P
private theorem transpose_mul_J_mul_apply {A : Type*} [Ring A] (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (Mᵀ * Formalism.YangianSpanCharacter.T.J A * N) i j = M 0 i * N 1 j - M 1 i * N 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring
private theorem mul_J_mul_transpose_apply' {A : Type*} [Ring A] (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (M * Formalism.YangianSpanCharacter.T.J A * Nᵀ) i j = M i 0 * N j 1 - M i 1 * N j 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : FrameModHyp := by
  intro A S _ _ _ _ _ _ r L f hf
  have hGGi : L.GGi ∈ zfns L := by simp [zfns]
  have hGG : L.GG ∈ zfns L := by simp [zfns]
  have hio_mul : ∀ a b : A, (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := fun a b => by
    simp only [io, map_mul]
  have hio_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by simp only [io, map_one]
  have hGG1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1 := by rw [← hio_mul, L.GG_GGi, hio_one]
  have hGG2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← hio_mul, L.GGi_GG, hio_one]
  have hFFi := hf.F_Fi
  have hFiF := hf.Fi_F
  have hc_mul : ∀ a b : SlopeTestRemainingChoices S A, f.F * a * f.Fi * (f.F * b * f.Fi) = f.F * (a * b) * f.Fi := by
    intro a b
    calc f.F * a * f.Fi * (f.F * b * f.Fi) = f.F * a * (f.Fi * f.F) * b * f.Fi := by
          simp only [mul_assoc]
      _ = f.F * (a * b) * f.Fi := by rw [hFiF, mul_one, mul_assoc f.F]
  have hT : ∀ Y ∈ f.reg, f.hatT Y = (f.TT Y).map (fun b => f.F * b * f.Fi) := by
    intro Y hY
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatT
    rw [if_pos hY]
  have hT0 : ∀ Y, Y ∉ f.reg → f.hatT Y = 0 := by
    intro Y hY
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatT
    rw [if_neg hY]
  have hτ11 : ∀ Y ∈ f.reg, f.hatT Y 1 1 = io L.GG * f.x Y := by
    intro Y hY
    rw [hT Y hY, Matrix.map_apply, hf.frame_τ Y hY, mul_assoc, hFFi, mul_one]
  have hxiG : ∀ Y ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi Y) (io g) := by
    intro Y hY g hg
    have hx := hf.x_fn Y g hg
    obtain ⟨h1, h2⟩ := hf.x_xi Y hY
    show f.xi Y * io g = io g * f.xi Y
    calc f.xi Y * io g = f.xi Y * io g * (f.x Y * f.xi Y) := by rw [h1, mul_one]
      _ = f.xi Y * (io g * f.x Y) * f.xi Y := by simp only [mul_assoc]
      _ = f.xi Y * (f.x Y * io g) * f.xi Y := by rw [← hx.eq]
      _ = (f.xi Y * f.x Y) * io g * f.xi Y := by simp only [mul_assoc]
      _ = io g * f.xi Y := by rw [h2, one_mul]
  have hq : ∀ Y, Y ∈ f.reg → Y + 1 ∈ f.reg → f.hatQ Y = f.q Y := by
    intro Y h1 h2
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatQ
    rw [if_pos ⟨h1, h2⟩]
  have hq0 : ∀ Y, ¬ (Y ∈ f.reg ∧ Y + 1 ∈ f.reg) → f.hatQ Y = 0 := by
    intro Y h
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatQ
    rw [if_neg h]
  have hJ : ∀ i j : Fin 2, f.F * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) i j * f.Fi = Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, hFFi]
  have h1 : ∀ (u v : ℂ) (i j k l : Fin 2),
      (u - v) • (f.hatT u i j * f.hatT v k l - f.hatT v k l * f.hatT u i j) =
        f.hatT u k j * f.hatT v i l - f.hatT v k j * f.hatT u i l := by
    intro u v i j k l
    by_cases hu : u ∈ f.reg
    · by_cases hv : v ∈ f.reg
      · have hR := rtt_relation_entries ℂ (SlopeTestRemainingChoices S A) f.TT v u (hf.module.rtt v hv u hu) i j k l
        simp only [hT u hu, hT v hv, Matrix.map_apply, hc_mul]
        simp only [← sub_mul, ← mul_sub]
        rw [← smul_mul_assoc, ← mul_smul_comm, hR]
      · simp [hT0 v hv]
    · simp [hT0 u hu]
  have h2 : ∀ Y, (f.hatT (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * f.hatT Y =
      f.hatQ Y • Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
    intro Y
    by_cases hY : Y ∈ f.reg ∧ Y + 1 ∈ f.reg
    · rw [hq Y hY.1 hY.2]
      have hD := (hf.module.det Y hY.1 hY.2).1
      ext i j : 1
      have e := congrFun (congrFun hD i) j
      rw [transpose_mul_J_mul_apply] at e ⊢
      rw [hT Y hY.1, hT (Y + 1) hY.2]
      simp only [Matrix.map_apply, hc_mul]
      simp only [← sub_mul, ← mul_sub]
      rw [e]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hJ]
    · rw [hq0 Y hY, zero_smul]
      by_cases h1 : Y ∈ f.reg
      · have h2' : Y + 1 ∉ f.reg := fun h => hY ⟨h1, h⟩
        rw [hT0 _ h2']
        simp
      · rw [hT0 _ h1]
        simp
  have h3 : ∀ Y, f.hatT Y * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (f.hatT (Y + 1))ᵀ =
      f.hatQ Y • Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
    intro Y
    by_cases hY : Y ∈ f.reg ∧ Y + 1 ∈ f.reg
    · rw [hq Y hY.1 hY.2]
      have hD := (hf.module.det Y hY.1 hY.2).2
      ext i j : 1
      have e := congrFun (congrFun hD i) j
      rw [mul_J_mul_transpose_apply'] at e ⊢
      rw [hT Y hY.1, hT (Y + 1) hY.2]
      simp only [Matrix.map_apply, hc_mul]
      simp only [← sub_mul, ← mul_sub]
      rw [e]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hJ]
    · rw [hq0 Y hY, zero_smul]
      by_cases h1 : Y ∈ f.reg
      · have h2' : Y + 1 ∉ f.reg := fun h => hY ⟨h1, h⟩
        rw [hT0 _ h2']
        simp
      · rw [hT0 _ h1]
        simp
  have h4 : ∀ u ∈ f.inv, f.hatT u 1 1 * (io L.GGi * f.xi u) = 1 ∧
      io L.GGi * f.xi u * f.hatT u 1 1 = 1 := by
    intro u hu
    rw [hτ11 u (hf.inv_reg hu)]
    obtain ⟨hx1, hx2⟩ := hf.x_xi u hu
    have hc1 := (hf.x_fn u L.GGi hGGi).eq
    have hc2 := (hxiG u hu L.GG hGG).eq
    constructor
    · calc io L.GG * f.x u * (io L.GGi * f.xi u) = io L.GG * (f.x u * io L.GGi) * f.xi u := by
            simp only [mul_assoc]
        _ = io L.GG * (io L.GGi * f.x u) * f.xi u := by rw [hc1]
        _ = (io L.GG * io L.GGi) * (f.x u * f.xi u) := by simp only [mul_assoc]
        _ = 1 := by rw [hGG1, hx1, one_mul]
    · calc io L.GGi * f.xi u * (io L.GG * f.x u) = io L.GGi * (f.xi u * io L.GG) * f.x u := by
            simp only [mul_assoc]
        _ = io L.GGi * (io L.GG * f.xi u) * f.x u := by rw [hc2]
        _ = (io L.GGi * io L.GG) * (f.xi u * f.x u) := by simp only [mul_assoc]
        _ = 1 := by rw [hGG2, hx2, one_mul]
  have h5 : ∀ u v, Commute (f.hatT u 1 1) (f.hatT v 1 1) := by
    intro u v
    by_cases hu : u ∈ f.reg
    · by_cases hv : v ∈ f.reg
      · rw [hτ11 u hu, hτ11 v hv]
        have hGGx : ∀ w, Commute (io L.GG : SlopeTestRemainingChoices S A) (f.x w) := fun w => (hf.x_fn w L.GG hGG).symm
        exact Commute.mul_left ((Commute.refl _).mul_right (hGGx v))
          (((hGGx u).symm).mul_right (hf.x_commute u v))
      · rw [hT0 v hv]
        simp
    · rw [hT0 u hu]
      simp
  have h6 : ∀ u v, Commute (f.hatT u 1 0) (f.hatT v 1 0) := by
    intro u v
    by_cases hu : u ∈ f.reg
    · by_cases hv : v ∈ f.reg
      · rw [hT u hu, hT v hv, Matrix.map_apply, Matrix.map_apply]
        show _ * _ = _ * _
        rw [hc_mul, hc_mul, (hf.lowerLeftEntry_commute u hu v hv).eq]
      · rw [hT0 v hv]
        simp
    · rw [hT0 u hu]
      simp
  refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, ?_⟩
  intro Y hY hY1
  have hr := hf.inv_reg hY
  unfold lf
  rw [hT Y hr, Matrix.map_apply, hf.frame_l Y hY hY1]
  obtain ⟨hx1, hx2⟩ := hf.x_xi Y hY
  have hc2 := (hxiG Y hY L.GG hGG).eq
  calc io L.GGi * f.xi Y * (io L.GG * f.x Y * f.l L Y * f.F * f.Fi)
      = io L.GGi * (f.xi Y * io L.GG) * f.x Y * f.l L Y * (f.F * f.Fi) := by simp only [mul_assoc]
    _ = io L.GGi * (io L.GG * f.xi Y) * f.x Y * f.l L Y * (f.F * f.Fi) := by rw [hc2]
    _ = (io L.GGi * io L.GG) * (f.xi Y * f.x Y) * f.l L Y * (f.F * f.Fi) := by simp only [mul_assoc]
    _ = f.l L Y := by simp only [hGG2, hx2, hFFi, one_mul, mul_one]
end Formalism.FourierDecayAlt.P
