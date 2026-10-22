-- Prove2me | solution 1 for DynkinIncInfo.Saddle.lemma_4_2_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:14:25.959176+00:00
-- url     : https://prove2.me/submissions/5e9b57dd-b56e-4d98-923f-131d6a8d653f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions
import Theorems.Thm_DynkinIncInfo_Saddle_lemma_3_1

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open DynkinIncInfo.Saddle

namespace DynkinLemma42Aux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Vup_le_G2 (p : Params) (st : Setting Ω) (x' y' : ℝ) :
    Vup p st x' y' ≤ ENNReal.ofReal (G2 p x') := by
  haveI := st.isProb
  unfold Vup dynkinUpper
  refine (iInf₂_le (fun _ : Ω => (0 : WithTop ℝ≥0)) (isStoppingTime_const _ _)).trans ?_
  refine iSup₂_le fun τ _ => ?_
  have hB := st.brownian.eval_zero_ae_eq_zero
  calc dynkinM st.P (L1 p st x' y') (U2 p st x' y') τ (fun _ => 0)
      ≤ ∫⁻ _, ENNReal.ofReal (G2 p x') ∂st.P := by
        apply lintegral_mono_ae
        filter_upwards [hB] with ω hω
        have hS : S p st x' y' 0 ω = x' := by simp [S, hω]
        unfold dynkinPayoff
        split_ifs with h1 h2
        · have : τ ω = 0 := le_antisymm h1.1 bot_le
          rw [this]
          show ENNReal.ofReal (Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * G1 p (S p st x' y' 0 ω)) ≤ _
          rw [hS]
          apply ENNReal.ofReal_le_ofReal
          simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul]
          unfold G1 G2; linarith [p.ε0_pos]
        · show ENNReal.ofReal (Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * G2 p (S p st x' y' 0 ω)) ≤ _
          rw [hS]; simp
        · exact zero_le
    _ = ENNReal.ofReal (G2 p x') := by simp

/-- `G1(x') ≤ V(x', y')` (take `τ ≡ 0`). -/
lemma G1_le_V (p : Params) (st : Setting Ω) (x' y' : ℝ) : G1 p x' ≤ V p st x' y' := by
  haveI := st.isProb
  have hfin : Vup p st x' y' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Vup_le_G2 p st x' y')
  have hB := st.brownian.eval_zero_ae_eq_zero
  have hlow : ENNReal.ofReal (G1 p x') ≤ Vup p st x' y' := by
    unfold Vup dynkinUpper
    refine le_iInf₂ fun γ _ => ?_
    refine le_trans ?_ (le_iSup₂ (f := fun τ (_ : IsStoppingTime (FS p st x' y') τ) =>
      dynkinM st.P (L1 p st x' y') (U2 p st x' y') τ γ) (fun _ => (0 : WithTop ℝ≥0))
      (isStoppingTime_const _ _))
    calc ENNReal.ofReal (G1 p x') = ∫⁻ _, ENNReal.ofReal (G1 p x') ∂st.P := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hB] with ω hω
        have hS : S p st x' y' 0 ω = x' := by simp [S, hω]
        unfold dynkinPayoff
        rw [if_pos ⟨bot_le, WithTop.coe_ne_top⟩]
        show _ ≤ ENNReal.ofReal (Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * G1 p (S p st x' y' 0 ω))
        rw [hS]; simp
  unfold V
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hlow

end DynkinLemma42Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y y' : ℝ) (hxy : (x, y) ∈ S1 p st) (hyy' : y ≤ y') (hy' : y' ≤ 1) :
    (x, y') ∈ S1 p st := by
  obtain ⟨⟨hx0, hyI⟩, hV⟩ := hxy
  simp only at hx0 hyI hV
  have hy'I : y' ∈ Set.Icc (0 : ℝ) 1 := ⟨hyI.1.trans hyy', hy'⟩
  obtain ⟨_, hmono, _, _⟩ := lemma_3_1 p st (fun x y => V p st x y) (Or.inr rfl)
  have h1 : V p st x y' ≤ V p st x y := hmono x y y' hx0.le hyI hy'I hyy'
  have h2 := DynkinLemma42Aux.G1_le_V p st x y'
  exact ⟨⟨hx0, hy'I⟩, le_antisymm (h1.trans hV.le) h2⟩
