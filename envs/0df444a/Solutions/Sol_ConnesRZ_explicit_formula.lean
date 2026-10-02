-- Prove2me | solution 1 for ConnesRZ.explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-01T22:07:25.112979+00:00
-- url     : https://prove2.me/submissions/4439b223-de58-4509-a560-02a931fc86ac

import Definitions.Def_ConnesRZ_weil_defs
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_Zeta23_WeilEF_EF_lit_zeta

open Complex MeasureTheory

lemma connes_paperFT_dictionary (g : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT g z = ConnesRZ.mellinHat g (1 / 2 + I * z) := by
  unfold Zeta23.paperFT ConnesRZ.mellinHat
  congr 1
  funext t
  congr 1
  congr 1
  ring

lemma connes_paperFT_at_zero (g : ℝ → ℂ) (s : ℂ) :
    Zeta23.paperFT g (Zeta23.gammaOf s) = ConnesRZ.mellinHat g s := by
  rw [connes_paperFT_dictionary]
  congr 1
  unfold Zeta23.gammaOf
  field_simp
  ring

lemma connes_arithmetic_dictionary (g : ℝ → ℂ) :
    Zeta23.EF.literatureRHS g = ConnesRZ.weilDistribution g := by
  have h0 : (1 / 2 : ℂ) + I * (I / 2) = 0 := by
    calc
      _ = (1 + I ^ 2) / 2 := by ring
      _ = 0 := by rw [I_sq]; norm_num
  have h1 : (1 / 2 : ℂ) + I * (-I / 2) = 1 := by
    calc
      _ = (1 - I ^ 2) / 2 := by ring
      _ = 1 := by rw [I_sq]; norm_num
  unfold Zeta23.EF.literatureRHS ConnesRZ.weilDistribution ConnesRZ.primeSum
  simp only [connes_paperFT_dictionary, h0, h1]
  unfold ConnesRZ.archTerm Zeta23.EF.gammaBracket Complex.digamma
  rfl

/-- Transfer of the existing proved zeta explicit formula; no open analytic assumptions. -/
theorem solution (g : ℝ → ℂ) (hg : ConnesRZ.IsTest g) :
    HasSum (fun ρ : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
      (ConnesRZ.zeroMult ρ.1 : ℂ) * ConnesRZ.mellinHat g ρ.1)
      (ConnesRZ.weilDistribution g) := by
  have h := Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam g
    (hg.1.of_le (by decide)) hg.2
  have hfun :
      (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
        ((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) *
          Zeta23.paperFT g (Zeta23.gammaOf ρ)) =
      (fun ρ : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
        (ConnesRZ.zeroMult ρ.1 : ℂ) * ConnesRZ.mellinHat g ρ.1) := by
    funext ρ
    rw [connes_paperFT_at_zero]
    rfl
  rw [hfun, connes_arithmetic_dictionary] at h
  exact h.2 ▸ h.1.hasSum
