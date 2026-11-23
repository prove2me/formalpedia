-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.first_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:43.715806+00:00
-- url     : https://prove2.me/submissions/28758d54-0e16-4dd0-989a-e2d7740f81ca

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_x1__a3dada
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_one_le_threshold_mul_powers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_apos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution {C₁ : ℝ}
    (hC₁ : ∀ (e J : ℕ) (Y X' ρ p₀ : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
      0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ → 2 ≤ X' →
      (∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧
        (((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) ∨
          (p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X' * (1 + ρ)))) →
      ∑ p ∈ s, Real.log p / p ≤
        C₁ * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e +
          (⌊Real.log X'⌋₊ : ℝ) * ((4 * ρ + 1 / p₀) * Real.log (2 * X')))
    {P : Par} {e K : ℝ} (hCord : C₁ ≤ P.Cord) (hW : Windows P e K) (hL : LargeX P.x P.ε e K)
    (Ps : Finset ℕ) (cl : ℕ → PClass) (hPs : ∀ p ∈ Ps, p.Prime ∧ p ≠ 2) (hF : FirstHyp P Ps cl)
    (m T : ℝ) (hm : 0 ≤ m) (hT : 0 ≤ T) :
    4 * m * T * P.a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), Real.log p / p) ≤
      tOrders P m T + tBand P m T := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hx := F.hx
  have hx2 : P.x ≤ P.x ^ 2 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 2 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hx4 : P.x ≤ P.x ^ 4 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have he2 : 1 ≤ P.e₂ := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have h1 := F.n2x
    rw [h0, pow_zero] at h1
    linarith
  have hJo : 1 ≤ P.Jo := by
    unfold Par.Jo
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow F.x1 (by have := hW.1; positivity)
  have hρ : P.ρ ≤ 1 / 2 := by
    have h1 : (P.x ^ 2)⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    have := F.ρx
    norm_num at h1
    linarith
  have hp8 : (8 : ℝ) ≤ (P.p₀ : ℝ) := by linarith [F.px]
  have hX2 : 2 ≤ P.Xp := by
    rw [F.hXp]
    have := F.one_le_threshold_mul_powers; have := F.hXB
    linarith
  have hIb : ⌊Real.log P.Xp⌋₊ = P.Ib := by
    rw [F.hXp, F.logX, F.hu]; rfl
  have h := hC₁ P.e₂ P.Jo (max P.Y P.Xpp) P.Xp P.ρ (P.p₀ : ℝ) (Ps.filter (fun p => cl p = PClass.first)) he2 hJo
    (F.Y1.trans (le_max_left _ _))
    F.ρ0 hρ hp8 hX2 (by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine ⟨(hPs p hp.1).1, (hPs p hp.1).2, ?_⟩
      rcases hF p hp.1 hp.2 with ⟨a1, hl, a2⟩ | ⟨b1, b2⟩
      · exact Or.inl ⟨a1, hl, Nat.le_floor a2.le⟩
      · exact Or.inr ⟨by exact_mod_cast b1, b2⟩)
  rw [hIb] at h
  have hn0 : (0 : ℝ) < 2 ^ P.e₂ := by positivity
  have hJ0 : (0 : ℝ) ≤ P.Jo := Nat.cast_nonneg _
  have h2 : C₁ * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂ ≤
      P.Cord * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂ := by gcongr
  have hco : 0 ≤ 4 * m * T * P.a := by
    have := F.apos
    positivity
  have h3 := mul_le_mul_of_nonneg_left (h.trans (add_le_add_left h2 _)) hco
  unfold tOrders tBand
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
