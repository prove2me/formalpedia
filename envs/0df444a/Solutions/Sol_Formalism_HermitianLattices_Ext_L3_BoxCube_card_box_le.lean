-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxCube.card_box_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:34.898797+00:00
-- url     : https://prove2.me/submissions/44f18490-a1ba-4550-9a82-275617cdd6cc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxCube_absNorm_le_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxCube_card_le_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxCube_fDeg_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxCube
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxCube
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)}
    (hb : b ≠ ⊥) {T : ℝ} (hT0 : 0 ≤ T) :
    (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm b : ℝ) := by
  have hf : Formalism.HermitianLatticesTheory.fDeg K ≠ 0 := (fDeg_pos (K := K)).ne'
  have hN : (0 : ℝ) < (Ideal.absNorm b : ℝ) := by
    have : Ideal.absNorm b ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.pos_of_ne_zero this
  by_cases he : IsEmpty {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b}
  · rw [Nat.card_of_isEmpty, Nat.cast_zero, ← mul_pow]
    positivity
  rw [not_isEmpty_iff] at he
  obtain ⟨n, hn, hnb⟩ := he
  have hT : 0 < T := by
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    exact (hn φ).1.trans_le (hn φ).2
  set δ : ℝ := (Ideal.absNorm b : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ)⁻¹) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K = (Ideal.absNorm b : ℝ) := Real.rpow_inv_natCast_pow hN.le hf
  have hδT : δ ≤ T := by
    have := absNorm_le_pow hK hF hn hnb
    rw [← hδ] at this
    exact (pow_le_pow_iff_left₀ hδ0.le hT.le hf).1 this
  have h1 := card_le_pow hK hF (T := T) hδ0 hδ.le
  have h2 : ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T / δ := by
    have h3 := Nat.floor_le (div_nonneg hT.le hδ0.le)
    have h4 : 1 ≤ T / δ := (one_le_div hδ0).2 hδT
    push_cast
    rw [mul_div_assoc]
    linarith
  calc (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ)
      ≤ (((⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K := by push_cast; rfl
    _ ≤ (2 * T / δ) ^ Formalism.HermitianLatticesTheory.fDeg K := pow_le_pow_left₀ (by positivity) h2 _
    _ = _ := by rw [div_pow, mul_pow, hδ]
end Formalism.HermitianLattices.Ext.L3.BoxCube
