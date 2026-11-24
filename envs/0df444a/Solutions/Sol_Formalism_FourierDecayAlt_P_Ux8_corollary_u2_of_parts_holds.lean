-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.corollary_u2_of_parts_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:39:33.654178+00:00
-- url     : https://prove2.me/submissions/f9795d7c-65be-4b1a-b90f-51d31dcd0097

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cc_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux8
private theorem star_mono_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k j ρ : ℕ}
    {F₁ : B.Mat k (j + ρ) → E} {A₁ : ℝ} {Q : ℕ} {B₁ B₂ : ℝ} {K : Set ℝ}
    (h : Star k j ρ F₁ A₁ Q B₁ K) (hB : B₁ ≤ B₂) : Star k j ρ F₁ A₁ Q B₂ K := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun u v hu hv hl g hg => le_trans (h3 u v hu hv hl g hg) hB⟩
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (p : Seminorm ℂ V)
end
section supp
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pi
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
end pi
end supp
end Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : GermExpansionHypothesisFromComponents := by
  intro hTU hCU1 hSP hBud hTh hPS
  intro C₁ C₂
  refine ⟨16 * ((C₁ : ℝ) + 1) + 20, ?_⟩
  intro k p s ρ Wp Wq _ _ _ _ _ _ ι _ U hOk A₀ hA₀
  have hOk2 := hOk
  obtain ⟨hd, hs1, _, _, hDD, hχ, hχε, _, _, ho, hκ, hAB, hmm, hn3, hC2⟩ := hOk
  have hC1 : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg _
  have hle : C₂ * s ^ 2 ≤ C₂ * (p + s + ρ + 1) ^ 2 :=
    Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_left (by omega) 2)
  obtain ⟨hb1, _, _, _, hb5⟩ := hBud (p + s + ρ) (C₂ * s ^ 2) U.mmB U.o (U.κ + (p + s) * U.o) U.As
    (16 * ((C₁ : ℝ) + 1) + 20) A₀ (by omega) ((Nat.add_le_add_right hle 1).trans hC2) hmm ho hκ
    (by linarith) hA₀
  have hAeq : A₀ - ((U.κ + (p + s) * U.o : ℕ) : ℝ) - 2 * (((p + s + ρ : ℕ) : ℝ) + 1) *
      ((C₂ * s ^ 2 + 1 + U.mmB + U.o : ℕ) : ℝ) =
      A₀ - (U.κ : ℝ) - ((p + s : ℕ) : ℝ) * (U.o : ℝ) - 2 * (((p + s + ρ : ℕ) : ℝ) + 1) *
      (((C₂ * s ^ 2 + 1 + U.mmB) + U.o : ℕ) : ℝ) := by push_cast; ring
  have hc16 : (16 * ((C₁ : ℝ) + 1) + 20 - 20) / 16 = (C₁ : ℝ) + 1 := by ring
  rw [hAeq, hc16] at hb5
  obtain ⟨ht1, ht2, ht3⟩ := hTh (p + s + ρ) (2 * (p + s + ρ) + k + 1) s U.As C₁ ((C₁ : ℝ) + 1) U.AB
    (by omega) (by omega) hn3 hAB (by linarith) (by linarith)
  refine ⟨hb5, le_trans ht3 hb5, le_trans ht2 hb5, ?_⟩
  obtain ⟨_, hχc, hχ0⟩ := id hχ
  have hKc : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport U.χ) :=
    (hχc : IsCompact (tsupport U.χ)).image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport U.χ ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw, rfl⟩
    exact norm_pos_iff.2 (fun h => hχ0 (h ▸ hw))
  choose Ci hCi using fun i => hCU1 k (p + s) ρ Wp Wq U.z U.z' U.o U.κ (U.Θ i) U.χ U.χε U.ε (hDD i) hχ hχε
    (C₂ * s ^ 2 + 1 + U.mmB) (3 * U.As) A₀ hb1
  obtain ⟨CT, hCT⟩ := hTU k p s ρ U.σ U.d hd hs1 _ hKc hK0 (C₂ * s ^ 2) U.mmB (C₂ * s ^ 2 + 1 + U.mmB) _ le_rfl
    (lt_of_lt_of_le ht1 hb5)
  refine ⟨CT * (∑ i, |Ci i|), ?_⟩
  intro f c hf V _ _ _ M
  have hc0 : 0 ≤ c := cc_nonneg hf
  have hB : ∀ i, Ci i * c ≤ (∑ j, |Ci j|) * c := fun i =>
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (Ci j)) (Finset.mem_univ i))) hc0
  have hstar := hSP k (p + s) ρ ι (Wq →L[ℂ] Wp) (U.F1 f) _ _ _ _
    (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (Ci i)) hc0)
    (fun i => star_mono_bound (hCi i f c hf) (hB i))
  obtain ⟨_, _, hmain⟩ := hCT U.z U.z' (ι → (Wq →L[ℂ] Wp)) (U.F1 f) _ hstar
  obtain ⟨Φ, hev, hbd⟩ := hmain U.S V M (fun Z hZ γ hγ hγS => hPS k p s ρ Wp Wq ι U C₂ hOk2 f Z hZ γ hγ hγS)
  refine ⟨Φ, hev, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := hbd Z hZ
  refine ⟨h1, fun q hq => ?_⟩
  have h3 := h2 q hq
  rw [← mul_assoc] at h3
  exact h3
end Formalism.FourierDecayAlt.P.Ux8
