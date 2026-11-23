-- Prove2me | solution 1 for Formalism.DimensionVariation.first_descent_coupled_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:58.441213+00:00
-- url     : https://prove2.me/submissions/422da0b4-9ef2-4b59-8316-5355fd857594

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset NumberField
open scoped Real
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
namespace CB
end CB
open CB
namespace CB
end CB
private theorem perEmbCore_lemma : PerEmbeddingCB := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' logn logn' logOm v f m N L La logT
    logg C2 C3 C4 c5 c6 C7 C8 C0 hK hn hn' hOm hSK hth hh hh' hPl hg0 hm hN hL hLLa hLa hc5 hc6 hT hg
    p2 p3 p4 p5 p6 p7 p8 hC0
  have hEpos : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hE : (Fintype.card Emb : ℝ) ≠ 0 := hEpos.ne'
  have hf : 0 ≤ f := le_trans (Nat.cast_nonneg _) hPl
  have hF2 : 0 ≤ f * N ^ 2 := mul_nonneg hf (sq_nonneg N)
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hm3 : 1 ≤ m ^ 3 := by nlinarith
  have hm23 : m ^ 2 ≤ m ^ 3 := by nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm)]
  have hm13 : m ≤ m ^ 3 := by nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm2)]
  have hmL1 : L ≤ m ^ 3 * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hm3) hL]
  have hmL2 : m * L ≤ m ^ 3 * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hm13) hL]
  have hLa0 : 0 ≤ La := le_trans zero_le_one hLa
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have hNL : 1 ≤ N ^ 2 * La := by nlinarith
  have hX : 0 ≤ f * N ^ 2 * La := mul_nonneg hF2 hLa0
  have hY : 0 ≤ f * m ^ 3 * N ^ 2 * L :=
    mul_nonneg (mul_nonneg (mul_nonneg hf (pow_nonneg hm0 3)) (sq_nonneg N)) hL
  have v1 : C7 * (m * L) ≤ C7 * (m ^ 3 * L) := mul_le_mul_of_nonneg_left hmL2 p7
  have v2 : C8 * L ≤ C8 * (m ^ 3 * L) := mul_le_mul_of_nonneg_left hmL1 p8
  have q1 : 0 ≤ C2 * (C7 + C8) := mul_nonneg p2 (add_nonneg p7 p8)
  have q2 : 0 ≤ C4 * (1 + C7 + C8) := mul_nonneg p4 (add_nonneg (add_nonneg zero_le_one p7) p8)
  have k1 : (C3 + c5 + 2 * c6 + 1) * (f * N ^ 2 * La) ≤ C0 * (f * N ^ 2 * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX
  have k2 : (2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) + 2 * C8) * (f * m ^ 3 * N ^ 2 * L) ≤
      C0 * (f * m ^ 3 * N ^ 2 * L) :=
    mul_le_mul_of_nonneg_right (by linarith) hY
  have main : ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) ≤
      (Fintype.card Emb : ℝ) * sizeB ν logOm f m N L La C0 j := by
    intro j
    have hc1 : 0 ≤ (Fintype.card Pl : ℝ) * g0 j := mul_nonneg (Nat.cast_nonneg _) (hg0 j).1
    have hc1' : (Fintype.card Pl : ℝ) * g0 j ≤ f * N ^ 2 := mul_le_mul hPl (hg0 j).2 (hg0 j).1 hf
    have hterm : ∀ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j)) ≤
        (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) + (Fintype.card Pl : ℝ) * g0 j * logth0 s + ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
            2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
            (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) +
            (logn j + logn' j)) := by
      intro s
      have := hSK j s
      unfold liftedMapLogSize
      linarith
    have hsum : (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) ≤
        (∑ s, (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s))) + (Fintype.card Pl : ℝ) * g0 j * (∑ s, logth0 s) +
          (Fintype.card Emb : ℝ) * ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
            2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
            (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) +
            (logn j + logn' j)) := by
      refine le_trans (Finset.sum_le_sum (fun s _ => hterm s)) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hA : (∑ s, (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s))) =
        (Fintype.card Emb : ℝ) * ∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, (div_eq_iff hE).mp (hOm τ), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    have hth' : (∑ s, logth0 s) ≤ C3 * L * (Fintype.card Emb : ℝ) := (div_le_iff₀ hEpos).mp hth
    have hth'' : (Fintype.card Pl : ℝ) * g0 j * (∑ s, logth0 s) ≤
        (Fintype.card Pl : ℝ) * g0 j * (C3 * L * (Fintype.card Emb : ℝ)) :=
      mul_le_mul_of_nonneg_left hth' hc1
    have t1 : (Fintype.card Pl : ℝ) * g0 j * (C3 * L) ≤ f * N ^ 2 * (C3 * La) :=
      mul_le_mul hc1' (mul_le_mul_of_nonneg_left hLLa p3) (mul_nonneg p3 hL) hF2
    have t2a : (Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤
        (Fintype.card Pl : ℝ) * g0 j * (c5 * La) := mul_le_mul_of_nonneg_left (hc5 j) hc1
    have t2b : (Fintype.card Pl : ℝ) * g0 j * (c5 * La) ≤ f * N ^ 2 * (c5 * La) :=
      mul_le_mul_of_nonneg_right hc1' (mul_nonneg p5 hLa0)
    have hq : 0 ≤ 1 + 2 * (N ^ 2 * (c6 * La)) := by
      have := mul_nonneg (sq_nonneg N) (mul_nonneg p6 hLa0)
      linarith
    have t3 : (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) ≤
        f * (1 + 2 * (N ^ 2 * (c6 * La))) := by
      calc (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2)))
          ≤ ∑ _τ : Pl, (1 + 2 * (N ^ 2 * (c6 * La))) := Finset.sum_le_sum (fun τ _ => by
            have h1 : g0 j * Real.log (2 * (∑ i, ν j τ i) + 2) ≤ g0 j * (c6 * La) :=
              mul_le_mul_of_nonneg_left (hc6 j τ) (hg0 j).1
            have h2 : g0 j * (c6 * La) ≤ N ^ 2 * (c6 * La) :=
              mul_le_mul_of_nonneg_right (hg0 j).2 (mul_nonneg p6 hLa0)
            linarith)
        _ = (Fintype.card Pl : ℝ) * (1 + 2 * (N ^ 2 * (c6 * La))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ f * (1 + 2 * (N ^ 2 * (c6 * La))) := mul_le_mul_of_nonneg_right hPl hq
    have t4 : f * 1 ≤ f * (N ^ 2 * La) := mul_le_mul_of_nonneg_left hNL hf
    have t5 : C2 * f * m ^ 2 * N ^ 2 * (logg + logT) ≤ C2 * f * m ^ 2 * N ^ 2 * (C8 * L + C7 * m * L) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg (mul_nonneg p2 hf) (sq_nonneg m)) (sq_nonneg N))
    have t5b : C2 * f * N ^ 2 * (C8 * L) * m ^ 2 ≤ C2 * f * N ^ 2 * (C8 * L) * m ^ 3 :=
      mul_le_mul_of_nonneg_left hm23
        (mul_nonneg (mul_nonneg (mul_nonneg p2 hf) (sq_nonneg N)) (mul_nonneg p8 hL))
    have u : L + logT + logg ≤ m ^ 3 * L + C7 * (m ^ 3 * L) + C8 * (m ^ 3 * L) := by linarith
    have t6 : C4 * f * N ^ 2 * (L + logT + logg) ≤
        C4 * f * N ^ 2 * (m ^ 3 * L + C7 * (m ^ 3 * L) + C8 * (m ^ 3 * L)) :=
      mul_le_mul_of_nonneg_left u (mul_nonneg (mul_nonneg p4 hf) (sq_nonneg N))
    have t7 : f * N ^ 2 * logg ≤ f * N ^ 2 * (C8 * (m ^ 3 * L)) :=
      mul_le_mul_of_nonneg_left (le_trans hg v2) hF2
    have hZ : (Fintype.card Pl : ℝ) * g0 j * (C3 * L) + ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
            2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
            (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) +
            (logn j + logn' j)) ≤
        C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) := by
      linarith [hh j, hh' j, hn j, hn' j]
    have hZE := mul_le_mul_of_nonneg_left hZ hEpos.le
    rw [hA] at hsum
    unfold sizeB
    linarith
  have cnn : ∀ j, 0 ≤ sizeB ν logOm f m N L La C0 j -
      (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) / (Fintype.card Emb : ℝ) :=
    fun j => sub_nonneg.mpr ((div_le_iff₀ hEpos).mpr (by linarith [main j]))
  refine ⟨fun j => sizeB ν logOm f m N L La C0 j -
      (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) / (Fintype.card Emb : ℝ), cnn, ?_, ?_⟩
  · intro j s
    have := hK j s
    have := cnn j
    linarith
  · intro j
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
namespace CB
end CB
end Formalism.DimensionVariation
end

set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : StepDiCB := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' logn logn' hK logOm v f m N L La logT
    logg C2 C3 C4 c5 c6 C7 C8 C0 hK0 hn hn' hKd hOm hSK hth hh hh' hPl hg0 hm hN hL hLLa hLa hc5 hc6
    hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨cst, -, hc1, hc2⟩ := perEmbCore_lemma J Pl Emb r ν g0 logK MainNotions logOmτ logth0 logh logh'
    logn logn' logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hK0 hn hn' hOm hSK hth hh hh' hPl
    hg0 hm hN hL hLLa hLa hc5 hc6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have hEpos : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hB : ∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j := by
    intro j
    rw [hKd j, ← hc2 j]
    gcongr
    exact hc1 j _
  refine ⟨fun j s => ?_, fun j s => ?_, fun j s => ?_, hB,
    fun j => C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L), ?_⟩
  · have := hK0 j s
    unfold liftedMapLogSize at this ⊢
    linarith
  · have := hSK j s
    have := hn j
    have := hn' j
    linarith
  · have := hK0 j s
    unfold liftedMapLogSize at this ⊢
    linarith
  · unfold DiHyp6
    refine ⟨fun j => ?_, fun j => le_refl _⟩
    have := hB j
    unfold sizeB at this
    exact this
end Formalism.DimensionVariation
