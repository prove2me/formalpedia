-- Prove2me | solution 1 for Formalism.DimensionVariation.first_descent_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:18.5218+00:00
-- url     : https://prove2.me/submissions/8f4dba78-edd2-4b3a-9d79-e43d762bce48

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : StepDi6 := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' hK logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 h32 hmean hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have main : ∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j := by
    intro j
    unfold liftedMapLogSize at h32
    unfold sizeB
    have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := by exact_mod_cast Fintype.card_pos
    set E : ℝ := (Fintype.card Emb : ℝ) with hEdef
    set F : ℝ := (Fintype.card Pl : ℝ) with hFdef
    have hF0 : 0 ≤ F := Nat.cast_nonneg _
    have hf0 : 0 ≤ f := le_trans hF0 hcard
    have hLa0 : 0 ≤ La := le_trans hL hLLa
    obtain ⟨hG0, hGN⟩ := hg0 j
    have hOm' : ∀ τ, ∑ s, logOmτ τ s = logOm * E := fun τ => (div_eq_iff hE.ne').mp (hOm τ)
    have hth' : ∑ s, logth0 s ≤ C3 * L * E := (div_le_iff₀ hE).mp hth

    set X : ℝ := F * g0 j * (c5 * La) + 2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
      F * (1 + 2 * g0 j * (c6 * La)) + 2 * (C4 * f * N ^ 2 * (L + logT + logg)) with hX
    have hs : ∀ s, logK j s ≤ (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
        F * g0 j * logth0 s + X := by
      intro s
      have a1 : F * g0 j * Real.log (8 + 32 * (F * g0 j) * v) ≤ F * g0 j * (c5 * La) :=
        mul_le_mul_of_nonneg_left (h5 j) (mul_nonneg hF0 hG0)
      have a2 : (∑ τ : Pl, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) ≤
          F * (1 + 2 * g0 j * (c6 * La)) := by
        calc (∑ τ : Pl, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2)))
            ≤ ∑ _τ : Pl, (1 + 2 * g0 j * (c6 * La)) := by
              refine Finset.sum_le_sum (fun τ _ => ?_)
              have := mul_le_mul_of_nonneg_left (h6 j τ) (by linarith : 0 ≤ 2 * g0 j)
              linarith
          _ = F * (1 + 2 * g0 j * (c6 * La)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have a3 := hSK j s
      have a4 := hh j
      have a5 := hh' j
      have a6 := h32 j s
      rw [hX]; linarith
    have hsum : ∑ s, logK j s ≤
        E * (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm)) + F * g0 j * (C3 * L * E) + E * X := by
      calc ∑ s, logK j s ≤ ∑ s, ((∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
            F * g0 j * logth0 s + X) := Finset.sum_le_sum (fun s _ => hs s)
        _ = (∑ τ, ∑ s, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
            F * g0 j * (∑ s, logth0 s) + E * X := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
              simp [hEdef]
        _ = E * (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm)) +
            F * g0 j * (∑ s, logth0 s) + E * X := by
              congr 2
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun τ _ => ?_)
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hOm' τ]
              simp [hEdef]; ring
        _ ≤ _ := by
              have := mul_le_mul_of_nonneg_left hth' (mul_nonneg hF0 hG0)
              linarith

    have hN2 : 0 ≤ N ^ 2 := by positivity
    have hN21 : 1 ≤ N ^ 2 := one_le_pow₀ hN
    have hm2 : 0 ≤ m ^ 2 := by positivity
    have hm3 : m ≤ m ^ 3 := le_self_pow₀ hm (by norm_num)
    have hFG : F * g0 j ≤ f * N ^ 2 := mul_le_mul hcard hGN hG0 hf0
    have hfN : 0 ≤ f * N ^ 2 := mul_nonneg hf0 hN2
    have t1 : F * g0 j * (C3 * L) ≤ C3 * (f * N ^ 2 * La) := by
      have b1 : C3 * L ≤ C3 * La := mul_le_mul_of_nonneg_left hLLa p3
      have := mul_le_mul hFG b1 (mul_nonneg p3 hL) hfN
      linarith
    have t2 : F * g0 j * (c5 * La) ≤ c5 * (f * N ^ 2 * La) := by
      have := mul_le_mul_of_nonneg_right hFG (mul_nonneg p5 hLa0)
      linarith
    have hmL : L ≤ m * L := le_mul_of_one_le_left hL hm
    have hmL0 : 0 ≤ m * L := by positivity
    have hC8 : C8 * L ≤ C8 * (m * L) := mul_le_mul_of_nonneg_left hmL p8
    have t3 : 2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) ≤
        2 * C2 * (C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by
      have b0 : (C7 + C8) * (m * L) = C7 * m * L + C8 * (m * L) := by ring
      have b1 : logg + logT ≤ (C7 + C8) * (m * L) := by rw [b0]; linarith
      have b2 : 0 ≤ C2 * f * m ^ 2 * N ^ 2 := by positivity
      have b3 := mul_le_mul_of_nonneg_left b1 b2
      have b4 : C2 * f * m ^ 2 * N ^ 2 * ((C7 + C8) * (m * L)) =
          C2 * (C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by ring
      rw [b4] at b3
      linarith
    have t4 : F * (1 + 2 * g0 j * (c6 * La)) ≤ f * N ^ 2 * La + 2 * c6 * (f * N ^ 2 * La) := by
      have c0 : 0 ≤ c6 * La := mul_nonneg p6 hLa0
      have b0 := mul_le_mul_of_nonneg_right hGN c0
      have b1 : 1 + 2 * g0 j * (c6 * La) ≤ 1 + 2 * N ^ 2 * (c6 * La) := by linarith
      have b2 : F * (1 + 2 * g0 j * (c6 * La)) ≤ f * (1 + 2 * N ^ 2 * (c6 * La)) :=
        mul_le_mul hcard b1 (by positivity) hf0
      have b3 : f ≤ f * N ^ 2 * La := by
        have b5 : 1 ≤ N ^ 2 * La := one_le_mul_of_one_le_of_one_le hN21 hLa
        have b6 := mul_le_mul_of_nonneg_left b5 hf0
        linarith
      have b4 : f * (1 + 2 * N ^ 2 * (c6 * La)) = f + 2 * c6 * (f * N ^ 2 * La) := by ring
      rw [b4] at b2
      linarith
    have t5 : 2 * (C4 * f * N ^ 2 * (L + logT + logg)) ≤
        2 * C4 * (1 + C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by
      have b0 : (1 + C7 + C8) * (m * L) = m * L + C7 * m * L + C8 * (m * L) := by ring
      have b1 : L + logT + logg ≤ (1 + C7 + C8) * (m * L) := by rw [b0]; linarith
      have b3 : (1 + C7 + C8) * (m * L) ≤ (1 + C7 + C8) * (m ^ 3 * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm3 hL) (by linarith)
      have b2 : 0 ≤ C4 * f * N ^ 2 := by positivity
      have b4 := mul_le_mul_of_nonneg_left (le_trans b1 b3) b2
      have b5 : C4 * f * N ^ 2 * ((1 + C7 + C8) * (m ^ 3 * L)) =
          C4 * (1 + C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by ring
      rw [b5] at b4
      linarith
    have hU : 0 ≤ f * N ^ 2 * La := mul_nonneg hfN hLa0
    have hW : 0 ≤ f * m ^ 3 * N ^ 2 * L := by positivity
    have k1 : 0 ≤ 2 * C2 * (C7 + C8) := by positivity
    have k2 : 0 ≤ 2 * C4 * (1 + C7 + C8) := by positivity
    have u1 : (C3 + c5 + 2 * c6 + 1) * (f * N ^ 2 * La) ≤ C0 * (f * N ^ 2 * La) :=
      mul_le_mul_of_nonneg_right (by linarith) hU
    have u3 : (2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8)) * (f * m ^ 3 * N ^ 2 * L) ≤
        C0 * (f * m ^ 3 * N ^ 2 * L) := mul_le_mul_of_nonneg_right (by linarith) hW
    have hfin : F * g0 j * (C3 * L) + X ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) := by
      have e0 : C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) =
          C0 * (f * N ^ 2 * La) + C0 * (f * m ^ 3 * N ^ 2 * L) := by ring
      rw [hX, e0]; linarith
    show hK j ≤ (∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm)) +
      C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)
    rw [hmean j, div_le_iff₀ hE]
    have hfinE := mul_le_mul_of_nonneg_left hfin hE.le
    linarith

  refine ⟨main, fun _ => C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L), ?_, fun j => le_rfl⟩
  intro j
  have := main j
  unfold sizeB at this
  exact this
end Formalism.DimensionVariation
