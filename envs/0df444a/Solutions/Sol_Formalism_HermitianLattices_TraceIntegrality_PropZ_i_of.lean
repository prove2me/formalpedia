-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.PropZ_i_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:45.785466+00:00
-- url     : https://prove2.me/submissions/87663f44-671b-4128-bba3-d6f2ad8e485c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentArithmeticBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
private lemma mean_le_of_le_const {σ : Type} [Fintype σ] [Nonempty σ] (F : σ → ℝ) (B : ℝ)
    (h : ∀ s, F s ≤ B) : mean F ≤ B := by
  unfold mean
  have hc : (0:ℝ) < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc]
  calc ∑ s, F s ≤ ∑ _s : σ, B := Finset.sum_le_sum fun s _ => h s
    _ = B * (Fintype.card σ : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
private lemma mean_le_mean_of_le {σ : Type} [Fintype σ] (F G : σ → ℝ) (h : ∀ s, F s ≤ G s) :
    mean F ≤ mean G := by
  unfold mean
  gcongr with s
  exact h s
private lemma mean_add_distrib {σ : Type} [Fintype σ] (F G : σ → ℝ) :
    mean (fun s => F s + G s) = mean F + mean G := by
  simp only [mean]
  rw [Finset.sum_add_distrib, add_div]
private lemma mean_sum_comm {σ J : Type} [Fintype σ] [Fintype J] (F : J → σ → ℝ) :
    mean (fun s => ∑ j, F j s) = ∑ j, mean (F j) := by
  simp only [mean]
  rw [Finset.sum_comm, Finset.sum_div]
private lemma square_moment_arithmetic_bound (C₀ L logT logg b' : ℝ) (m N : ℕ) (hC : 0 ≤ C₀) (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hT : logT ≤ C₀ * m * L) (hg : logg ≤ C₀ * L) (hb : (1 + 2 * C₀) * (m : ℝ) ^ 3 * N ≤ b') :
    (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ N * b' * L := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hCL : 0 ≤ C₀ * L := mul_nonneg hC hL0
  have e1 : C₀ * L ≤ C₀ * m * L := by nlinarith [mul_nonneg hCL (sub_nonneg.2 hm')]
  have e2 : L ≤ m * L := by nlinarith [mul_nonneg (sub_nonneg.2 hm') hL0]
  have h1 : L + logT + logg ≤ (1 + 2 * C₀) * m * L := by linarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  calc (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)
      ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * ((1 + 2 * C₀) * m * L) := by gcongr
    _ = ((1 + 2 * C₀) * (m : ℝ) ^ 3 * N) * (N * L) := by ring
    _ ≤ b' * (N * L) := mul_le_mul_of_nonneg_right hb (mul_nonneg hN0 hL0)
    _ = N * b' * L := by ring
private lemma first_part_arithmetic_bound (C₀ C2 C3 f tt M tr Nn b' L logT eta S : ℝ) (hC : 0 ≤ C₀) (hf0 : 0 ≤ f)
    (htt0 : 0 ≤ tt) (htt : tt ≤ f) (hm1 : 1 ≤ M) (hNn1 : 1 ≤ Nn) (hb1 : 1 ≤ b') (hL : 1 ≤ L)
    (hT0 : 0 ≤ logT) (hTle : logT ≤ C₀ * M * L) (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ M * tr)
    (hsmall : S + eta + M * tr ≤ b') (hNL : Nn * L ≤ b') :
    C3 * tt * b' * (logT + Nn * L) + C3 * f * (eta + 3 * S + M * tr) * (logT + Nn * L)
      + C3 * f * Nn ^ 2 * L + M * (C2 * f * Nn * b' * L)
      ≤ (|C2| + |C3| * (4 * (C₀ + 1) + 1)) * f * M * Nn * b' * L := by
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hN0 : (0:ℝ) ≤ Nn := by linarith
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hQ : 0 ≤ M * Nn * L := mul_nonneg (mul_nonneg hM0 hN0) hL0
  have hX0 : 0 ≤ logT + Nn * L := by nlinarith
  have hX : logT + Nn * L ≤ (C₀ + 1) * (M * Nn * L) := by
    have h1 : C₀ * M * L ≤ C₀ * M * Nn * L := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC hM0) hL0) (sub_nonneg.2 hNn1)]
    have h2 : Nn * L ≤ M * Nn * L := by
      nlinarith [mul_nonneg (mul_nonneg hN0 hL0) (sub_nonneg.2 hm1)]
    nlinarith
  have hY0 : 0 ≤ eta + 3 * S + M * tr := by linarith
  have hY : eta + 3 * S + M * tr ≤ 3 * b' := by linarith
  have k1 : tt * b' * (logT + Nn * L) ≤ f * b' * ((C₀ + 1) * (M * Nn * L)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right htt hb0) hX hX0 (mul_nonneg hf0 hb0)
  have t1 : C3 * tt * b' * (logT + Nn * L) ≤ |C3| * (f * b' * ((C₀ + 1) * (M * Nn * L))) := by
    calc C3 * tt * b' * (logT + Nn * L) = C3 * (tt * b' * (logT + Nn * L)) := by ring
      _ ≤ |C3| * (tt * b' * (logT + Nn * L)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (mul_nonneg htt0 hb0) hX0)
      _ ≤ |C3| * (f * b' * ((C₀ + 1) * (M * Nn * L))) := mul_le_mul_of_nonneg_left k1 (abs_nonneg _)
  have k2 : f * (eta + 3 * S + M * tr) * (logT + Nn * L) ≤ f * (3 * b') * ((C₀ + 1) * (M * Nn * L)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hY hf0) hX hX0 (mul_nonneg hf0 (by linarith))
  have t2 : C3 * f * (eta + 3 * S + M * tr) * (logT + Nn * L)
      ≤ |C3| * (f * (3 * b') * ((C₀ + 1) * (M * Nn * L))) := by
    calc C3 * f * (eta + 3 * S + M * tr) * (logT + Nn * L)
        = C3 * (f * (eta + 3 * S + M * tr) * (logT + Nn * L)) := by ring
      _ ≤ |C3| * (f * (eta + 3 * S + M * tr) * (logT + Nn * L)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (mul_nonneg hf0 hY0) hX0)
      _ ≤ _ := mul_le_mul_of_nonneg_left k2 (abs_nonneg _)
  have hML : 1 ≤ M * L := by nlinarith
  have a1 : Nn ^ 2 * L ≤ Nn * b' := by
    calc Nn ^ 2 * L = Nn * (Nn * L) := by ring
      _ ≤ Nn * b' := mul_le_mul_of_nonneg_left hNL hN0
  have a2 : Nn * b' ≤ M * Nn * b' * L := by
    calc Nn * b' = Nn * b' * 1 := by ring
      _ ≤ Nn * b' * (M * L) := mul_le_mul_of_nonneg_left hML (mul_nonneg hN0 hb0)
      _ = M * Nn * b' * L := by ring
  have k3 : f * Nn ^ 2 * L ≤ f * (M * Nn * b' * L) := by
    calc f * Nn ^ 2 * L = f * (Nn ^ 2 * L) := by ring
      _ ≤ f * (M * Nn * b' * L) := mul_le_mul_of_nonneg_left (a1.trans a2) hf0
  have t3 : C3 * f * Nn ^ 2 * L ≤ |C3| * (f * (M * Nn * b' * L)) := by
    calc C3 * f * Nn ^ 2 * L = C3 * (f * Nn ^ 2 * L) := by ring
      _ ≤ |C3| * (f * Nn ^ 2 * L) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (mul_nonneg hf0 (sq_nonneg _)) hL0)
      _ ≤ _ := mul_le_mul_of_nonneg_left k3 (abs_nonneg _)
  have t4 : M * (C2 * f * Nn * b' * L) ≤ |C2| * (f * M * Nn * b' * L) := by
    calc M * (C2 * f * Nn * b' * L) = C2 * (f * M * Nn * b' * L) := by ring
      _ ≤ |C2| * (f * M * Nn * b' * L) :=
          mul_le_mul_of_nonneg_right (le_abs_self _)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 hM0) hN0) hb0) hL0)
  linarith [t1, t2, t3, t4]
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution (h2 : MeanLogNormBound) (h3 : ZetaBoundApplication) : PropZ_i := by
  intro C₀ hC
  obtain ⟨C2, hC2⟩ := h2 C₀ hC
  obtain ⟨C3, hC3⟩ := h3 C₀ hC
  refine ⟨|C2| + |C3| * (4 * (C₀ + 1) + 1), ?_⟩
  intro ι σ _ _ _ _ TT T2 k m t n R nu A w bt lam sg a b' L v logT logg eta S logOm logOms logTh
    logK logP logPK hN hdis hR hanti htop htopj hthin hper hOm hTh hK hI hW hB0t hB0o hX hdt hdo
    hP hPK
  have hL := hN.one_le_L
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hb1 := hN.one_le_b'
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hg0 := hN.logg_nonneg
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hN.one_le_m
  have hm0 : (0:ℝ) ≤ m := by linarith
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hmt : (0:ℝ) ≤ (m:ℝ) * t := mul_nonneg hm0 ht0
  have ha0 : (0:ℝ) < a := by linarith
  have hloga : Real.log a ≤ L := by
    refine le_trans (Real.log_le_log ha0 ?_) hN.log_av
    nlinarith [hN.one_le_v]
  have hlin := hN.lin
  push_cast at hlin
  have hNL : ((n:ℝ) + 1) * L ≤ b' := by linarith
  have hsqm := square_moment_arithmetic_bound C₀ L logT logg b' m (n + 1) hC hL hN.one_le_m hN.logT_le hN.logg_le hN.pow
  have key2 : ∀ j, mean (logK j) ≤ ∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ τ ∈ T2, placeTerm (nu j τ) logOm + C2 * Fintype.card ι * ((n:ℝ) + 1) * b' * L := by
    intro j
    have := hC2 ι σ TT T2 (R j) (n + 1) m (nu j) A (w j) a b' L logT logg logOm logOms (logTh j)
      (logK j) hdis (hR j) hL hloga hb1 hba (by push_cast; exact hNL) hT0 hg0 hsqm (hanti j)
      (fun τ hτ => ⟨(htop τ hτ).1, (htop τ hτ).2.1, (htopj j τ hτ).1, (htopj j τ hτ).2.1,
        (htopj j τ hτ).2.2⟩)
      (hthin j) hper hOm (by push_cast; exact hTh j) (by push_cast; exact hK j)
    push_cast at this
    exact this
  have key3 := hC3 ι TT n lam sg (fun ρ => (A ρ : ℝ)) bt b' L logT eta S ((m:ℝ) * t)
    (∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT) hL hT0 hb0 hN.eta_nonneg hN.S_nonneg hmt hI hW
    (fun ρ h => (htop ρ h).2.2) hB0t hB0o hX hdt hdo le_rfl
  have hmean : mean logPK ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT + ∑ j, mean (logK j) := by
    calc mean logPK ≤ mean (fun s => logP s + ∑ j, logK j s) := mean_le_mean_of_le _ _ hPK
      _ = mean logP + ∑ j, mean (logK j) := by rw [mean_add_distrib, mean_sum_comm]
      _ ≤ _ := by gcongr; exact mean_le_of_le_const _ _ hP
  have hsum2 : ∑ j, mean (logK j) ≤ ∑ _j : Fin m, ∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ j : Fin m, ∑ τ ∈ T2, placeTerm (nu j τ) logOm
      + m * (C2 * Fintype.card ι * ((n:ℝ) + 1) * b' * L) := by
    calc ∑ j, mean (logK j) ≤ ∑ j : Fin m, (∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ τ ∈ T2, placeTerm (nu j τ) logOm + C2 * Fintype.card ι * ((n:ℝ) + 1) * b' * L) :=
          Finset.sum_le_sum fun j _ => key2 j
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have har := first_part_arithmetic_bound C₀ C2 C3 (Fintype.card ι) TT.card m t ((n:ℝ) + 1) b' L logT eta S hC
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast Finset.card_le_univ TT) hm1
    (by linarith) hb1 hL hT0 hN.logT_le hN.eta_nonneg hN.S_nonneg hmt hN.small hNL
  linarith
end Formalism.HermitianLattices.TraceIntegrality
