-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_InstSizes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:42.837837+00:00
-- url     : https://prove2.me/submissions/eb01e144-bffe-44fb-ae70-aa7bc8673ec4

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_rd_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_sqrt_idl
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_BlockLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_sp_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_supA_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_thrS_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_lamHat_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_memS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_memP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : InstSizes := by
  intro hL hI hN hDeg hFP hX E W _ _ _ D e G C de de' T T' l Θ hU hInst hg1 hg2 hC hlen hΘ hGr
  obtain ⟨hr, hK, hPl, hv, hLa, hLap, hLad, hszD, hszL, hvol⟩ := hInst
  have hgN : 0 < G.g1 * G.g2 := Nat.mul_pos hg1 hg2
  have hGg : G.g = ((G.g1 * G.g2 : ℕ) : ℝ) := by unfold Sz.Glob.g; push_cast; ring
  have hgpos : 0 < G.g := by rw [hGg]; exact_mod_cast hgN
  have hrd := rd_pos E
  have hka : G.ka = 2 * Real.pi / S6.rd E := by
    unfold Sz.Glob.ka; rw [hv]; field_simp
  have hkapos : 0 < G.ka := by rw [hka]; have := Real.pi_pos; positivity
  have hcard : Fintype.card (InfinitePlace E) = S6.deg E := (hDeg E).2.1
  have hf : D.f = Fintype.card (InfinitePlace E) := by simpa using Fintype.card_congr e
  have hGf : G.f = Fintype.card (InfinitePlace E) := rfl
  have hM : ∀ x ∈ G.thrSet C de de' T T' l, x ≤ (Θ ^ G.f)⁻¹ := fun x hx => hGr.2 hx
  have BL := fun b s => t_BlockLattices hL hI hN E hU (G.g1 * G.g2) G.r b s hgN

  have key : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → ∀ w, thrS G C de de' T T' l b s w *
      (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) =
      Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w) := by
    intro b s hb hs w
    have := (hFP G.r b s C (S6.rd E) G.g G.N G.lenI
      (supA G de de' T T' l (decide (b = 1 ∧ s = 1)) w) 0 hb hs hrd hgpos).1
    unfold thrS
    rw [show G.m = 2 * G.r + 2 from rfl, this, ← hka]
    congr 1
    exact supA_mul G de de' T T' l hgpos hkapos _ w
  have keyP : ∀ b : ℕ, 1 ≤ b → ∀ w, thrP G C de de' T T' l b w *
      (G.g * S6.rd E ^ (S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
      Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') := by
    intro b hb w
    have := (hFP G.r b 1 C (S6.rd E) G.g G.N G.lenI
      (supA G de de' T T' l false w) (T * T') hb le_rfl hrd hgpos).2
    unfold thrP
    rw [show G.m = 2 * G.r + 2 from rfl, this, ← hka]
    congr 1
    exact supA_mul G de de' T T' l hgpos hkapos False w

  have prodkey : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → ∏ w, thrS G C de de' T T' l b s w =
      (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)) *
        √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
    intro b s hb hs
    have hc : 0 < G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1) := by positivity
    unfold S6.dualIdl
    rw [sqrt_idl hN E _ _ hgN, ← hGg, ← hcard, ← Finset.card_univ, ← Finset.prod_const,
      ← div_eq_mul_inv, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun w _ => eq_div_of_mul_eq hc.ne' (key b s hb hs w)
  have Ppos : ∀ b s : ℕ, 0 ≤ ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g
      (sp G de de' T T' l (b = 1 ∧ s = 1) w) := fun b s =>
    Finset.prod_nonneg fun w _ => lamHat_nonneg G C hgpos hkapos hC hlen b s _
      (sp_nonneg G de de' T T' l hgpos.le hkapos.le _ w)
  have Ple : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → b + s ≤ G.r + 2 →
      ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w) ≤
        (Θ ^ G.f)⁻¹ := fun b s hb hs hbs => hM _ (memS G C de de' T T' l hX b s hb hs hbs)
  have Npos : ∀ ν : ℤ, 0 < √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) ν) : ℝ) := by
    intro ν
    unfold S6.dualIdl
    rw [sqrt_idl hN E _ _ hgN]
    have : (0 : ℝ) < ((G.g1 * G.g2 : ℕ) : ℝ) := by exact_mod_cast hgN
    positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro b s
    rw [hvol]
    apply div_nonneg (sq_nonneg _)
    exact_mod_cast FractionalIdeal.absNorm_nonneg _
  · intro b s hb hs hbs
    rw [hr] at hbs
    rw [hvol, prodkey b s hb hs, mul_pow, Real.sq_sqrt (Real.sqrt_pos.1 (Npos _)).le,
      mul_div_assoc, div_self (Real.sqrt_pos.1 (Npos _)).ne', mul_one, hf, ← hGf]
    exact pow_le_pow_left₀ (Ppos b s) (Ple b s hb hs hbs) 2
  · intro i hi1 hi2
    rw [hr] at hi2
    refine ⟨(BL i 1).2.2.2.1, ?_, fun v => ?_, ?_⟩
    · intro x hx; rw [hLad] at hx; exact (BL i 1).1 x hx
    · rw [hszD]; exact thrS_nonneg G C de de' T T' l hgpos hkapos hC hlen _ _ _
    · have h1 : ∏ v, D.szD i v = ∏ w, thrS G C de de' T T' l i 1 w := by
        rw [← Equiv.prod_comp e]; exact Finset.prod_congr rfl fun v _ => hszD i v
      rw [h1]
      have h2 := prodkey i 1 hi1 le_rfl
      rw [Nat.cast_one] at h2
      beta_reduce
      rw [h2, one_div, inv_pow, hf, ← hGf]
      exact mul_le_mul_of_nonneg_right (Ple i 1 hi1 le_rfl (by omega)) (Real.sqrt_nonneg _)
  · intro b s hb hs hbs hne
    rw [hr] at hbs hne
    refine ⟨(BL b s).2.2.2.2.1, ?_, fun v => ?_, ?_⟩
    · intro x hx; rw [hLap] at hx; exact (BL b s).2.2.1 x hx
    · rw [hszL]; split_ifs
      · exact thrS_nonneg G C de de' T T' l hgpos hkapos hC hlen _ _ _
      · unfold thrP; positivity
    · have h2Θ : (Θ ^ G.f)⁻¹ ≤ (2 / Θ) ^ D.f := by
        rw [hf, ← hGf, div_pow, div_eq_mul_inv]
        have : (1 : ℝ) ≤ 2 ^ G.f := one_le_pow₀ (by norm_num)
        have h0 : 0 ≤ (Θ ^ G.f)⁻¹ := by positivity
        nlinarith
      by_cases hc : b + s ≤ G.r + 1
      · have h1 : ∏ v, D.szL b s v = ∏ w, thrS G C de de' T T' l b (s + 1) w := by
          rw [← Equiv.prod_comp e]
          exact Finset.prod_congr rfl fun v _ => by rw [hszL, if_pos hc]
        beta_reduce
        rw [h1, prodkey b (s + 1) hb (by omega), (BL b s).2.2.2.2.2.1]
        exact mul_le_mul_of_nonneg_right ((Ple b (s + 1) hb (by omega) (by omega)).trans h2Θ)
          (Real.sqrt_nonneg _)
      · have hs' : (s : ℤ) = (G.r : ℤ) + 2 - b := by omega
        have h1 : ∏ v, D.szL b s v = 2 ^ D.f * ∏ w, thrP G C de de' T T' l b w := by
          calc ∏ v, D.szL b s v = ∏ v, (2 * thrP G C de de' T T' l b (e v)) :=
                Finset.prod_congr rfl fun v _ => by rw [hszL, if_neg hc]
            _ = 2 ^ D.f * ∏ v, thrP G C de de' T T' l b (e v) := by
                rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ = _ := by rw [Equiv.prod_comp e (fun w => thrP G C de de' T T' l b w)]
        have hcpos : 0 < G.g * S6.rd E ^ (S6.nuBlock G.r b s) := by positivity
        have h2 : ∏ w, thrP G C de de' T T' l b w =
            (∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')) *
              √(FractionalIdeal.absNorm (S6.liftIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
          unfold S6.liftIdl
          rw [sqrt_idl hN E _ _ hgN, ← hGg, ← hcard, ← Finset.card_univ, ← Finset.prod_const,
            ← div_eq_mul_inv, ← Finset.prod_div_distrib]
          refine Finset.prod_congr rfl fun w _ => eq_div_of_mul_eq hcpos.ne' ?_
          rw [hs']; exact keyP b hb w
        beta_reduce
        rw [h1, h2, ← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h3 := hM _ (memP G C de de' T T' l b hb (by omega))
        rw [div_pow, div_eq_mul_inv, hf, ← hGf]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
  · unfold TB.Data.Ntop Sz.Glob.N
    rw [hK, hr]; push_cast; ring
end Formalism.FourierDecayAlt.P.Jx7
