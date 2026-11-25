-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.instance_sizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:00.584718+00:00
-- url     : https://prove2.me/submissions/533806cd-c2dd-4820-96d9-1503bb2cf487

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Jx5_rd_pos__157dd2cb063d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_ka_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_thrS_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_thrP_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : InstSizes := by
  intro hLG hIM hNI hDF hFP hX E W _ _ _ D e G C de de' T T' l Θ hU hInst hg1 hg2 hC hI hΘ hGr
  obtain ⟨hr, hK, hPl, hv, hLa, hLap, hLad, hszD, hszL, hvol⟩ := hInst
  have hrd := rd_pos' (E := E)
  have hg : 0 < G.g := by
    unfold Sz.Glob.g
    have a1 : (0:ℝ) < G.g1 := by exact_mod_cast hg1
    have a2 : (0:ℝ) < G.g2 := by exact_mod_cast hg2
    positivity
  have hgN : 0 < G.g1 * G.g2 := Nat.mul_pos hg1 hg2
  have hgc : ((G.g1 * G.g2 : ℕ) : ℝ) = G.g := by unfold Sz.Glob.g; push_cast; ring
  obtain ⟨_, hcard, hdeg⟩ := hDF E
  have hfd : G.f = S6.deg E := hcard
  have hfD : D.f = G.f := by
    have := Fintype.card_congr e
    simpa [Sz.Glob.f] using this
  have hka0 : 0 < G.ka := by rw [ka_eq G hv]; positivity
  have hN0 : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have hND : ∀ ν : ℤ, √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) ν) : ℝ) =
      ((G.g * S6.rd E ^ (ν + 1)) ^ G.f)⁻¹ := by
    intro ν
    have := hNI E (G.g1 * G.g2) (-1) (-(ν + 1)) hgN
    unfold S6.dualIdl
    rw [this, hgc, hfd, ← inv_pow, mul_inv, zpow_neg, zpow_neg, zpow_one]
  have hNL : ∀ ν : ℤ, √(FractionalIdeal.absNorm (S6.liftIdl E (G.g1 * G.g2) ν) : ℝ) =
      ((G.g * S6.rd E ^ ν) ^ G.f)⁻¹ := by
    intro ν
    have := hNI E (G.g1 * G.g2) (-1) (-ν) hgN
    unfold S6.liftIdl
    rw [this, hgc, hfd, ← inv_pow, mul_inv, zpow_neg, zpow_neg, zpow_one]
  have hcp : ∀ ν : ℤ, 0 < G.g * S6.rd E ^ ν := fun ν => mul_pos hg (zpow_pos hrd _)
  have hbe : ∀ (w : InfinitePlace E) (Y : ℝ), 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y := by
    intro w Y
    exact mul_nonneg (pow_nonneg hg.le _)
      (mul_nonneg (inv_nonneg.2 (pow_nonneg hka0.le _)) (Real.sqrt_nonneg _))
  have hsI : ∀ w, 0 ≤ G.supI de de' T T' l w := by
    intro w; apply Real.sSup_nonneg; rintro x ⟨Y, _, rfl⟩; exact hbe w Y
  have hsI1 : ∀ w, 0 ≤ G.cutSupLong de de' T T' l w := by
    intro w; apply Real.sSup_nonneg; rintro x ⟨Y, _, rfl⟩; exact hbe w Y
  have hS0 : ∀ b s w, 0 ≤ supBS G de de' T T' l b s w := by
    intro b s w; unfold supBS; split_ifs
    · exact hsI1 w
    · exact hsI w
  have hlam0 : ∀ b s B, 0 ≤ B → 0 ≤ Sz.lamHat b s C G.ka G.N G.lenI G.g B := by
    intro b s B hB
    unfold Sz.lamHat
    exact mul_nonneg (mul_nonneg hC hB) (pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg hC hka0.le) hN0)
      (mul_nonneg hg.le hI.le)) _)

  have hPle : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ G.r + 2 →
      ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) ≤ (Θ ^ G.f)⁻¹ := by
    intro b s hb hs hbs
    apply hGr.2
    refine ⟨b, hb, by omega, ?_⟩
    by_cases h1 : s = 1
    · subst h1
      by_cases hb1 : b = 1
      · subst hb1
        left
        refine ⟨rfl, Finset.prod_congr rfl fun w _ => ?_⟩
        rw [(hX 0 1 C G.ka G.N G.lenI 0 G.g _).2]; simp [supBS]
      · right; left
        refine ⟨by omega, Finset.prod_congr rfl fun w _ => ?_⟩
        rw [(hX 0 b C G.ka G.N G.lenI 0 G.g _).2]; simp [supBS, hb1]
    · right; right; left
      refine ⟨s, by omega, by omega, Finset.prod_congr rfl fun w _ => ?_⟩
      simp [supBS, h1]
  have hQle : ∀ b, 1 ≤ b → b ≤ G.r + 1 →
      ∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') ≤ (Θ ^ G.f)⁻¹ := by
    intro b hb hb'
    apply hGr.2
    exact ⟨b, hb, hb', Or.inr (Or.inr (Or.inr rfl))⟩
  have hthrw : ∀ b s, 1 ≤ b → 1 ≤ s → ∀ w, thrS G C de de' T T' l b s w =
      Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) /
        (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) := by
    intro b s hb hs w
    rw [eq_div_iff (hcp _).ne']
    exact thrS_norm G C de de' T T' l hFP hv hg b s hb hs w
  have hthr : ∀ b s, 1 ≤ b → 1 ≤ s → ∏ w, thrS G C de de' T T' l b s w =
      (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w)) *
        ((G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) ^ G.f)⁻¹ := by
    intro b s hb hs
    rw [Finset.prod_congr rfl fun w _ => hthrw b s hb hs w, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, div_eq_mul_inv]
    rfl
  have hthr0 : ∀ b s, 1 ≤ b → 1 ≤ s → ∀ w, 0 ≤ thrS G C de de' T T' l b s w := by
    intro b s hb hs w
    rw [hthrw b s hb hs w]
    exact div_nonneg (hlam0 _ _ _ (hS0 _ _ _)) (hcp _).le
  have hP0 : ∀ b s, 0 ≤ ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) :=
    fun b s => Finset.prod_nonneg fun w _ => hlam0 _ _ _ (hS0 _ _ _)
  have hΘf : 0 < (Θ ^ G.f)⁻¹ := by positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro b s
    rw [hvol]
    exact div_nonneg (sq_nonneg _) (Rat.cast_nonneg.2 (FractionalIdeal.absNorm_nonneg _))
  · intro b s hb hs hbs
    rw [hr] at hbs
    rw [hvol, hthr b s hb hs, ← hND, hfD]
    have hn : 0 < √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
      rw [hND]; exact inv_pos.2 (pow_pos (hcp _) _)
    have hn' := Real.sqrt_pos.1 hn
    rw [mul_pow, Real.sq_sqrt hn'.le, mul_div_assoc, div_self hn'.ne', mul_one]
    exact pow_le_pow_left₀ (hP0 b s) (hPle b s hb hs hbs) 2
  · intro i hi hi'
    rw [hr] at hi'
    have hn : 0 < √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r i 1)) : ℝ) := by
      rw [hND]; exact inv_pos.2 (pow_pos (hcp _) _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      simp only at h0
      rw [h0] at hn
      simp at hn
    · intro x hx
      rw [hLad] at hx
      exact (hLG E hU (G.g1 * G.g2) (S6.nuBlock G.r i 1) 1 hgN).2.2.2.2.1 hx
    · intro v; rw [hszD]; exact hthr0 i 1 hi le_rfl _
    · rw [Finset.prod_congr rfl fun v _ => hszD i v,
        Equiv.prod_comp e (fun w => thrS G C de de' T T' l i 1 w)]
      have := hthr i 1 hi le_rfl
      push_cast at this
      rw [this, ← hND, hfD, one_div, inv_pow]
      exact mul_le_mul_of_nonneg_right (hPle i 1 hi le_rfl (by omega)) hn.le
  · intro b s hb hs hbs hne
    rw [hr] at hbs hne
    have hn : 0 < √(FractionalIdeal.absNorm (S6.liftIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
      rw [hNL]; exact inv_pos.2 (pow_pos (hcp _) _)
    have h2 : (Θ ^ G.f)⁻¹ ≤ (2 / Θ) ^ G.f := by
      rw [div_pow, div_eq_mul_inv]
      have : (1:ℝ) ≤ 2 ^ G.f := one_le_pow₀ (by norm_num)
      nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      simp only at h0
      rw [h0] at hn
      simp at hn
    · intro x hx
      rw [hLap] at hx
      exact (hLG E hU (G.g1 * G.g2) (S6.nuBlock G.r b s) s hgN).2.2.2.2.2.2.1 hx
    · intro v; rw [hszL]; split_ifs
      · exact hthr0 b (s + 1) hb (by omega) _
      · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · beta_reduce
      by_cases hc : b + s ≤ G.r + 1
      · rw [Finset.prod_congr rfl fun v _ => (by rw [hszL, if_pos hc] :
          D.szL b s v = thrS G C de de' T T' l b (s + 1) (e v)),
          Equiv.prod_comp e (fun w => thrS G C de de' T T' l b (s + 1) w), hthr b (s + 1) hb (by omega), hfD]
        have hν : S6.nuBlock G.r b ((s + 1 : ℕ) : ℤ) + 1 = S6.nuBlock G.r b s := by
          unfold S6.nuBlock; push_cast; ring
        rw [hν, ← hNL]
        exact mul_le_mul_of_nonneg_right (le_trans (hPle b (s + 1) hb (by omega) (by omega)) h2) hn.le
      · rw [Finset.prod_congr rfl fun v _ => (by rw [hszL, if_neg hc] :
          D.szL b s v = 2 * thrP G C de de' T T' l b (e v)),
          Equiv.prod_comp e (fun w => 2 * thrP G C de de' T T' l b w), hfD]
        have hν : ((G.r : ℤ) + 2 - b) = s := by
          have : b + s = G.r + 2 := by omega
          have : ((b + s : ℕ) : ℤ) = ((G.r + 2 : ℕ) : ℤ) := by rw [this]
          push_cast at this; linarith
        have hw : ∀ w, 2 * thrP G C de de' T T' l b w =
            2 * Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') /
              (G.g * S6.rd E ^ (S6.nuBlock G.r b s)) := by
          intro w
          rw [eq_div_iff (hcp _).ne', mul_assoc, ← hν]
          rw [thrP_norm G C de de' T T' l hFP hv hg b hb w]
        rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_div_distrib, Finset.prod_const,
          Finset.card_univ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, div_eq_mul_inv]
        change 2 ^ G.f * _ * ((G.g * S6.rd E ^ (S6.nuBlock G.r b s)) ^ G.f)⁻¹ ≤ _
        rw [← hNL, div_pow, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ hn.le
        exact mul_le_mul_of_nonneg_left (hQle b hb (by omega)) (by positivity)
  · unfold TB.Data.Ntop Sz.Glob.N
    rw [hK, hr]; push_cast; ring
end Formalism.FourierDecayAlt.P
