-- Prove2me | solution 1 for Bl.CofiniteContinuousBounds.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:15.082972+00:00
-- url     : https://prove2.me/submissions/63b67514-653b-49d5-8824-c6ea8cdac13e

import Mathlib
import Definitions.Def_Lemmata_CofiniteContinuousBounds_LeOfCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.CofiniteContinuousBounds
private lemma le_of_cofinite {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {S : Set ℂ} (hS : S.Finite) (h : ∀ s, s ∉ S → f s ≤ g s) (s : ℂ) : f s ≤ g s := by
  have hd : Dense Sᶜ := hS.countable.dense_compl ℂ
  have hc : IsClosed {x | f x ≤ g x} := isClosed_le hf hg
  have hsub : closure Sᶜ ⊆ {x | f x ≤ g x} := hc.closure_subset_iff.2 (fun x hx => h x hx)
  exact hsub (hd s)
open Polynomial in
private lemma cont_bound (K : ℝ) (m : ℕ) (q : ℂ[X]) :
    Continuous fun s : ℂ => K * (1 + ‖s‖) ^ m * ‖q.eval s‖ :=
  (continuous_const.mul ((continuous_const.add continuous_norm).pow m)).mul
    (Polynomial.continuous q).norm
open Polynomial in
private lemma key (K : ℝ) (m : ℕ) (n : ℕ) : ∀ (p q : ℂ[X]), q.natDegree = n → q ≠ 0 →
    (∀ s : ℂ, ‖p.eval s‖ ≤ K * (1 + ‖s‖) ^ m * ‖q.eval s‖) → q ∣ p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p q hn hq h
  by_cases h0 : q.natDegree = 0
  · rw [natDegree_eq_zero] at h0
    obtain ⟨c, rfl⟩ := h0
    have hc : c ≠ 0 := fun hc => hq (by rw [hc, C_0])
    exact (isUnit_C.2 (Ne.isUnit hc)).dvd
  · have hdeg : 0 < q.degree := by
      rw [degree_eq_natDegree hq]; exact_mod_cast Nat.pos_of_ne_zero h0
    obtain ⟨a, ha⟩ := Complex.exists_root hdeg
    have hpa : IsRoot p a := by
      have h1 := h a
      rw [ha.eq_zero, norm_zero, mul_zero] at h1
      exact norm_le_zero_iff.1 h1
    obtain ⟨q', eq⟩ : ∃ q', (X - C a) * q' = q := ⟨_, mul_divByMonic_eq_iff_isRoot.2 ha⟩
    obtain ⟨p', ep⟩ : ∃ p', (X - C a) * p' = p := ⟨_, mul_divByMonic_eq_iff_isRoot.2 hpa⟩
    have hq'0 : q' ≠ 0 := by
      rintro h'; rw [h', mul_zero] at eq; exact hq eq.symm
    have hdeg' : q'.natDegree < n := by
      rw [← hn, ← eq, natDegree_mul (X_sub_C_ne_zero a) hq'0, natDegree_X_sub_C]; omega
    have hb : ∀ s, s ∉ ({a} : Set ℂ) → ‖p'.eval s‖ ≤ K * (1 + ‖s‖) ^ m * ‖q'.eval s‖ := by
      intro s hs
      have hsa : s - a ≠ 0 := sub_ne_zero.2 hs
      have h1 := h s
      rw [← eq, ← ep, eval_mul, eval_mul, eval_sub, eval_X, eval_C, norm_mul, norm_mul] at h1
      have hpos : 0 < ‖s - a‖ := norm_pos_iff.2 hsa
      have e : K * (1 + ‖s‖) ^ m * (‖s - a‖ * ‖eval s q'‖)
          = ‖s - a‖ * (K * (1 + ‖s‖) ^ m * ‖eval s q'‖) := by ring
      rw [e] at h1
      exact le_of_mul_le_mul_left h1 hpos
    have hall := le_of_cofinite (Polynomial.continuous p').norm (cont_bound K m q')
      (Set.finite_singleton a) hb
    rw [← eq, ← ep]
    exact mul_dvd_mul_left _ (ih _ hdeg' p' q' rfl hq'0 hall)
end Bl.CofiniteContinuousBounds
end

set_option autoImplicit false
open Bl Bl.CofiniteContinuousBounds
namespace Bl.CofiniteContinuousBounds
theorem _root_.solution :
  ∀ {p q : Polynomial.{0} Complex},
  Ne.{1} q 0 →
    ∀ (K : Real) (m : Nat),
      (∀ (s : Complex),
          Ne.{1} (Polynomial.eval.{0} s q) 0 →
            LE.le.{0} (Norm.norm.{0} (Polynomial.eval.{0} s p))
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} K (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (Norm.norm.{0} s)) m))
                (Norm.norm.{0} (Polynomial.eval.{0} s q)))) →
        Dvd.dvd.{0} q p := by
  intro p q hq K m h
  have hall := le_of_cofinite (Polynomial.continuous p).norm (cont_bound K m q)
    (Polynomial.finite_setOfPred_isRoot hq) (fun s hs => h s hs)
  exact key K m q.natDegree p q rfl hq hall
end Bl.CofiniteContinuousBounds
