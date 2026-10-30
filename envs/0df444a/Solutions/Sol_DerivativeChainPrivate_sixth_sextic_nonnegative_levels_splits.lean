-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_sextic_nonnegative_levels_splits
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:53:50.886192+00:00
-- url     : https://prove2.me/submissions/fdd0236f-4858-44b9-87a6-79490bcd3610

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace DerivativeChainPrivate.Hermite















end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite























end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma root_between (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ x ∈ Set.Ioo a b, p.eval x = 0 := by
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc hab.le p.continuous.continuousOn
    (show (0:ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨ha.le,hb.le⟩)
  refine ⟨x,⟨?_,?_⟩,hroot⟩
  · by_contra hn
    have he : x = a := by linarith [hx.1]
    subst x; linarith
  · by_contra hn
    have he : x = b := by linarith [hx.2]
    subst x; linarith









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite













end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite





end DerivativeChainPrivate.Hermite

theorem solution (t : ℝ) (ht : 0 ≤ t) :
    (211302*X^3 + (-417690)*X^2 + C (169065-211302*t)*X + 24565 : Polynomial ℝ).Splits := by
  let p : Polynomial ℝ := 211302*X^3 + (-417690)*X^2 + C (169065-211302*t)*X + 24565
  change p.Splits
  have hneg : p.eval (-t-10) < 0 := by
    norm_num [p]
    nlinarith only [ht,pow_nonneg ht 2,pow_nonneg ht 3]
  have hpos : 0 < p.eval (t+10) := by
    norm_num [p]
    nlinarith only [ht,pow_nonneg ht 2,pow_nonneg ht 3]
  obtain ⟨a,ha,hra⟩ := Hermite.root_between p (show -t-10 < 0 by linarith)
    hneg (by norm_num [p])
  obtain ⟨b,hb,hrb⟩ := Hermite.root_between (-p) (show (0 : ℝ) < 1 by norm_num)
    (by norm_num [p]) (by norm_num [p]; linarith)
  have hrb : p.eval b = 0 := by simpa using hrb
  obtain ⟨c,hc,hrc⟩ := Hermite.root_between p (show 1 < t+10 by linarith)
    (by norm_num [p]; linarith) hpos
  let r : Fin 3 → ℝ := ![a,b,c]
  have hinj : Function.Injective r := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [r] at hij ⊢ <;>
      linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2]
  have hr : ∀ i, p.eval (r i) = 0 := by
    intro i
    fin_cases i
    · exact hra
    · exact hrb
    · exact hrc
  let s := Finset.univ.image r
  have hs : s.card = 3 := by simp [s,Finset.card_image_of_injective _ hinj]
  have hdeg : p.natDegree = 3 := by dsimp [p]; compute_degree!
  have hn : p ≠ 0 := by
    intro he
    have := congrArg (fun q : Polynomial ℝ => q.eval 0) he
    norm_num [p] at this
  have heq : p.roots = s.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact hr i
    · omega
    · exact hn
  apply Polynomial.splits_iff_card_roots.mpr
  simpa [heq,hdeg] using hs
