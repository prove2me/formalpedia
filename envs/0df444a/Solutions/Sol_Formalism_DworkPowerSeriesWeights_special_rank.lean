-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.special_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:13.006186+00:00
-- url     : https://prove2.me/submissions/e4b14552-948c-4587-8407-42e590628a0a

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_special_det_monomial_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : SpecialRank := by
  intro l hl T _ _ J j hj N0 hN
  have hcard : Fintype.card (Σ t, Fin (J t)) ≤ Fintype.card (Fin N0) := by
    simpa [Fintype.card_sigma] using hN
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨f, f.injective, ?_⟩
  set g : (Σ t, Fin (J t)) → ℕ := fun r => l ^ j r.1 r.2 with hg
  have hM : (Matrix.of fun (r c : Σ t, Fin (J t)) =>
      (MvPolynomial.X (r.1, f c) : MvPolynomial (T × Fin N0) (ZMod l)) ^ (l ^ j r.1 r.2)) =
      Matrix.of fun r c => MvPolynomial.monomial (Finsupp.single (r.1, f c) (g r)) (1 : ZMod l) := by
    ext r c; simp [MvPolynomial.X_pow_eq_monomial, hg]
  rw [hM]
  refine special_det_monomial_ne_zero _ ?_
  have hS : ∀ (p : Equiv.Perm (Σ t, Fin (J t))) (t : T) (c : Σ t, Fin (J t)),
      (∑ c', Finsupp.single ((p c').1, f c') (g (p c'))) (t, f c) =
        if (p c).1 = t then g (p c) else 0 := by
    intro p t c
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
    · simp only [Finsupp.single_apply, Prod.mk.injEq, and_true]
    · intro c' _ hc'
      rw [Finsupp.single_apply, if_neg]
      intro he
      exact hc' (f.injective (Prod.mk.inj he).2)
    · simp
  have hgpos : ∀ r, g r ≠ 0 := fun r => pow_ne_zero _ hl.out.ne_zero
  have hginj : ∀ a b : (Σ t, Fin (J t)), a.1 = b.1 → g a = g b → a = b := by
    rintro ⟨t, x⟩ ⟨t', y⟩ h1 h2
    simp only at h1
    subst h1
    have h3 : j t x = j t y := Nat.pow_right_injective hl.out.two_le h2
    rw [hj t h3]
  intro p q h
  simp only at h
  ext1 c
  have hc := DFunLike.congr_fun h ((p c).1, f c)
  rw [hS p, hS q, if_pos rfl] at hc
  by_cases ht : (q c).1 = (p c).1
  · rw [if_pos ht] at hc
    exact hginj _ _ ht.symm hc
  · rw [if_neg ht] at hc
    exact absurd hc (hgpos _)
end Formalism.DworkPowerSeriesWeights
