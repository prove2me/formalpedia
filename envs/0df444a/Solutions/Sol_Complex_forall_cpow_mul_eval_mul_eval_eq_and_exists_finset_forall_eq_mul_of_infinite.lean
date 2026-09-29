-- Prove2me | solution 1 for Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e9550b9d-e057-50cc-a9df-86643e36bba7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite

set_option autoImplicit false

open Polynomial

namespace LTLaurentCancel

theorem natCast_cpow_intCast_mul (q : ℕ) (n : ℤ) (w : ℂ) :
    (q : ℂ) ^ ((n : ℂ) * w) = ((q : ℂ) ^ (-w)) ^ (-n) := by
  have : ((n : ℂ) * w) = ((-n : ℤ) : ℂ) * (-w) := by push_cast; ring
  rw [this, Complex.cpow_int_mul]

theorem natCast_cpow_ne_zero {q : ℕ} (hq : 1 < q) (w : ℂ) : (q : ℂ) ^ w ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast (show (q : ℕ) ≠ 0 by omega)

theorem infinite_setOf_cpow {q : ℕ} (hq : 1 < q) (S : Set ℂ) (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite) :
    {Y : ℂ | ∃ s ∈ S, Y = (q : ℂ) ^ (-s)}.Infinite := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  set f : ℝ → ℂ := fun t => (((q : ℝ) ^ (-t) : ℝ) : ℂ) with hf
  have hinj : Set.InjOn f {t : ℝ | (t : ℂ) ∈ S} := by
    intro t₁ _ t₂ _ h
    have h' : (q : ℝ) ^ (-t₁) = (q : ℝ) ^ (-t₂) := by
      have := congrArg Complex.re h
      simpa [hf] using this
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (q : ℝ) ^ (-t₂) < (q : ℝ) ^ (-t₁) := (Real.rpow_lt_rpow_left_iff hq1).mpr (by linarith)
      exact this.ne' h'
    · have : (q : ℝ) ^ (-t₁) < (q : ℝ) ^ (-t₂) := (Real.rpow_lt_rpow_left_iff hq1).mpr (by linarith)
      exact this.ne h'
  refine Set.infinite_of_injOn_mapsTo hinj ?_ hS
  intro t ht
  refine ⟨(t : ℂ), ht, ?_⟩
  show (((q : ℝ) ^ (-t) : ℝ) : ℂ) = (q : ℂ) ^ (-(t : ℂ))
  rw [Complex.ofReal_cpow hq0]; push_cast; rfl

theorem laurent_identity_of_infinite {q : ℕ} (hq : 1 < q) (P Q₁ Q₂ : ℂ[X]) (m k : ℤ) (S : Set ℂ)
    (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite)
    (h : ∀ s ∈ S,
      (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) (s : ℂ) :
    (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
      Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) := by

  set M : ℤ := max (max m k) 0 with hM
  have hmM : m ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hkM : k ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  set A : ℂ[X] := X ^ (M - m).toNat * (P * Q₂) with hA
  set B : ℂ[X] := X ^ (M - k).toNat * Q₁ with hB
  have hevalA : ∀ Y : ℂ, Y ≠ 0 → A.eval Y = Y ^ M * (Y ^ (-m) * P.eval Y * Q₂.eval Y) := by
    intro Y hY
    rw [hA, eval_mul, eval_pow, eval_X, eval_mul]
    have : (Y ^ (M - m).toNat : ℂ) = Y ^ M * Y ^ (-m) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hmM), ← zpow_add₀ hY]; ring_nf
    rw [this]; ring
  have hevalB : ∀ Y : ℂ, Y ≠ 0 → B.eval Y = Y ^ M * (Q₁.eval Y * Y ^ (-k)) := by
    intro Y hY
    rw [hB, eval_mul, eval_pow, eval_X]
    have : (Y ^ (M - k).toNat : ℂ) = Y ^ M * Y ^ (-k) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hkM), ← zpow_add₀ hY]; ring_nf
    rw [this]; ring
  have hlaur : ∀ s : ℂ,
      ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
          Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) ↔
        A.eval ((q : ℂ) ^ (-s)) = B.eval ((q : ℂ) ^ (-s)) := by
    intro s
    have hY : (q : ℂ) ^ (-s) ≠ 0 := natCast_cpow_ne_zero hq _
    rw [hevalA _ hY, hevalB _ hY, natCast_cpow_intCast_mul q m s, natCast_cpow_intCast_mul q k s,
      mul_right_inj' (zpow_ne_zero M hY)]
  have hAB : A = B := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (infinite_setOf_cpow hq S hS)
    rintro Y ⟨s', hs', rfl⟩
    exact (hlaur s').mp (h s' hs')
  exact (hlaur s).mpr (by rw [hAB])

theorem exists_finset_dual_eq {q : ℕ} (hq : 1 < q) (Zd γ : ℂ → ℂ) (P Q₁ Q₂ : ℂ[X]) (hQ₂ : Q₂ ≠ 0)
    (m k : ℤ) (S S₁ : Set ℂ) (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite)
    (h : ∀ s ∈ S,
      (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s))
    (h₁ : ∀ s ∈ S₁,
      Zd s * Q₂.eval ((q : ℂ) ^ (-s)) = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) * γ s) :
    ∃ R : Finset ℝ, ∀ s ∈ S₁, (q : ℝ) ^ (-s.re) ∉ R →
      Zd s = γ s * ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s))) := by
  classical
  refine ⟨Q₂.roots.toFinset.image (fun z => ‖z‖), fun s hs hR => ?_⟩
  have hq0 : 0 < q := by omega
  have hY : Q₂.eval ((q : ℂ) ^ (-s)) ≠ 0 := by
    intro h0
    apply hR
    refine Finset.mem_image.mpr ⟨(q : ℂ) ^ (-s), ?_, ?_⟩
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ₂).mpr h0)
    · rw [Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re]
  have h2 := h₁ s hs
  rw [← laurent_identity_of_infinite hq P Q₁ Q₂ m k S hS h s] at h2
  have h3 : Zd s * Q₂.eval ((q : ℂ) ^ (-s)) =
      (γ s * ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)))) * Q₂.eval ((q : ℂ) ^ (-s)) := by
    rw [h2]; ring
  exact mul_right_cancel₀ hY h3

theorem infinite_real_of_lt_re (σ : ℝ) : {t : ℝ | ((t : ℂ)) ∈ {s : ℂ | σ < s.re}}.Infinite := by
  have : {t : ℝ | ((t : ℂ)) ∈ {s : ℂ | σ < s.re}} = Set.Ioi σ := by
    ext t; simp
  rw [this]; exact Set.Ioi_infinite σ

theorem infinite_real_of_re_lt (σ : ℝ) : {t : ℝ | ((t : ℂ)) ∈ {s : ℂ | s.re < σ}}.Infinite := by
  have : {t : ℝ | ((t : ℂ)) ∈ {s : ℂ | s.re < σ}} = Set.Iio σ := by
    ext t; simp
  rw [this]; exact Set.Iio_infinite σ

end LTLaurentCancel

open LTLaurentCancel

theorem solution
    (q : ℕ) (hq : 1 < q) (P Q₁ Q₂ : Polynomial ℂ) (hQ₂ : Q₂ ≠ 0) (m k : ℤ) (γ Zd : ℂ → ℂ) (S S₁ : Set ℂ)
    (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite)
    (h : ∀ s ∈ S,
      (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s))
    (h₁ : ∀ s ∈ S₁,
      Zd s * Q₂.eval ((q : ℂ) ^ (-s)) = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) * γ s) :
    (∀ s : ℂ, (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) ∧
    ∃ R : Finset ℝ, ∀ s ∈ S₁, (q : ℝ) ^ (-s.re) ∉ R →
      Zd s = γ s * ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s))) :=
  ⟨laurent_identity_of_infinite hq P Q₁ Q₂ m k S hS h,
    exists_finset_dual_eq hq Zd γ P Q₁ Q₂ hQ₂ m k S S₁ hS h h₁⟩

end S_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
end P2MW
export P2MW.S_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite (solution)
