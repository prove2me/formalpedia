-- Prove2me | solution 1 for FinancialDerivatives.FD01.forward_fair_delivery_price
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:25:09.136107+00:00
-- url     : https://prove2.me/submissions/7aaec597-92ad-4854-8734-acd1e6c5483a

import Mathlib
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_callValue
import Definitions.Def_fd01_putValue
import Definitions.Def_fd01_spotValue
import Definitions.Def_fd01_forwardPayoff
import Definitions.Def_fd01_price
open Finset
namespace FinancialDerivatives.FD01
theorem S189F_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ)
    (h : ∀ ω, f ω ≤ g ω) : m.price f ≤ m.price g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (m.statePrice_nonneg ω)
theorem S189F_sub {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) :
    m.price f - m.price g = m.price (fun ω => f ω - g ω) := by
  unfold FinitePriceSystem.price; rw [← sum_sub_distrib]; exact sum_congr rfl fun ω _ => by ring
theorem S189F_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (a : ℝ) :
    m.price (fun _ => a) = m.discount * a := by
  unfold FinitePriceSystem.price; rw [← sum_mul, m.statePrice_sum]
theorem S189F_spotK {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) :
    m.spotValue s - m.discount * K = m.price (fun ω => s ω - K) := by
  rw [← S189F_const m K, FinitePriceSystem.spotValue, S189F_sub]
theorem S189F_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f : Ω → ℝ)
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ m.price f :=
  sum_nonneg fun ω _ => mul_nonneg (m.statePrice_nonneg ω) (h ω)

theorem S189F_u1 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  m.putValue s K₁ ≤ m.putValue s K₂ := S189F_mono m _ _ fun ω => max_le_max (by linarith) le_rfl
theorem S189F_u2 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  m.callValue s K₂ ≤ m.callValue s K₁ := S189F_mono m _ _ fun ω => max_le_max (by linarith) le_rfl
theorem S189F_u3 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  max (m.discount * K - m.spotValue s) 0 ≤ m.putValue s K := by
  refine max_le ?_ (S189F_nonneg m _ fun ω => le_max_right _ _)
  have : m.discount * K - m.spotValue s = m.price (fun ω => K - s ω) := by
    rw [← S189F_const m K, FinitePriceSystem.spotValue, S189F_sub]
  rw [this]; exact S189F_mono m _ _ fun ω => le_max_left _ _
theorem S189F_u4 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  max (m.spotValue s - m.discount * K) 0 ≤ m.callValue s K := by
  refine max_le ?_ (S189F_nonneg m _ fun ω => le_max_right _ _)
  rw [S189F_spotK]; exact S189F_mono m _ _ fun ω => le_max_left _ _
theorem S189F_u5 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) :
  m.callValue s K - m.putValue s K = m.spotValue s - m.discount * K := by
  rw [S189F_spotK, FinitePriceSystem.callValue, FinitePriceSystem.putValue, S189F_sub]
  congr 1; funext ω
  rcases le_total (s ω) K with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
theorem S189F_u6 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  0 ≤ m.putValue s K ∧ m.putValue s K ≤ m.discount * K := by
  refine ⟨S189F_nonneg m _ fun ω => le_max_right _ _, ?_⟩
  rw [← S189F_const m K]
  exact S189F_mono m _ _ fun ω => max_le (by linarith [hs ω]) hK
theorem S189F_u7 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  0 ≤ m.callValue s K ∧ m.callValue s K ≤ m.spotValue s := by
  refine ⟨S189F_nonneg m _ fun ω => le_max_right _ _, ?_⟩
  exact S189F_mono m _ _ fun ω => max_le (by linarith) (hs ω)
theorem S189F_u8 (s K₁ K₂ K₃ : ℝ) (hK₁ : K₁ ≤ K₂) (hK₂ : K₂ ≤ K₃) (hmid : 2 * K₂ = K₁ + K₃) :
  0 ≤ max (s - K₁) 0 - 2 * max (s - K₂) 0 + max (s - K₃) 0 := by
  rcases le_total s K₁ with h1 | h1 <;> rcases le_total s K₂ with h2 | h2 <;> rcases le_total s K₃ with h3 | h3 <;>
  simp only [max_eq_left, max_eq_right, sub_nonneg, sub_nonpos, *] <;> linarith
theorem S189F_u9 (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ max (K₂ - s) 0 - max (K₁ - s) 0 ∧ max (K₂ - s) 0 - max (K₁ - s) 0 ≤ K₂ - K₁ := by
  have h1 : max (K₁ - s) 0 ≤ max (K₂ - s) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (K₂ - s) 0 ≤ max (K₁ - s) 0 + (K₂ - K₁) :=
    max_le (by linarith [le_max_left (K₁ - s) 0]) (by linarith [le_max_right (K₁ - s) 0])
  constructor <;> linarith
theorem S189F_u10 (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ max (s - K₁) 0 - max (s - K₂) 0 ∧ max (s - K₁) 0 - max (s - K₂) 0 ≤ K₂ - K₁ := by
  have h1 : max (s - K₂) 0 ≤ max (s - K₁) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (s - K₁) 0 ≤ max (s - K₂) 0 + (K₂ - K₁) :=
    max_le (by linarith [le_max_left (s - K₂) 0]) (by linarith [le_max_right (s - K₂) 0])
  constructor <;> linarith
theorem S189F_u11 (s K : ℝ) :
  max (s - K) 0 + max (K - s) 0 = |s - K| := by
  rcases le_total s K with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring
theorem S189F_u12 (s K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  max ((w * K₁ + (1 - w) * K₂) - s) 0 ≤ w * max (K₁ - s) 0 + (1 - w) * max (K₂ - s) 0 := by
  have a := le_max_left (K₁ - s) 0; have b := le_max_left (K₂ - s) 0
  have c := le_max_right (K₁ - s) 0; have d := le_max_right (K₂ - s) 0
  have h1w : 0 ≤ 1 - w := by linarith
  refine max_le ?_ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left a hw₀, mul_le_mul_of_nonneg_left b h1w]
theorem S189F_u13 (s K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  max (s - (w * K₁ + (1 - w) * K₂)) 0 ≤ w * max (s - K₁) 0 + (1 - w) * max (s - K₂) 0 := by
  have a := le_max_left (s - K₁) 0; have b := le_max_left (s - K₂) 0
  have c := le_max_right (s - K₁) 0; have d := le_max_right (s - K₂) 0
  have h1w : 0 ≤ 1 - w := by linarith
  refine max_le ?_ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left a hw₀, mul_le_mul_of_nonneg_left b h1w]

theorem S189F_lin {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (a b : ℝ) :
    m.price (fun ω => a * f ω + b * g ω) = a * m.price f + b * m.price g := by
  unfold FinitePriceSystem.price; rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring
theorem S189F_err {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (B : ℝ)
    (h : ∀ ω, |f ω - g ω| ≤ B) : |m.price f - m.price g| ≤ m.discount * B := by
  unfold FinitePriceSystem.price
  rw [← sum_sub_distrib, ← m.statePrice_sum, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ω _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (m.statePrice_nonneg ω)]
  exact mul_le_mul_of_nonneg_left (h ω) (m.statePrice_nonneg ω)
theorem S189F_cspread {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ m.callValue s K₁ - m.callValue s K₂ ∧ m.callValue s K₁ - m.callValue s K₂ ≤ m.discount * (K₂ - K₁) := by
  unfold FinitePriceSystem.callValue
  rw [S189F_sub, ← S189F_const]
  exact ⟨S189F_nonneg m _ fun ω => (S189F_u10 (s ω) K₁ K₂ hK).1, S189F_mono m _ _ fun ω => (S189F_u10 (s ω) K₁ K₂ hK).2⟩
theorem S189F_pspread {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ m.putValue s K₂ - m.putValue s K₁ ∧ m.putValue s K₂ - m.putValue s K₁ ≤ m.discount * (K₂ - K₁) := by
  unfold FinitePriceSystem.putValue
  rw [S189F_sub, ← S189F_const]
  exact ⟨S189F_nonneg m _ fun ω => (S189F_u9 (s ω) K₁ K₂ hK).1, S189F_mono m _ _ fun ω => (S189F_u9 (s ω) K₁ K₂ hK).2⟩
theorem S189F_bfly {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ K₃ : ℝ) (hK₁ : K₁ ≤ K₂) (hK₂ : K₂ ≤ K₃) (hmid : 2 * K₂ = K₁ + K₃) :
  0 ≤ m.callValue s K₁ - 2 * m.callValue s K₂ + m.callValue s K₃ := by
  have : m.callValue s K₁ - 2 * m.callValue s K₂ + m.callValue s K₃ =
      m.price (fun ω => max (s ω - K₁) 0 - 2 * max (s ω - K₂) 0 + max (s ω - K₃) 0) := by
    unfold FinitePriceSystem.callValue FinitePriceSystem.price
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by ring
  rw [this]; exact S189F_nonneg m _ fun ω => S189F_u8 (s ω) K₁ K₂ K₃ hK₁ hK₂ hmid
theorem S189F_pconv {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  m.putValue s (w * K₁ + (1 - w) * K₂) ≤ w * m.putValue s K₁ + (1 - w) * m.putValue s K₂ := by
  unfold FinitePriceSystem.putValue; rw [← S189F_lin]
  exact S189F_mono m _ _ fun ω => S189F_u12 (s ω) K₁ K₂ w hw₀ hw₁
theorem S189F_cconv {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  m.callValue s (w * K₁ + (1 - w) * K₂) ≤ w * m.callValue s K₁ + (1 - w) * m.callValue s K₂ := by
  unfold FinitePriceSystem.callValue; rw [← S189F_lin]
  exact S189F_mono m _ _ fun ω => S189F_u13 (s ω) K₁ K₂ w hw₀ hw₁
theorem S189F_plip {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) :
  |m.putValue s K₁ - m.putValue s K₂| ≤ m.discount * |K₁ - K₂| := by
  refine S189F_err m _ _ _ fun ω => ?_
  rw [abs_le]; constructor <;> cases' le_total (K₁ - s ω) 0 with h h <;> cases' le_total (K₂ - s ω) 0 with h' h' <;>
    simp_all <;> cases' abs_cases (K₁ - K₂) with a a <;> linarith
theorem S189F_clip {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) :
  |m.callValue s K₁ - m.callValue s K₂| ≤ m.discount * |K₁ - K₂| := by
  refine S189F_err m _ _ _ fun ω => ?_
  rw [abs_le]; constructor <;> cases' le_total (s ω - K₁) 0 with h h <;> cases' le_total (s ω - K₂) 0 with h' h' <;>
    simp_all <;> cases' abs_cases (K₁ - K₂) with a a <;> linarith
end FinancialDerivatives.FD01

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) :
  m.price (fun ω => forwardPayoff (s ω) K) = m.spotValue s - m.discount * K ∧ (m.price (fun ω => forwardPayoff (s ω) K) = 0 ↔ K = m.spotValue s / m.discount) := by
  have h : m.price (fun ω => forwardPayoff (s ω) K) = m.spotValue s - m.discount * K := by
    rw [S189F_spotK]; rfl
  refine ⟨h, ?_⟩
  rw [h]; have := m.discount_pos.ne'
  constructor
  · intro h0; field_simp; linarith
  · intro h0; rw [h0]; field_simp; ring
