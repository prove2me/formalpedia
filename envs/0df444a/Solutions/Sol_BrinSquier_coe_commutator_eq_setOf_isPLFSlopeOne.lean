-- Prove2me | solution 1 for BrinSquier.coe_commutator_eq_setOf_isPLFSlopeOne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T20:55:32.44635+00:00
-- url     : https://prove2.me/submissions/b3b5a0ec-663b-45de-ae29-ef01ba483390

import Theorems.Thm_BrinSquier_slope_one_commutator
import Theorems.Thm_BrinSquier_isPLF_mul
import Theorems.Thm_BrinSquier_isPLF_inv
import Theorems.Thm_BrinSquier_isPLFSlopeOne_mul
import Theorems.Thm_BrinSquier_isPLFSlopeOne_inv
import Definitions.Def_BrinSquier
import Mathlib

open scoped commutatorElement
namespace BS_oc

lemma affine_unique {a b a' b' y₁ y₂ : ℝ} (hne : y₁ ≠ y₂)
    (h1 : a * y₁ + b = a' * y₁ + b') (h2 : a * y₂ + b = a' * y₂ + b') :
    a = a' ∧ b = b' := by
  have hsub : (a - a') * (y₁ - y₂) = 0 := by nlinarith [h1, h2]
  have haa : a - a' = 0 := by
    rcases mul_eq_zero.1 hsub with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  have ha : a = a' := by linarith
  refine ⟨ha, ?_⟩
  rw [ha] at h1
  linarith

/-- Local affineness on an open interval makes `f` affine on the whole interval. -/
theorem affine_on_Ioo {f : ℝ → ℝ} {p q : ℝ}
    (H : ∀ x ∈ Set.Ioo p q, ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo p q) :
    ∃ a b : ℝ, ∀ y ∈ Set.Ioo p q, f y = a * y + b := by
  obtain ⟨e₀, he₀, a₀, b₀, h₀⟩ := H x₀ hx₀
  obtain ⟨hpx, hxq⟩ := hx₀
  refine ⟨a₀, b₀, ?_⟩
  -- LEFT: agreement on (p, x₀]
  have left : ∀ y ∈ Set.Ioc p x₀, f y = a₀ * y + b₀ := by
    set S : Set ℝ := {t : ℝ | p < t ∧ t ≤ x₀ ∧ ∀ z ∈ Set.Icc t x₀, f z = a₀ * z + b₀} with hS
    set t₁ := max ((p + x₀)/2) (x₀ - e₀/2) with ht₁
    have ht₁p : p < t₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have ht₁x : t₁ < x₀ := max_lt (by linarith) (by linarith)
    have ht₁e : x₀ - e₀/2 ≤ t₁ := le_max_right _ _
    have hbase : t₁ ∈ S :=
      ⟨ht₁p, le_of_lt ht₁x, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    have hne : S.Nonempty := ⟨_, hbase⟩
    have hbdd : BddBelow S := ⟨p, fun z hz => le_of_lt hz.1⟩
    have hcp : sInf S = p := by
      by_contra hcne
      have hge : p ≤ sInf S := le_csInf hne (fun z hz => le_of_lt hz.1)
      have hgt : p < sInf S := lt_of_le_of_ne hge (Ne.symm hcne)
      set c := sInf S with hc
      have hcx : c ≤ t₁ := csInf_le hbdd hbase
      have hcq : c < q := by linarith
      obtain ⟨e, he, a, b, h⟩ := H c ⟨hgt, hcq⟩
      obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne
        (show c < c + min e (x₀ - c) by
          have : 0 < min e (x₀ - c) := lt_min he (by linarith)
          linarith)
      have hct : c ≤ t := csInf_le hbdd htS
      have htx : t < x₀ := by have := min_le_right e (x₀ - c); linarith
      have hte : t < c + e := by have := min_le_left e (x₀ - c); linarith
      set u := min (c + e) x₀ with hu
      have htu : t < u := lt_min hte htx
      set pp := (t + u)/2 with hpp
      have htp : t < pp := by simp only [hpp]; linarith
      have hpu : pp < u := by simp only [hpp]; linarith
      have hpx2 : pp ≤ x₀ := le_of_lt (lt_of_lt_of_le hpu (min_le_right _ _))
      have hpe : pp < c + e := lt_of_lt_of_le hpu (min_le_left _ _)
      have e1 : f t = a₀ * t + b₀ := htS.2.2 t ⟨le_refl _, le_of_lt htx⟩
      have e2 : f pp = a₀ * pp + b₀ := htS.2.2 pp ⟨le_of_lt htp, hpx2⟩
      have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
      have e4 : f pp = a * pp + b := h pp ⟨by linarith, by linarith⟩
      obtain ⟨haa, hbb⟩ := affine_unique (ne_of_lt htp) (e3.symm.trans e1) (e4.symm.trans e2)
      set c' := max ((p + c)/2) (c - e/2) with hc'
      have hc'p : p < c' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hc'c : c' < c := max_lt (by linarith) (by linarith)
      have hc'e : c - e/2 ≤ c' := le_max_right _ _
      have : c' ∈ S := by
        refine ⟨hc'p, by linarith, fun z hz => ?_⟩
        by_cases hzt : t ≤ z
        · exact htS.2.2 z ⟨hzt, hz.2⟩
        · replace hzt := not_le.mp hzt
          have := h z ⟨by linarith [hz.1], by linarith⟩
          rw [this, haa, hbb]
      have := csInf_le hbdd this
      linarith
    intro y hy
    obtain ⟨t, htS, hty⟩ := exists_lt_of_csInf_lt hne (by rw [hcp]; exact hy.1)
    exact htS.2.2 y ⟨le_of_lt hty, hy.2⟩
  -- RIGHT: agreement on [x₀, q)
  have right : ∀ y ∈ Set.Ico x₀ q, f y = a₀ * y + b₀ := by
    set S : Set ℝ := {t : ℝ | t < q ∧ x₀ ≤ t ∧ ∀ z ∈ Set.Icc x₀ t, f z = a₀ * z + b₀} with hS
    set t₁ := min ((q + x₀)/2) (x₀ + e₀/2) with ht₁
    have ht₁q : t₁ < q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₁x : x₀ < t₁ := lt_min (by linarith) (by linarith)
    have ht₁e : t₁ ≤ x₀ + e₀/2 := min_le_right _ _
    have hbase : t₁ ∈ S :=
      ⟨ht₁q, le_of_lt ht₁x, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    have hne : S.Nonempty := ⟨_, hbase⟩
    have hbdd : BddAbove S := ⟨q, fun z hz => le_of_lt hz.1⟩
    have hcq : sSup S = q := by
      by_contra hcne
      have hle : sSup S ≤ q := csSup_le hne (fun z hz => le_of_lt hz.1)
      have hlt : sSup S < q := lt_of_le_of_ne hle hcne
      set c := sSup S with hc
      have hcx : t₁ ≤ c := le_csSup hbdd hbase
      have hcp2 : p < c := by linarith
      obtain ⟨e, he, a, b, h⟩ := H c ⟨hcp2, hlt⟩
      obtain ⟨t, htS, htlt⟩ := exists_lt_of_lt_csSup hne
        (show c - min e (c - x₀) < c by
          have : 0 < min e (c - x₀) := lt_min he (by linarith)
          linarith)
      have hct : t ≤ c := le_csSup hbdd htS
      have htx : x₀ < t := by have := min_le_right e (c - x₀); linarith
      have hte : c - e < t := by have := min_le_left e (c - x₀); linarith
      set u := max (c - e) x₀ with hu
      have hut : u < t := max_lt hte htx
      set pp := (u + t)/2 with hpp
      have hpt : pp < t := by simp only [hpp]; linarith
      have hup : u < pp := by simp only [hpp]; linarith
      have hpx2 : x₀ ≤ pp := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hup)
      have hpe : c - e < pp := lt_of_le_of_lt (le_max_left _ _) hup
      have e1 : f t = a₀ * t + b₀ := htS.2.2 t ⟨le_of_lt htx, le_refl _⟩
      have e2 : f pp = a₀ * pp + b₀ := htS.2.2 pp ⟨hpx2, le_of_lt hpt⟩
      have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
      have e4 : f pp = a * pp + b := h pp ⟨by linarith, by linarith⟩
      obtain ⟨haa, hbb⟩ := affine_unique (ne_of_gt hpt) (e3.symm.trans e1) (e4.symm.trans e2)
      set c' := min ((q + c)/2) (c + e/2) with hc'
      have hc'q : c' < q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hc'c : c < c' := lt_min (by linarith) (by linarith)
      have hc'e : c' ≤ c + e/2 := min_le_right _ _
      have : c' ∈ S := by
        refine ⟨hc'q, by linarith, fun z hz => ?_⟩
        by_cases hzt : z ≤ t
        · exact htS.2.2 z ⟨hz.1, hzt⟩
        · replace hzt := not_le.mp hzt
          have := h z ⟨by linarith, by linarith [hz.2]⟩
          rw [this, haa, hbb]
      have := le_csSup hbdd this
      linarith
    intro y hy
    obtain ⟨t, htS, hty⟩ := exists_lt_of_lt_csSup hne (by rw [hcq]; exact hy.2)
    exact htS.2.2 y ⟨hy.1, le_of_lt hty⟩
  intro y hy
  by_cases hle : y ≤ x₀
  · exact left y ⟨hy.1, hle⟩
  · exact right y ⟨le_of_lt (not_le.mp hle), hy.2⟩

/-- Local affineness on an order-connected set makes `f` affine on all of it.
Reduces to the interval case by widening slightly past the endpoints, where the
endpoints' own affine neighbourhoods still apply. -/
theorem affine_on_ordConnected {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (H : ∀ x ∈ S, ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ∃ a b : ℝ, ∀ y ∈ S, f y = a * y + b := by
  obtain ⟨e₀, he₀, a₀, b₀, h₀⟩ := H x₀ hx₀
  refine ⟨a₀, b₀, ?_⟩
  intro y hyS
  obtain ⟨ey, hey, ay, cy, hy⟩ := H y hyS
  set d := min ey e₀ with hd
  have hdpos : 0 < d := lt_min hey he₀
  have hdy : d ≤ ey := min_le_left _ _
  have hd0 : d ≤ e₀ := min_le_right _ _
  -- a widened open interval on which `f` is still locally affine everywhere
  have key : ∀ lo hi : ℝ, lo < hi → x₀ ∈ Set.Ioo lo hi → y ∈ Set.Ioo lo hi →
      (∀ x ∈ Set.Ioo lo hi, ∃ ε > 0, ∃ a b : ℝ,
        ∀ z ∈ Set.Ioo (x - ε) (x + ε), f z = a * z + b) → f y = a₀ * y + b₀ := by
    intro lo hi _ hx₀J hyJ hJ
    obtain ⟨a, b, hab⟩ := affine_on_Ioo hJ hx₀J
    -- pin `(a,b)` to `(a₀,b₀)` using two points near `x₀`
    set r := min (min e₀ (x₀ - lo)) (hi - x₀) with hr
    have hrpos : 0 < r := lt_min (lt_min he₀ (by linarith [hx₀J.1])) (by linarith [hx₀J.2])
    have hp1 : x₀ + r/3 ∈ Set.Ioo lo hi :=
      ⟨by linarith [hx₀J.1], by
        have := min_le_right (min e₀ (x₀ - lo)) (hi - x₀); linarith⟩
    have hp2 : x₀ + r/2 ∈ Set.Ioo lo hi :=
      ⟨by linarith [hx₀J.1], by
        have := min_le_right (min e₀ (x₀ - lo)) (hi - x₀); linarith⟩
    have hq1 : x₀ + r/3 ∈ Set.Ioo (x₀ - e₀) (x₀ + e₀) := by
      have := (min_le_left (min e₀ (x₀ - lo)) (hi - x₀)).trans (min_le_left e₀ (x₀ - lo))
      exact ⟨by linarith, by linarith⟩
    have hq2 : x₀ + r/2 ∈ Set.Ioo (x₀ - e₀) (x₀ + e₀) := by
      have := (min_le_left (min e₀ (x₀ - lo)) (hi - x₀)).trans (min_le_left e₀ (x₀ - lo))
      exact ⟨by linarith, by linarith⟩
    obtain ⟨haa, hbb⟩ := affine_unique (by intro h; simp only [add_right_inj] at h; linarith)
      ((hab _ hp1).symm.trans (h₀ _ hq1)) ((hab _ hp2).symm.trans (h₀ _ hq2))
    rw [hab y hyJ, haa, hbb]
  rcases le_total y x₀ with hle | hle
  · refine key (y - d) (x₀ + d) (by linarith) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (fun x hx => ?_)
    rcases lt_or_ge x y with h1 | h1
    · refine ⟨min (x - (y - ey)) (y - x), lt_min (by linarith [hx.1]) (by linarith), ay, cy,
        fun z hz => hy z ⟨?_, ?_⟩⟩
      · have := min_le_left (x - (y - ey)) (y - x); linarith [hz.1]
      · have := min_le_right (x - (y - ey)) (y - x); linarith [hz.2]
    rcases le_or_gt x x₀ with h2 | h2
    · exact H x (hS.out hyS hx₀ ⟨h1, h2⟩)
    · refine ⟨min ((x₀ + e₀) - x) (x - x₀), lt_min (by linarith [hx.2]) (by linarith), a₀, b₀,
        fun z hz => h₀ z ⟨?_, ?_⟩⟩
      · have := min_le_right ((x₀ + e₀) - x) (x - x₀); linarith [hz.1]
      · have := min_le_left ((x₀ + e₀) - x) (x - x₀); linarith [hz.2]
  · refine key (x₀ - d) (y + d) (by linarith) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (fun x hx => ?_)
    rcases lt_or_ge x x₀ with h1 | h1
    · refine ⟨min (x - (x₀ - e₀)) (x₀ - x), lt_min (by linarith [hx.1]) (by linarith), a₀, b₀,
        fun z hz => h₀ z ⟨?_, ?_⟩⟩
      · have := min_le_left (x - (x₀ - e₀)) (x₀ - x); linarith [hz.1]
      · have := min_le_right (x - (x₀ - e₀)) (x₀ - x); linarith [hz.2]
    rcases le_or_gt x y with h2 | h2
    · exact H x (hS.out hx₀ hyS ⟨h1, h2⟩)
    · refine ⟨min ((y + ey) - x) (x - y), lt_min (by linarith [hx.2]) (by linarith), ay, cy,
        fun z hz => hy z ⟨?_, ?_⟩⟩
      · have := min_le_right ((y + ey) - x) (x - y); linarith [hz.1]
      · have := min_le_left ((y + ey) - x) (x - y); linarith [hz.2]

end BS_oc
namespace BSGen
open BrinSquier

/-- `T a : t ↦ t + a`, Brin–Squier's generator (2.1b). -/
def T (a : ℝ) : ℝ ≃o ℝ := OrderIso.addRight a

/-- `M p : t ↦ p * t` for `p > 0`, Brin–Squier's generator (2.1a). -/
noncomputable def M (p : ℝ) (hp : 0 < p) : ℝ ≃o ℝ := OrderIso.mulLeft₀ p hp

@[simp] lemma T_apply (a t : ℝ) : T a t = t + a := rfl
@[simp] lemma M_apply (p : ℝ) (hp : 0 < p) (t : ℝ) : M p hp t = p * t := rfl

/-- Both are piecewise linear with finitely many breaks: no breaks at all. -/
lemma isPLF_T (a : ℝ) : IsPLF (T a) :=
  ⟨∅, fun x _ => ⟨1, one_pos, 1, a, fun y _ => by simp⟩⟩

lemma isPLF_M (p : ℝ) (hp : 0 < p) : IsPLF (M p hp) :=
  ⟨∅, fun x _ => ⟨1, one_pos, p, 0, fun y _ => by simp⟩⟩

/-- `T` is a homomorphism from `(ℝ, +)`. -/
lemma T_mul (a b : ℝ) : T a * T b = T (a + b) := by
  refine RelIso.ext fun t => ?_; show t + b + a = t + (a + b); ring

@[simp] lemma T_zero : T 0 = 1 := by refine RelIso.ext fun t => ?_; show t + 0 = t; ring

lemma T_inv (a : ℝ) : (T a)⁻¹ = T (-a) := by
  rw [inv_eq_iff_mul_eq_one, T_mul]; simp

/-- Relation (2.2b): scaling conjugates a translation to a rescaled one. Stated
without inverses, which is how it is proved. -/
lemma M_mul_T (p : ℝ) (hp : 0 < p) (b : ℝ) :
    M p hp * T b = T (p * b) * M p hp := by
  refine RelIso.ext fun t => ?_; show p * (t + b) = p * t + p * b; ring

lemma conj_T (p : ℝ) (hp : 0 < p) (b : ℝ) :
    M p hp * T b * (M p hp)⁻¹ = T (p * b) := by
  rw [M_mul_T, mul_inv_cancel_right]

/-- **Every translation is a commutator**, so translations lie in the derived
subgroup of any subgroup containing the scalings and the translations. Taking
`p = 2`, `⁅M 2, T a⁆ = T (2a) * T (-a) = T a`. -/
lemma T_eq_commutator (a : ℝ) :
    M 2 two_pos * T a * (M 2 two_pos)⁻¹ * (T a)⁻¹ = T a := by
  rw [conj_T, T_inv, T_mul]; ring_nf

end BSGen

namespace BSGen
open BrinSquier

/-- The underlying function of Brin–Squier's generator (2.1c): the identity to the
left of `b`, and slope `q` to the right of it. -/
noncomputable def xf (b q : ℝ) : ℝ → ℝ := fun t => if t ≤ b then t else b + q * (t - b)

lemma xf_of_le {b q t : ℝ} (h : t ≤ b) : xf b q t = t := by simp [xf, h]
lemma xf_of_lt {b q t : ℝ} (h : b < t) : xf b q t = b + q * (t - b) := by
  simp [xf, not_le.mpr h]

lemma xf_strictMono {b q : ℝ} (hq : 0 < q) : StrictMono (xf b q) := by
  intro s t hst
  rcases le_or_gt s b with hs | hs
  · rcases le_or_gt t b with ht | ht
    · rw [xf_of_le hs, xf_of_le ht]; exact hst
    · rw [xf_of_le hs, xf_of_lt ht]
      have : 0 < q * (t - b) := mul_pos hq (by linarith)
      linarith
  · have ht : b < t := lt_trans hs hst
    rw [xf_of_lt hs, xf_of_lt ht]
    have : q * (s - b) < q * (t - b) := by
      apply mul_lt_mul_of_pos_left _ hq; linarith
    linarith

lemma xf_surjective {b q : ℝ} (hq : 0 < q) : Function.Surjective (xf b q) := by
  intro y
  rcases le_or_gt y b with hy | hy
  · exact ⟨y, xf_of_le hy⟩
  · refine ⟨b + (y - b) / q, ?_⟩
    have hlt : b < b + (y - b) / q := by
      have : 0 < (y - b) / q := div_pos (by linarith) hq
      linarith
    rw [xf_of_lt hlt]; field_simp; ring

/-- Brin–Squier's generator (2.1c) as an order isomorphism of the line. -/
noncomputable def X (b q : ℝ) (hq : 0 < q) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (xf b q) (xf_strictMono hq) (xf_surjective hq)

@[simp] lemma X_apply (b q : ℝ) (hq : 0 < q) (t : ℝ) : X b q hq t = xf b q t := by
  rw [X, StrictMono.coe_orderIsoOfSurjective]

/-- `X b q` is piecewise linear with the single breakpoint `b`. -/
lemma isPLF_X (b q : ℝ) (hq : 0 < q) : IsPLF (X b q hq) := by
  refine ⟨{b}, fun x hx => ?_⟩
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
  rcases lt_or_gt_of_ne hx with h | h
  · refine ⟨b - x, by linarith, 1, 0, fun y hy => ?_⟩
    have : y ≤ b := by have := hy.2; linarith
    rw [X_apply, xf_of_le this]; ring
  · refine ⟨x - b, by linarith, q, b - q * b, fun y hy => ?_⟩
    have : b < y := by have := hy.1; linarith
    rw [X_apply, xf_of_lt this]; ring

/-- Relation (2.2f): at a common breakpoint, the slopes multiply. -/
lemma X_mul_X (b p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    X b q hq * X b p hp = X b (q * p) (mul_pos hq hp) := by
  refine RelIso.ext fun t => ?_
  show (X b q hq) ((X b p hp) t) = _
  rw [X_apply, X_apply, X_apply]
  rcases le_or_gt t b with ht | ht
  · rw [xf_of_le ht, xf_of_le ht, xf_of_le ht]
  · have h1 : b < xf b p t := by rw [xf_of_lt ht]; nlinarith [mul_pos hp (sub_pos.mpr ht)]
    rw [xf_of_lt h1]; simp only [xf_of_lt ht]; ring

/-- Relation (2.2e): a translation moves the breakpoint. -/
lemma T_mul_X (a b q : ℝ) (hq : 0 < q) :
    T a * X b q hq = X (b + a) q hq * T a := by
  refine RelIso.ext fun t => ?_
  show (T a) ((X b q hq) t) = (X (b + a) q hq) ((T a) t)
  rw [X_apply, X_apply, T_apply, T_apply]
  rcases le_or_gt t b with ht | ht
  · rw [xf_of_le ht, xf_of_le (by linarith : t + a ≤ b + a)]
  · rw [xf_of_lt ht, xf_of_lt (by linarith : b + a < t + a)]; ring

/-- **`X b q` and `X c q` are conjugate by a translation, so their quotient is a
commutator.** This is what makes the breakpoint invisible in the abelianization. -/
lemma X_div_X_eq_commutator (b c q : ℝ) (hq : 0 < q) :
    X b q hq * (X c q hq)⁻¹
      = X b q hq * T (c - b) * (X b q hq)⁻¹ * (T (c - b))⁻¹ := by
  have h : T (c - b) * X b q hq * (T (c - b))⁻¹ = X c q hq := by
    rw [T_mul_X, mul_inv_cancel_right]
    congr 1; ring
  rw [← h]
  group
end BSGen

namespace P493
open BrinSquier BSGen BS_oc

/-- Affine on a neighbourhood of a point. -/
def AffAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b

/-- **Local affineness composes.** If `f` is affine near `x` and `g` is affine near `f x`,
then `g ∘ f` is affine near `x`. No continuity hypothesis is needed: the affine form of `f`
supplies its own modulus. -/
lemma affAt_comp {f g : ℝ → ℝ} {x : ℝ} (hf : AffAt f x) (hg : AffAt g (f x)) :
    AffAt (g ∘ f) x := by
  obtain ⟨ε, hε, a, b, hab⟩ := hf
  obtain ⟨δ, hδ, c, d, hcd⟩ := hg
  have hx : f x = a * x + b := hab x (by constructor <;> linarith)
  refine ⟨min ε (δ / (|a| + 1)), lt_min hε (div_pos hδ (by positivity)), c * a, c * b + d, ?_⟩
  intro y hy
  have hyε : y ∈ Set.Ioo (x - ε) (x + ε) := by
    constructor
    · have := hy.1; have := min_le_left ε (δ / (|a| + 1)); linarith
    · have := hy.2; have := min_le_left ε (δ / (|a| + 1)); linarith
  have hfy : f y = a * y + b := hab y hyε
  -- `f y` stays within `δ` of `f x`
  have hdist : |f y - f x| < δ := by
    rw [hfy, hx]
    have e : a * y + b - (a * x + b) = a * (y - x) := by ring
    rw [e, abs_mul]
    have h1 : |y - x| < δ / (|a| + 1) := by
      rw [abs_lt]
      have := hy.1; have := hy.2
      have hm := min_le_right ε (δ / (|a| + 1))
      constructor <;> linarith
    have h2 : |a| * |y - x| ≤ (|a| + 1) * |y - x| := by
      apply mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h3 : (|a| + 1) * |y - x| < (|a| + 1) * (δ / (|a| + 1)) := by
      apply mul_lt_mul_of_pos_left h1 (by positivity)
    have h4 : (|a| + 1) * (δ / (|a| + 1)) = δ := by field_simp
    linarith
  have hmem : f y ∈ Set.Ioo (f x - δ) (f x + δ) := by
    rw [abs_lt] at hdist; constructor <;> linarith [hdist.1, hdist.2]
  show g (f y) = c * a * y + (c * b + d)
  rw [hcd _ hmem, hfy]; ring

/-- Pointwise form of `affAt_comp`, so the caller never has to match `∘`. -/
lemma affAt_comp' {F f g : ℝ → ℝ} {x : ℝ} (hF : ∀ y, F y = g (f y))
    (hf : AffAt f x) (hg : AffAt g (f x)) : AffAt F x := by
  obtain ⟨η, hη, e, k, hek⟩ := affAt_comp hf hg
  exact ⟨η, hη, e, k, fun y hy => by rw [hF y]; exact hek y hy⟩

/-- Off its breakpoint, `(X b q)⁻¹` is affine near any point. -/
lemma affAt_X_inv {b q : ℝ} (hq : 0 < q) {y : ℝ} (hy : b < y) :
    AffAt ((X b q hq)⁻¹ : ℝ ≃o ℝ) y := by
  refine ⟨y - b, by linarith, 1 / q, b - b / q, ?_⟩
  intro z hz
  have hzb : b < z := by have := hz.1; linarith
  have hxz : ((X b q hq)⁻¹ : ℝ ≃o ℝ) z = b + (z - b) / q := by
    have hlt : b < b + (z - b) / q := by
      have : 0 < (z - b) / q := div_pos (by linarith) hq
      linarith
    have hfwd : X b q hq (b + (z - b) / q) = z := by
      rw [X_apply, xf_of_lt hlt]
      have hq0 : q ≠ 0 := ne_of_gt hq
      have e1 : b + (z - b) / q - b = (z - b) / q := by ring
      have e : q * (b + (z - b) / q - b) = z - b := by
        rw [e1, mul_comm, div_mul_cancel₀ _ hq0]
      linarith
    calc ((X b q hq)⁻¹ : ℝ ≃o ℝ) z
        = ((X b q hq)⁻¹ : ℝ ≃o ℝ) (X b q hq (b + (z - b) / q)) := by rw [hfwd]
      _ = b + (z - b) / q := RelIso.inv_apply_self _ _
  rw [hxz]; field_simp; ring

end P493

namespace P493
open BrinSquier BSGen BS_oc

/-- Locally affine off a finite set — this is the body of `IsPLF`. -/
def LocAffOff (f : ℝ → ℝ) (B : Finset ℝ) : Prop :=
  ∀ x ∉ (B : Set ℝ), ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b

/-- **Below its least breakpoint, a map that is the identity near `-∞` is the identity.**
The bridge lemma upgrades local affineness on `Iio b` to one affine map there, and two
points where the map is already the identity pin that affine map down; continuity carries
the conclusion to `b` itself. -/
lemma id_below_min {f : ℝ ≃o ℝ} {B : Finset ℝ} (hB : LocAffOff f B)
    {M : ℝ} (hid : ∀ y < M, f y = y) {b : ℝ} (hmin : ∀ x ∈ B, b ≤ x) :
    ∀ y ≤ b, f y = y := by
  -- every point below `b` is off `B`
  have hoff : ∀ x ∈ Set.Iio b, x ∉ (B : Set ℝ) := by
    intro x hx hxB
    exact absurd (hmin x (by simpa using hxB)) (not_le.mpr hx)
  set m : ℝ := min b M with hm
  have hlt1 : m - 1 < b := by have : m ≤ b := min_le_left _ _; linarith
  have hlt2 : m - 2 < b := by have : m ≤ b := min_le_left _ _; linarith
  obtain ⟨a, c, haff⟩ :=
    affine_on_ordConnected (f := (f : ℝ → ℝ)) (S := Set.Iio b) Set.ordConnected_Iio
      (fun x hx => hB x (hoff x hx)) (x₀ := m - 1) hlt1
  -- two points where `f` is already the identity pin the affine map to `id`
  have hM1 : m - 1 < M := by have : m ≤ M := min_le_right _ _; linarith
  have hM2 : m - 2 < M := by have : m ≤ M := min_le_right _ _; linarith
  have e1 : a * (m - 1) + c = 1 * (m - 1) + 0 := by
    rw [← haff _ hlt1, hid _ hM1]; ring
  have e2 : a * (m - 2) + c = 1 * (m - 2) + 0 := by
    rw [← haff _ hlt2, hid _ hM2]; ring
  obtain ⟨ha, hc⟩ := affine_unique (by norm_num : m - 1 ≠ m - 2) e1 e2
  have hIio : Set.EqOn (f : ℝ → ℝ) id (Set.Iio b) := by
    intro y hy; rw [haff y hy, ha, hc]; simp
  -- continuity extends the agreement to the closure `Iic b`
  have hcl : Set.EqOn (f : ℝ → ℝ) id (closure (Set.Iio b)) :=
    hIio.closure (OrderIso.continuous f) continuous_id
  intro y hy
  have hmem : y ∈ closure (Set.Iio b) := by rw [closure_Iio b]; exact hy
  simpa using hcl hmem

end P493

namespace P493
open BrinSquier BSGen BS_oc

/-- `X` extended to all `q` by the identity, so lists of `(b, q)` pairs need no proofs. -/
noncomputable def Xt (b q : ℝ) : ℝ ≃o ℝ := if h : 0 < q then X b q h else 1

lemma Xt_of_pos {b q : ℝ} (hq : 0 < q) : Xt b q = X b q hq := by rw [Xt, dif_pos hq]


/-- Slope at `+∞` is unique: two affine maps agreeing with `f` on rays agree. -/
lemma slopeAtTop_unique {f : ℝ ≃o ℝ} {a a' : ℝ}
    (h : SlopeAtTop f a) (h' : SlopeAtTop f a') : a = a' := by
  obtain ⟨b, M, hM⟩ := h
  obtain ⟨b', M', hM'⟩ := h'
  set y₁ : ℝ := max M M' + 1 with hy1
  set y₂ : ℝ := max M M' + 2 with hy2
  have e1 : a * y₁ + b = a' * y₁ + b' := by
    rw [← hM y₁ (by simp [hy1]; linarith [le_max_left M M']),
        ← hM' y₁ (by simp [hy1]; linarith [le_max_right M M'])]
  have e2 : a * y₂ + b = a' * y₂ + b' := by
    rw [← hM y₂ (by simp [hy2]; linarith [le_max_left M M']),
        ← hM' y₂ (by simp [hy2]; linarith [le_max_right M M'])]
  exact (affine_unique (by simp [hy1, hy2]) e1 e2).1

lemma slopeAtTop_X {b q : ℝ} (hq : 0 < q) : SlopeAtTop (X b q hq) q :=
  ⟨b - q * b, b, fun y hy => by rw [X_apply, xf_of_lt hy]; ring⟩

end P493

namespace P493
open BrinSquier BSGen BS_oc

/-- The induction behind the normal form: strip one generator at a time, cutting the
breakpoint witness down by one each round. -/
lemma exists_list_aux : ∀ (n : ℕ) (f : ℝ ≃o ℝ) (B : Finset ℝ), B.card = n →
    LocAffOff (f : ℝ → ℝ) B → (∃ M, ∀ y < M, f y = y) →
    ∃ l : List (ℝ × ℝ), (∀ p ∈ l, 0 < p.2) ∧ f = (l.map (fun p => Xt p.1 p.2)).prod := by
  intro n
  induction n with
  | zero =>
      intro f B hcard hB hid
      have hBe : B = ∅ := Finset.card_eq_zero.mp hcard
      obtain ⟨M, hM⟩ := hid
      obtain ⟨a, c, haff⟩ := affine_on_ordConnected (f := (f : ℝ → ℝ)) (S := Set.univ)
        Set.ordConnected_univ (fun x _ => hB x (by simp [hBe])) (x₀ := 0) (Set.mem_univ 0)
      have e1 : a * (M - 1) + c = 1 * (M - 1) + 0 := by
        rw [← haff _ (Set.mem_univ _), hM _ (by linarith)]; ring
      have e2 : a * (M - 2) + c = 1 * (M - 2) + 0 := by
        rw [← haff _ (Set.mem_univ _), hM _ (by linarith)]; ring
      obtain ⟨ha, hc⟩ := affine_unique (by norm_num : M - 1 ≠ M - 2) e1 e2
      refine ⟨[], by simp, ?_⟩
      simp only [List.map_nil, List.prod_nil]
      refine RelIso.ext fun t => ?_
      rw [haff t (Set.mem_univ t), ha, hc]; simp
  | succ n ih =>
      intro f B hcard hB hid
      have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨M, hM⟩ := hid
      set b := B.min' hBne with hbdef
      have hbB : b ∈ B := B.min'_mem hBne
      have hmin : ∀ x ∈ B, b ≤ x := fun x hx => B.min'_le x hx
      have hidb : ∀ y ≤ b, f y = y := id_below_min hB hM hmin
      -- a gap to the right of `b` containing no breakpoint
      obtain ⟨b'', hbb'', hnoB⟩ : ∃ b'' : ℝ, b < b'' ∧ ∀ x ∈ B, x ∉ Set.Ioo b b'' := by
        by_cases h : (B.filter (fun x => b < x)).Nonempty
        · refine ⟨(B.filter (fun x => b < x)).min' h, ?_, ?_⟩
          · exact (Finset.mem_filter.mp ((B.filter (fun x => b < x)).min'_mem h)).2
          · intro x hx hmem
            have hx' : x ∈ B.filter (fun x => b < x) := Finset.mem_filter.mpr ⟨hx, hmem.1⟩
            exact absurd hmem.2
              (not_lt.mpr ((B.filter (fun x => b < x)).min'_le x hx'))
        · exact ⟨b + 1, by linarith, fun x hx hmem =>
            h ⟨x, Finset.mem_filter.mpr ⟨hx, hmem.1⟩⟩⟩
      -- `f` is affine on that gap
      obtain ⟨q, r, hqr⟩ := affine_on_ordConnected (f := (f : ℝ → ℝ)) (S := Set.Ioo b b'')
        Set.ordConnected_Ioo
        (fun x hx => hB x (fun hxB => hnoB x (by simpa using hxB) hx))
        (x₀ := (b + b'') / 2) ⟨by linarith, by linarith⟩
      -- continuity pins the constant: the affine map sends `b` to `b`
      have hEq : Set.EqOn (f : ℝ → ℝ) (fun y => q * y + r) (Set.Ioo b b'') :=
        fun y hy => hqr y hy
      have hcl : Set.EqOn (f : ℝ → ℝ) (fun y => q * y + r) (closure (Set.Ioo b b'')) :=
        hEq.closure (OrderIso.continuous f) (by fun_prop)
      have hr : q * b + r = b := by
        have h1 := hcl (by rw [closure_Ioo (ne_of_lt hbb'')]; exact ⟨le_refl _, le_of_lt hbb''⟩)
        rw [hidb b (le_refl b)] at h1
        exact h1.symm
      have hqpos : 0 < q := by
        have hy1 : b + (b'' - b) / 4 ∈ Set.Ioo b b'' := by
          constructor <;> [linarith; linarith]
        have hy2 : b + (b'' - b) / 2 ∈ Set.Ioo b b'' := by
          constructor <;> [linarith; linarith]
        have hlt : f (b + (b'' - b) / 4) < f (b + (b'' - b) / 2) :=
          (f : ℝ ≃o ℝ).strictMono (by linarith)
        rw [hqr _ hy1, hqr _ hy2] at hlt
        nlinarith
      -- `f` agrees with the generator `X b q` below the gap's right end
      have hfX : ∀ y < b'', f y = X b q hqpos y := by
        intro y hy
        rcases le_or_gt y b with h | h
        · rw [X_apply, xf_of_le h, hidb y h]
        · rw [X_apply, xf_of_lt h, hqr y ⟨h, hy⟩]; linarith
      set g : ℝ ≃o ℝ := (X b q hqpos)⁻¹ * f with hg
      have hgid : ∀ y < b'', g y = y := by
        intro y hy
        show ((X b q hqpos)⁻¹ : ℝ ≃o ℝ) (f y) = y
        rw [hfX y hy]; exact RelIso.inv_apply_self _ _
      -- stripping the generator removes `b` from the witness and adds nothing
      have hgB : LocAffOff (g : ℝ → ℝ) (B.erase b) := by
        intro x hx
        by_cases hxlt : x < b''
        · exact ⟨b'' - x, by linarith, 1, 0, fun y hy => by
            rw [hgid y (by have := hy.2; linarith)]; ring⟩
        · push_neg at hxlt
          have hxB : x ∉ (B : Set ℝ) := by
            intro hxB
            have hxb : x ≠ b := by intro h; rw [h] at hxlt; linarith
            exact hx (Finset.mem_erase.mpr ⟨hxb, by simpa using hxB⟩)
          have hfx : b < f x := by
            have h2 : f b < f x := (f : ℝ ≃o ℝ).strictMono (by linarith)
            rwa [hidb b (le_refl b)] at h2
          exact affAt_comp' (f := (f : ℝ → ℝ))
            (g := (((X b q hqpos)⁻¹ : ℝ ≃o ℝ) : ℝ → ℝ))
            (fun y => rfl) (hB x hxB) (affAt_X_inv hqpos hfx)
      have hcard' : (B.erase b).card = n := by
        rw [Finset.card_erase_of_mem hbB, hcard]; omega
      obtain ⟨l', hpos', hprod'⟩ := ih g (B.erase b) hcard' hgB ⟨b'', hgid⟩
      refine ⟨(b, q) :: l', ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with h | h
        · rw [h]; exact hqpos
        · exact hpos' p h
      · simp only [List.map_cons, List.prod_cons]
        rw [Xt_of_pos hqpos, ← hprod', hg]
        group

/-- **(A)** A piecewise-linear map that is the identity near `-∞` is a finite product of
generators `X`. This is the existence half of Brin–Squier's normal form (2.3), and the step
their p. 493 remark delegates to. -/
theorem exists_list_of_id_atBot {f : ℝ ≃o ℝ} (hf : IsPLF f) (hid : ∃ M, ∀ y < M, f y = y) :
    ∃ l : List (ℝ × ℝ), (∀ p ∈ l, 0 < p.2) ∧ f = (l.map (fun p => Xt p.1 p.2)).prod := by
  obtain ⟨B, hB⟩ := hf
  exact exists_list_aux B.card f B rfl hB hid

end P493

namespace P493
open BrinSquier BSGen BS_oc

lemma X_one (b : ℝ) : X b 1 one_pos = 1 := by
  refine RelIso.ext fun t => ?_
  rw [X_apply]
  rcases le_or_gt t b with h | h
  · rw [xf_of_le h]; rfl
  · rw [xf_of_lt h]; show b + 1 * (t - b) = t; ring

@[simp] lemma Xt_one (b : ℝ) : Xt b 1 = 1 := by rw [Xt_of_pos one_pos, X_one]

/-- `⁅G, G⁆` is closed under conjugation by elements of `G`: the generating commutators are,
because `G` is a subgroup, and closure inherits it. -/
lemma conj_mem_commutator {G : Subgroup (ℝ ≃o ℝ)} {a : ℝ ≃o ℝ} (ha : a ∈ G) :
    ∀ x ∈ ⁅G, G⁆, a * x * a⁻¹ ∈ ⁅G, G⁆ := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy
      have e : a * ⁅g₁, g₂⁆ * a⁻¹ = ⁅a * g₁ * a⁻¹, a * g₂ * a⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        (mul_mem (mul_mem ha hg₁) (inv_mem ha)) (mul_mem (mul_mem ha hg₂) (inv_mem ha))
  | one => simpa using one_mem (⁅G, G⁆)
  | mul p q _ _ hp hq =>
      have e : a * (p * q) * a⁻¹ = (a * p * a⁻¹) * (a * q * a⁻¹) := by group
      rw [e]; exact mul_mem hp hq
  | inv p _ hp =>
      have e : a * p⁻¹ * a⁻¹ = (a * p * a⁻¹)⁻¹ := by group
      rw [e]; exact inv_mem hp

/-- **(B)** Modulo the commutator subgroup, a product of generators `X` collapses to a single
one at breakpoint `0` whose slope is the product of the slopes: the breakpoints are invisible
(conjugate by a translation) and slopes at a shared breakpoint multiply. -/
lemma prod_Xt_mem (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f, f ∈ G ↔ IsPLF f) :
    ∀ l : List (ℝ × ℝ), (∀ p ∈ l, 0 < p.2) →
      (l.map (fun p => Xt p.1 p.2)).prod * (Xt 0 ((l.map (fun p => p.2)).prod))⁻¹ ∈ ⁅G, G⁆ := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons p t ih =>
      intro hpos
      have hq : 0 < p.2 := hpos p (by simp)
      have htpos : ∀ r ∈ t, 0 < r.2 := fun r hr => hpos r (by simp [hr])
      have hP : 0 < (t.map (fun r => r.2)).prod := by
        clear ih hpos
        induction t with
        | nil => simp
        | cons r s ihs =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_pos (htpos r (by simp)) (ihs (fun z hz => htpos z (by simp [hz])))
      set P : ℝ := (t.map (fun r => r.2)).prod with hPdef
      set R : ℝ ≃o ℝ := (t.map (fun r => Xt r.1 r.2)).prod with hRdef
      -- the head's breakpoint is invisible
      have h1 : Xt p.1 p.2 * (Xt 0 p.2)⁻¹ ∈ ⁅G, G⁆ := by
        rw [Xt_of_pos hq, Xt_of_pos hq, X_div_X_eq_commutator]
        exact Subgroup.commutator_mem_commutator
          ((hG _).2 (isPLF_X _ _ hq)) ((hG _).2 (isPLF_T _))
      -- the tail collapses, then gets conjugated into place
      have h2 : Xt 0 p.2 * (R * (Xt 0 P)⁻¹) * (Xt 0 p.2)⁻¹ ∈ ⁅G, G⁆ :=
        conj_mem_commutator ((hG _).2 (by rw [Xt_of_pos hq]; exact isPLF_X _ _ hq))
          _ (ih htpos)
      have hXmul : Xt 0 p.2 * Xt 0 P = Xt 0 (p.2 * P) := by
        rw [Xt_of_pos hq, Xt_of_pos hP, Xt_of_pos (mul_pos hq hP)]
        exact X_mul_X 0 P p.2 hP hq
      have hsplit : (Xt p.1 p.2 * R) * (Xt 0 (p.2 * P))⁻¹
          = (Xt p.1 p.2 * (Xt 0 p.2)⁻¹) * (Xt 0 p.2 * (R * (Xt 0 P)⁻¹) * (Xt 0 p.2)⁻¹) := by
        rw [← hXmul]; group
      simp only [List.map_cons, List.prod_cons, ← hRdef, ← hPdef, hsplit]
      exact mul_mem h1 h2

end P493

namespace P493
open BrinSquier BSGen BS_oc

/-- The slope-one piecewise-linear maps as a subgroup: what the two closure results buy. -/
def PLFSO : Subgroup (ℝ ≃o ℝ) where
  carrier := {x | IsPLFSlopeOne x}
  one_mem' := ⟨⟨∅, fun x _ => ⟨1, one_pos, 1, 0, fun y _ => by simp⟩⟩,
    ⟨0, 0, fun y _ => by simp⟩, ⟨0, 0, fun y _ => by simp⟩⟩
  mul_mem' := fun ha hb => isPLFSlopeOne_mul ha hb
  inv_mem' := fun ha => isPLFSlopeOne_inv ha

/-- **The easy inclusion**: (2.14a) gives each commutator slope one at both ends, and the
slope-one maps form a subgroup. -/
theorem commutator_le_slopeOne (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f, f ∈ G ↔ IsPLF f) :
    ⁅G, G⁆ ≤ PLFSO := by
  rw [Subgroup.commutator_le]
  intro p hp q hq
  have hp' : IsPLF p := (hG p).1 hp
  have hq' : IsPLF q := (hG q).1 hq
  rw [commutatorElement_def]
  exact ⟨isPLF_mul (isPLF_mul (isPLF_mul hp' hq') (isPLF_inv hp')) (isPLF_inv hq'),
    (slope_one_commutator hp' hq').1, (slope_one_commutator hp' hq').2⟩

lemma prod_pos {l : List (ℝ × ℝ)} (h : ∀ p ∈ l, 0 < p.2) :
    0 < (l.map (fun r => r.2)).prod := by
  induction l with
  | nil => simp
  | cons r s ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_pos (h r (by simp)) (ih fun z hz => h z (by simp [hz]))

lemma isPLFSlopeOne_T (a : ℝ) : IsPLFSlopeOne (T a) :=
  ⟨isPLF_T a, ⟨a, 0, fun y _ => by show y + a = 1 * y + a; ring⟩,
    ⟨a, 0, fun y _ => by show y + a = 1 * y + a; ring⟩⟩

/-- **The hard inclusion**: a piecewise-linear map of slope one at each end lies in the
commutator subgroup. Normalise it to be the identity near `-∞` by a translation, which is
itself a commutator; write it as a product of generators; collapse that product modulo the
commutator subgroup to a single generator at `0`; and observe that the easy inclusion forces
that generator's slope to be `1`, i.e. the identity. -/
theorem slopeOne_le_commutator (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f, f ∈ G ↔ IsPLF f)
    {f : ℝ ≃o ℝ} (hf : IsPLFSlopeOne f) : f ∈ ⁅G, G⁆ := by
  obtain ⟨hfPLF, hbot, htop⟩ := hf
  obtain ⟨c, M₀, hM⟩ := hbot
  -- (D) a translation, itself a commutator, normalises `f` to the identity near `-∞`
  have hTmem : ∀ a : ℝ, T a ∈ ⁅G, G⁆ := by
    intro a
    have : T a = ⁅M 2 two_pos, T a⁆ := by
      rw [commutatorElement_def]; exact (T_eq_commutator a).symm
    rw [this]
    exact Subgroup.commutator_mem_commutator ((hG _).2 (isPLF_M 2 two_pos))
      ((hG _).2 (isPLF_T a))
  set h : ℝ ≃o ℝ := T (-c) * f with hh
  have hhid : ∀ y < M₀, h y = y := by
    intro y hy; show f y + -c = y; rw [hM y hy]; ring
  have hhPLF : IsPLF h := isPLF_mul (isPLF_T _) hfPLF
  have hhSO : IsPLFSlopeOne h := isPLFSlopeOne_mul (isPLFSlopeOne_T _) ⟨hfPLF, ⟨c, M₀, hM⟩, htop⟩
  -- (A) it is a product of generators
  obtain ⟨l, hpos, hprod⟩ := exists_list_of_id_atBot hhPLF ⟨M₀, hhid⟩
  set P : ℝ := (l.map (fun r => r.2)).prod with hPdef
  have hPpos : 0 < P := prod_pos hpos
  -- (B) modulo the commutator subgroup, the product collapses to one generator at `0`
  have hcol : h * (Xt 0 P)⁻¹ ∈ ⁅G, G⁆ := by
    rw [hh, ← hh, hprod]; exact prod_Xt_mem G hG l hpos
  -- (C) the easy inclusion forces that generator to have slope one, hence `P = 1`
  have hXin : Xt 0 P ∈ PLFSO := by
    have e : Xt 0 P = (h * (Xt 0 P)⁻¹)⁻¹ * h := by group
    rw [e]
    exact mul_mem (inv_mem (commutator_le_slopeOne G hG hcol)) hhSO
  have hP1 : P = 1 :=
    slopeAtTop_unique (by rw [Xt_of_pos hPpos]; exact slopeAtTop_X hPpos) hXin.2.2
  -- so `h` itself is in the commutator subgroup, and so is `f`
  have hhmem : h ∈ ⁅G, G⁆ := by
    have := hcol
    rw [hP1, Xt_one] at this
    simpa using this
  have hf' : f = T c * h := by rw [hh, ← mul_assoc, T_mul]; simp
  rw [hf']
  exact mul_mem (hTmem c) hhmem

/-- **p. 493**: the commutator subgroup of `PLF(ℝ)` consists precisely of the elements of
slope one at each end. -/
theorem coe_commutator_eq_setOf_isPLFSlopeOne
    (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f, f ∈ G ↔ IsPLF f) :
    (↑⁅G, G⁆ : Set (ℝ ≃o ℝ)) = {f | IsPLFSlopeOne f} := by
  ext f
  exact ⟨fun hx => commutator_le_slopeOne G hG hx, fun hx => slopeOne_le_commutator G hG hx⟩

end P493

theorem solution (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f, f ∈ G ↔ BrinSquier.IsPLF f) :
    (↑⁅G, G⁆ : Set (ℝ ≃o ℝ)) = {f | BrinSquier.IsPLFSlopeOne f} :=
  P493.coe_commutator_eq_setOf_isPLFSlopeOne G hG
