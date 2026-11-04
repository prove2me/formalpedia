-- Prove2me | solution 1 for ContextFooling.FoolingEq.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:42:45.87337+00:00
-- url     : https://prove2.me/submissions/1a9d94ee-355f-4214-a946-b3a38613bfde

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

namespace Prop2Aux

variable {P : Params}

lemma derivc_strictMono (hP : P.Standing) : StrictMonoOn (deriv P.c) (Set.Ici 0) := by
  obtain ⟨_, _, _, _, hc, _, _, _, hc2, _⟩ := hP
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact (hc.continuous_deriv (by norm_num)).continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    exact hc2 x (le_of_lt hx)

lemma c_diff (hP : P.Standing) : Differentiable ℝ P.c := by
  obtain ⟨_, _, _, _, hc, _⟩ := hP
  exact hc.differentiable (by norm_num)

/-- Strict tangent-line inequality for `c` on `[0, ∞)`. -/
lemma tangent (hP : P.Standing) {q0 q : ℝ} (hq0 : 0 ≤ q0) (hq : 0 ≤ q) (hne : q ≠ q0) :
    P.c q0 + deriv P.c q0 * (q - q0) < P.c q := by
  have hmono := derivc_strictMono hP
  have hd := c_diff hP
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope P.c h hd.continuous.continuousOn
      (hd.differentiableOn)
    have hξ0 : 0 ≤ ξ := le_trans hq (le_of_lt hξ.1)
    have : deriv P.c ξ < deriv P.c q0 := hmono hξ0 hq0 hξ.2
    rw [hξd] at this
    have hpos : 0 < q0 - q := by linarith
    rw [div_lt_iff₀ hpos] at this
    nlinarith
  · obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope P.c h hd.continuous.continuousOn
      (hd.differentiableOn)
    have hξ0 : 0 ≤ ξ := le_trans hq0 (le_of_lt hξ.1)
    have : deriv P.c q0 < deriv P.c ξ := hmono hq0 hξ0 hξ.1
    rw [hξd] at this
    have hpos : 0 < q - q0 := by linarith
    rw [lt_div_iff₀ hpos] at this
    nlinarith

lemma tangent_le (hP : P.Standing) {q0 q : ℝ} (hq0 : 0 ≤ q0) (hq : 0 ≤ q) :
    P.c q0 + deriv P.c q0 * (q - q0) ≤ P.c q := by
  by_cases h : q = q0
  · subst h; simp
  · exact le_of_lt (tangent hP hq0 hq h)

/-- Basic facts collected. -/
structure Facts (P : Params) : Prop where
  hβ : 1 < P.β
  hqlow : 0 < P.qlow
  hb : 0 < P.b
  hqP : 0 < P.qP
  hPS : P.qP < P.qS
  hSQ : P.qS < P.qQ
  hlowP : P.qlow ≤ P.qP
  hcQb : P.c P.qQ ≤ P.b
  -- A := qS - c qS
  hA : ∀ q, 0 ≤ q → q - P.c q ≤ P.qS - P.c P.qS
  hA0 : 0 ≤ P.qS - P.c P.qS
  hB : ∀ q, 0 ≤ q → P.β * q - P.c q ≤ P.β * P.qQ - P.c P.qQ
  hBs : ∀ q, 0 ≤ q → q ≠ P.qQ → P.β * q - P.c q < P.β * P.qQ - P.c P.qQ
  hC : ∀ q, 0 ≤ q → q - P.β * P.c q ≤ P.qP - P.β * P.c P.qP
  hCs : ∀ q, 0 ≤ q → q ≠ P.qP → q - P.β * P.c q < P.qP - P.β * P.c P.qP
  hc0 : ∀ q, 0 ≤ q → 0 ≤ P.c q
  hcmono : ∀ q q', 0 ≤ q → q < q' → P.c q < P.c q'

lemma facts (hP : P.Standing) : Facts P := by
  have hP' := hP
  obtain ⟨hβ, hqlow, hb, hK, hc, hc0, hd0, hd1, hd2, hS0, hSd, hQ0, hQd, hP0, hPd, hlowP,
    hcQb, _, _, _⟩ := hP'
  have hmono := derivc_strictMono hP
  have hβpos : 0 < P.β := by linarith
  have hqP : 0 < P.qP := by
    by_contra h
    have : P.qP = 0 := le_antisymm (not_lt.mp h) hP0
    rw [this, hd0] at hPd
    have : 0 < 1 / P.β := by positivity
    linarith
  have hinvlt : 1 / P.β < 1 := by rw [div_lt_one hβpos]; exact hβ
  have hPS : P.qP < P.qS := by
    rw [← hmono.lt_iff_lt hP0 hS0, hPd, hSd]; exact hinvlt
  have hSQ : P.qS < P.qQ := by
    rw [← hmono.lt_iff_lt hS0 hQ0, hSd, hQd]; exact hβ
  have hA : ∀ q, 0 ≤ q → q - P.c q ≤ P.qS - P.c P.qS := by
    intro q hq
    have := tangent_le hP hS0 hq
    rw [hSd] at this
    linarith
  have hBs : ∀ q, 0 ≤ q → q ≠ P.qQ → P.β * q - P.c q < P.β * P.qQ - P.c P.qQ := by
    intro q hq hne
    have := tangent hP hQ0 hq hne
    rw [hQd] at this
    nlinarith
  have hCs : ∀ q, 0 ≤ q → q ≠ P.qP → q - P.β * P.c q < P.qP - P.β * P.c P.qP := by
    intro q hq hne
    have := tangent hP hP0 hq hne
    rw [hPd] at this
    have h2 : P.β * (P.c P.qP + 1 / P.β * (q - P.qP)) < P.β * P.c q :=
      mul_lt_mul_of_pos_left this hβpos
    have h3 : P.β * (P.c P.qP + 1 / P.β * (q - P.qP)) = P.β * P.c P.qP + (q - P.qP) := by
      field_simp
    linarith
  have hc0' : ∀ q, 0 ≤ q → 0 ≤ P.c q := by
    intro q hq
    have := tangent_le hP (le_refl 0) hq
    rw [hd0, hc0] at this
    linarith
  have hcmono : ∀ q q', 0 ≤ q → q < q' → P.c q < P.c q' := by
    intro q q' hq hqq
    have := tangent hP hq (by linarith) (ne_of_gt hqq)
    have hdq : 0 ≤ deriv P.c q := by
      rcases eq_or_lt_of_le hq with h | h
      · rw [← h, hd0]
      · exact le_of_lt (hd1 q h)
    nlinarith
  refine ⟨hβ, hqlow, hb, hqP, hPS, hSQ, hlowP, hcQb, hA, ?_, ?_, hBs, ?_, hCs, hc0', hcmono⟩
  · have := hA 0 (le_refl 0); rw [hc0] at this; linarith
  · intro q hq
    by_cases h : q = P.qQ
    · rw [h]
    · exact le_of_lt (hBs q hq h)
  · intro q hq
    by_cases h : q = P.qP
    · rw [h]
    · exact le_of_lt (hCs q hq h)

lemma facts2 (F : Facts P) :
    P.qS - P.c P.qS < P.β * P.qQ - P.c P.qQ ∧
    P.qS - P.c P.qS < nuQQ P ∧ nuQQ P < nuPQ P ∧ nuPP P < nuPQ P ∧
    P.qP - P.β * P.c P.qP ≤ P.qS - P.c P.qS ∧ 0 < nuQQ P ∧ 0 ≤ P.β * P.qQ - P.c P.qQ := by
  have hβ := F.hβ
  have hS0 : 0 ≤ P.qS := by linarith [F.hqP, F.hPS]
  have h1 := F.hB P.qS hS0
  have h2 : 0 < (P.β - 1) * P.qS := mul_pos (by linarith) (by linarith [F.hqP, F.hPS])
  have h3 : 0 < (P.β - 1) * (P.qS - P.qlow) :=
    mul_pos (by linarith) (by linarith [F.hPS, F.hlowP])
  have h4 : 0 < (P.β - 1) * (P.b + P.qlow) := mul_pos (by linarith) (by linarith [F.hb, F.hqlow])
  have h5 : 0 ≤ (P.β - 1) * P.c P.qP := mul_nonneg (by linarith) (F.hc0 _ (le_of_lt F.hqP))
  have h6 := F.hA P.qP (le_of_lt F.hqP)
  have hA0 := F.hA0
  unfold nuQQ nuPQ nuPP
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The good pairs, store-wide case. -/
def GoodSW (P : Params) (t a : Product) : Prop :=
  (t = tQ P ∧ a = aQ P ∧ nuPP P ≤ nuQQ P) ∨ (t = tP P ∧ a = aP P ∧ nuQQ P ≤ nuPP P)

lemma bound_sw (F : Facts P) (a t : Product) (ha : Acceptable P a) (ht : Acceptable P t)
    (hθ : a.θ = t.θ) (hv : val P.β a ≤ val P.β t) (hu : max (nuQQ P) (nuPP P) ≤ u a) :
    t.p - P.c t.q ≤ 0 ∧ (t.p - P.c t.q = 0 → GoodSW P t a) := by
  obtain ⟨hAQ, hAQQ, hQQPQ, hPPPQ, hCA, hQQpos, hB0⟩ := facts2 F
  have hβ := F.hβ
  have hu1 : nuQQ P ≤ u a := le_trans (le_max_left _ _) hu
  have hu2 : nuPP P ≤ u a := le_trans (le_max_right _ _) hu
  obtain ⟨qa, pa, θa⟩ := a
  obtain ⟨qt, pt, θt⟩ := t
  simp only [Acceptable] at ha ht
  simp only at hθ
  subst hθ
  have hqt0 : 0 ≤ qt := by linarith [F.hqlow]
  have hqa0 : 0 ≤ qa := by linarith [F.hqlow]
  simp only [u] at hu1 hu2 hu
  cases θa with
  | N =>
    simp only [val] at hv
    have := F.hA qt hqt0
    have hlt : pt - P.c qt < 0 := by linarith
    exact ⟨le_of_lt hlt, fun h => absurd h (ne_of_lt hlt)⟩
  | Q =>
    simp only [val] at hv
    have hB := F.hB qt hqt0
    have hm : 0 ≤ (P.β - 1) * (qa - P.qlow) := mul_nonneg (by linarith) (by linarith)
    have key : pt - P.c qt ≤ 0 := by unfold nuQQ at hu1; nlinarith
    refine ⟨key, fun h0 => ?_⟩
    simp only at h0
    have hqt : qt = P.qQ := by
      by_contra hne
      have := F.hBs qt hqt0 hne
      unfold nuQQ at hu1; nlinarith
    have hqa : qa = P.qlow := by
      by_contra hne
      have hm' : 0 < (P.β - 1) * (qa - P.qlow) :=
        mul_pos (by linarith) (lt_of_le_of_ne (by linarith) (fun h => hne (by linarith)))
      unfold nuQQ at hu1; nlinarith
    subst hqt hqa
    have hua : P.qlow - pa = nuQQ P := by unfold nuQQ at hu1 ⊢; nlinarith
    left
    refine ⟨?_, ?_, ?_⟩
    · simp only [tQ]; congr 1; linarith
    · simp only [aQ]; congr 1; unfold nuQQ at hua; linarith
    · have := le_max_right (nuQQ P) (nuPP P); linarith
  | P =>
    simp only [val] at hv
    have hC := F.hC qt hqt0
    have hm : 0 ≤ (P.β - 1) * (P.b - pa) := mul_nonneg (by linarith) (by linarith)
    have key' : P.β * (pt - P.c qt) ≤ nuPP P - (qa - pa) := by unfold nuPP; nlinarith
    have key : pt - P.c qt ≤ 0 := by
      by_contra hc
      have : 0 < P.β * (pt - P.c qt) := mul_pos (by linarith) (by linarith)
      linarith
    refine ⟨key, fun h0 => ?_⟩
    simp only at h0
    have hqt : qt = P.qP := by
      by_contra hne
      have := F.hCs qt hqt0 hne
      have : P.β * (pt - P.c qt) < nuPP P - (qa - pa) := by unfold nuPP; nlinarith
      rw [h0, mul_zero] at this; linarith
    have hpa : pa = P.b := by
      by_contra hne
      have hm' : 0 < (P.β - 1) * (P.b - pa) :=
        mul_pos (by linarith) (lt_of_le_of_ne (by linarith) (fun h => hne (by linarith)))
      have : P.β * (pt - P.c qt) < nuPP P - (qa - pa) := by unfold nuPP; nlinarith
      rw [h0, mul_zero] at this; linarith
    subst hqt hpa
    have hua : qa - P.b = nuPP P := by
      have : P.β * (pt - P.c P.qP) = 0 := by rw [h0, mul_zero]
      linarith
    right
    refine ⟨?_, ?_, ?_⟩
    · simp only [tP]; congr 1; linarith
    · simp only [aP]; congr 1; unfold nuPP at hua; linarith
    · have := le_max_left (nuQQ P) (nuPP P); linarith

/-- The good pairs, product-specific case. -/
def GoodPS (P : Params) (t a : Product) : Prop := t = tPQ P ∧ a = aPQ P

lemma bound_ps (F : Facts P) (a t : Product) (ha : Acceptable P a) (ht : Acceptable P t)
    (hv : val P.β a ≤ val P.β t) (hu : nuPQ P ≤ u a) :
    t.p - P.c t.q ≤ 0 ∧ (t.p - P.c t.q = 0 → GoodPS P t a) := by
  obtain ⟨hAQ, hAQQ, hQQPQ, hPPPQ, hCA, hQQpos, hB0⟩ := facts2 F
  have hβ := F.hβ
  obtain ⟨qa, pa, θa⟩ := a
  obtain ⟨qt, pt, θt⟩ := t
  simp only [Acceptable] at ha ht
  have hqt0 : 0 ≤ qt := by linarith [F.hqlow]
  have hqa0 : 0 ≤ qa := by linarith [F.hqlow]
  simp only [u] at hu
  have hA := F.hA qt hqt0
  have hB := F.hB qt hqt0
  have hC := F.hC qt hqt0
  have hb1 : 0 ≤ (P.β - 1) * (P.b - pa) := mul_nonneg (by linarith) (by linarith)
  have hb2 : 0 ≤ (P.β - 1) * qa := mul_nonneg (by linarith) (by linarith)
  have hb3 : 0 < (P.β - 1) * P.b := mul_pos (by linarith) F.hb
  -- strict cases
  have strict : pt - P.c qt < 0 → pt - P.c qt ≤ 0 ∧ (pt - P.c qt = 0 → GoodPS P ⟨qt, pt, θt⟩
      ⟨qa, pa, θa⟩) := fun h => ⟨le_of_lt h, fun h0 => absurd h0 (ne_of_lt h)⟩
  -- P-target strictness helper
  have ptarget : P.β * (pt - P.c qt) < 0 → pt - P.c qt < 0 := by
    intro h
    by_contra hc
    have : 0 ≤ P.β * (pt - P.c qt) := mul_nonneg (by linarith) (by linarith)
    linarith
  unfold nuPQ at hu
  unfold nuQQ at hAQQ hQQPQ
  unfold nuPP at hPPPQ
  cases θa <;> cases θt <;> simp only [val] at hv
  · exact strict (by linarith)
  · exact strict (by linarith)
  · exact strict (ptarget (by nlinarith))
  · exact strict (by nlinarith)
  · exact strict (by nlinarith)
  · exact strict (ptarget (by nlinarith))
  · exact strict (by nlinarith)
  · -- (P, Q): the extremal case
    have key : pt - P.c qt ≤ 0 := by nlinarith
    refine ⟨key, fun h0 => ?_⟩
    simp only at h0
    have hqt : qt = P.qQ := by
      by_contra hne
      have := F.hBs qt hqt0 hne
      nlinarith
    have hpa : pa = P.b := by
      by_contra hne
      have hm' : 0 < (P.β - 1) * (P.b - pa) :=
        mul_pos (by linarith) (lt_of_le_of_ne (by linarith) (fun h => hne (by linarith)))
      nlinarith
    subst hqt hpa
    refine ⟨?_, ?_⟩
    · simp only [tPQ]; congr 1; linarith
    · simp only [aPQ]; congr 1; nlinarith
  · exact strict (ptarget (by nlinarith))


/-! ### Menu lemmas -/

lemma mem_acc {M : Finset Product} {j : Product} : j ∈ acc P M ↔ j ∈ M ∧ Acceptable P j := by
  classical
  unfold acc; simp [Finset.mem_filter]

lemma mem_Pred {M : Finset Product} {γ : ℝ} {j : Product} :
    j ∈ Pred P M γ ↔ j ∈ acc P M ∧ ∀ j' ∈ acc P M, val γ j' ≤ val γ j := by
  classical
  unfold Pred; simp [Finset.mem_filter]

lemma mem_Bought {M : Finset Product} {j : Product} :
    j ∈ Bought P M ↔ j ∈ acc P M ∧ ∀ j' ∈ acc P M, val P.β j' ≤ val P.β j := mem_Pred

lemma exp_attained {M : Finset Product} {γ : ℝ} (h : (Pred P M γ).Nonempty) :
    ∃ a ∈ Pred P M γ, u a = ExpSurplus P M γ := by
  unfold ExpSurplus
  rw [dif_pos h]
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup' h u
  exact ⟨a, ha, he.symm⟩

lemma exp_le {M : Finset Product} {γ : ℝ} {a : Product} (ha : a ∈ Pred P M γ) :
    u a ≤ ExpSurplus P M γ := by
  have h : (Pred P M γ).Nonempty := ⟨a, ha⟩
  unfold ExpSurplus
  rw [dif_pos h]
  exact Finset.le_sup' u ha

lemma margin_ge {M : Finset Product} {t : Product} (ht : t ∈ Bought P M) :
    t.p - P.c t.q ≤ margin P M := by
  have h : (Bought P M).Nonempty := ⟨t, ht⟩
  unfold margin
  rw [dif_pos h]
  exact Finset.le_sup' (fun j => j.p - P.c j.q) ht

lemma margin_le {M : Finset Product} {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ t ∈ Bought P M, t.p - P.c t.q ≤ x) : margin P M ≤ x := by
  unfold margin
  split_ifs with hne
  · exact Finset.sup'_le hne _ h
  · exact hx

lemma margin_attained {M : Finset Product} (h : (Bought P M).Nonempty) :
    ∃ t ∈ Bought P M, t.p - P.c t.q = margin P M := by
  unfold margin
  rw [dif_pos h]
  obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup' h (fun j => j.p - P.c j.q)
  exact ⟨t, ht, he.symm⟩

lemma bought_nonempty {M : Finset Product} (h : (acc P M).Nonempty) : (Bought P M).Nonempty := by
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (acc P M) (val P.β) h
  exact ⟨t, mem_Bought.2 ⟨ht, hmax⟩⟩

lemma pred_sub_acc {M : Finset Product} {γ : ℝ} {a : Product} (ha : a ∈ Pred P M γ) :
    a ∈ acc P M := (mem_Pred.1 ha).1

lemma acc_pair {t a : Product} (ht : Acceptable P t) (ha : Acceptable P a) :
    acc P {t, a} = {t, a} := by
  ext j
  rw [mem_acc]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact ht
    · exact ha

lemma pred_pair {t a : Product} {γ : ℝ} (ht : Acceptable P t) (ha : Acceptable P a)
    (hlt : val γ t < val γ a) : Pred P {t, a} γ = {a} := by
  ext j
  rw [mem_Pred, acc_pair ht ha]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨rfl | rfl, h1, h2⟩
    · exact absurd h2 (not_le.2 hlt)
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, le_of_lt hlt, le_refl _⟩

lemma exp_pair {t a : Product} {γ : ℝ} (ht : Acceptable P t) (ha : Acceptable P a)
    (hlt : val γ t < val γ a) : ExpSurplus P {t, a} γ = u a := by
  have hp := pred_pair ht ha hlt
  have hne : (Pred P {t, a} γ).Nonempty := by rw [hp]; exact Finset.singleton_nonempty a
  unfold ExpSurplus
  rw [dif_pos hne]
  simp [hp]

lemma bought_pair {t a : Product} (ht : Acceptable P t) (ha : Acceptable P a)
    (hv : val P.β a ≤ val P.β t) : t ∈ Bought P {t, a} := by
  rw [mem_Bought, acc_pair ht ha]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨by simp, le_refl _, hv⟩

lemma nDist_eq_card {M : Finset Product} (h : ∀ j ∈ M, j.θ ≠ Ctx.N) : nDist M = M.card := by
  classical
  unfold nDist
  rw [Finset.filter_true_of_mem h]

lemma nDist_le_card (M : Finset Product) : nDist M ≤ M.card := by
  classical
  unfold nDist
  exact Finset.card_filter_le _ _


/-! ### Generic equilibrium analysis -/

structure Setup (P : Params) where
  Tech : Finset Product → Prop
  Compat : Product → Product → Prop
  V : ℝ
  Good : Product → Product → Prop
  hV : 0 ≤ V
  compat : ∀ M a t, Tech M → a ∈ M → t ∈ M → Compat a t
  bound : ∀ a t, Acceptable P a → Acceptable P t → Compat a t → val P.β a ≤ val P.β t →
    V ≤ u a → t.p - P.c t.q ≤ 0 ∧ (t.p - P.c t.q = 0 → Good t a)
  good : ∀ t a, Good t a → t ≠ a ∧ Tech {t, a} ∧ Acceptable P t ∧ Acceptable P a ∧ u a = V ∧
    t.p = P.c t.q ∧ a.p - P.c a.q < 0 ∧ val P.β a = val P.β t ∧
    (∀ γ ∈ Set.Ioo 1 P.β, val γ t < val γ a) ∧ t.θ ≠ Ctx.N ∧ a.θ ≠ Ctx.N
  exGood : ∃ t a, Good t a
  dev : ∃ ε0 > 0, ∀ ε, 0 < ε → ε < ε0 → ∃ M', Tech M' ∧ 0 < margin P M' ∧
    ∀ γ ∈ Set.Ioo 1 P.β, (Pred P M' γ).Nonempty ∧ V - ε ≤ ExpSurplus P M' γ ∧
      0 ≤ ExpSurplus P M' γ

variable (S : Setup P)

lemma good_pair {t a : Product} (hg : S.Good t a) :
    margin P {t, a} = 0 ∧ Sells P {t, a} t ∧
    ∀ γ ∈ Set.Ioo 1 P.β, Pred P {t, a} γ = {a} ∧ ExpSurplus P {t, a} γ = S.V := by
  obtain ⟨hne, hT, ht, ha, hua, htp, hap, hvb, hvg, _, _⟩ := S.good t a hg
  have htB : t ∈ Bought P {t, a} := bought_pair ht ha (le_of_eq hvb)
  have hsub : ∀ j ∈ Bought P {t, a}, j = t ∨ j = a := by
    intro j hj
    have := (mem_acc.1 (mem_Bought.1 hj).1).1
    simpa using this
  have hm : margin P {t, a} = 0 := by
    apply le_antisymm
    · apply margin_le (le_refl 0)
      intro j hj
      rcases hsub j hj with rfl | rfl
      · linarith
      · linarith
    · have := margin_ge htB; linarith
  refine ⟨hm, ⟨htB, ?_⟩, ?_⟩
  · intro j hj
    rcases hsub j hj with rfl | rfl
    · left; rfl
    · right; linarith
  · intro γ hγ
    exact ⟨pred_pair ht ha (hvg γ hγ), by rw [exp_pair ht ha (hvg γ hγ), hua]⟩

lemma dev_bound {M : Finset Product} {γ : ℝ} (hT : S.Tech M) (hne : (Pred P M γ).Nonempty)
    (hV : S.V ≤ ExpSurplus P M γ) : ∃ a ∈ Pred P M γ, u a = ExpSurplus P M γ ∧
      ∀ t ∈ Bought P M, t.p - P.c t.q ≤ 0 ∧ (t.p - P.c t.q = 0 → S.Good t a) := by
  obtain ⟨a, ha, hua⟩ := exp_attained hne
  refine ⟨a, ha, hua, fun t ht => ?_⟩
  obtain ⟨htacc, hmax⟩ := mem_Bought.1 ht
  have haacc := pred_sub_acc ha
  obtain ⟨haM, haA⟩ := mem_acc.1 haacc
  obtain ⟨htM, htA⟩ := mem_acc.1 htacc
  exact S.bound a t haA htA (S.compat M a t hT haM htM) (hmax a haacc) (by rw [hua]; exact hV)

lemma margin_nonpos {M : Finset Product} {γ : ℝ} (hT : S.Tech M)
    (hne : (Pred P M γ).Nonempty) (hV : S.V ≤ ExpSurplus P M γ) : margin P M ≤ 0 := by
  obtain ⟨a, _, _, hall⟩ := dev_bound S hT hne hV
  exact margin_le (le_refl 0) (fun t ht => (hall t ht).1)

lemma pos_of_sup (hprob : P.μ Set.univ = 1) (hnull : P.μ (Set.Ioo 1 P.β)ᶜ = 0) {E : Set ℝ}
    (h : Set.Ioo 1 P.β ⊆ E) : 0 < P.μ E := by
  have h1 : P.μ Set.univ ≤ P.μ (Set.Ioo 1 P.β) + P.μ (Set.Ioo 1 P.β)ᶜ := by
    rw [← Set.union_compl_self (Set.Ioo 1 P.β)]
    exact MeasureTheory.measure_union_le _ _
  rw [hprob, hnull, add_zero] at h1
  exact lt_of_lt_of_le (by norm_num) (le_trans h1 (MeasureTheory.measure_mono h))

lemma exists_good_point {E N : Set ℝ} (hE : 0 < P.μ E) (hN : P.μ N = 0) :
    ∃ γ ∈ E, γ ∉ N := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have : P.μ E = 0 := MeasureTheory.measure_mono_null (fun γ hγ => h γ hγ) hN
  rw [this] at hE
  exact lt_irrefl 0 hE

lemma exists_other (hK : 2 ≤ P.K) (k : Fin P.K) : ∃ k' : Fin P.K, k' ≠ k := by
  by_cases h : k.val = 0
  · refine ⟨⟨1, by omega⟩, fun h' => ?_⟩
    rw [Fin.ext_iff] at h'
    simp at h'
    omega
  · refine ⟨⟨0, by omega⟩, fun h' => ?_⟩
    rw [Fin.ext_iff] at h'
    simp at h'
    omega

lemma pred_empty {γ : ℝ} : ¬ (Pred P ∅ γ).Nonempty := by
  rintro ⟨j, hj⟩
  exact absurd (mem_acc.1 (pred_sub_acc hj)).1 (Finset.notMem_empty j)

lemma mem_active {σ : Profile P} {k : Fin P.K} : k ∈ active P σ ↔ PosDemand P σ k := by
  classical
  unfold active; simp


lemma entrant (hnull : P.μ (Set.Ioo 1 P.β)ᶜ = 0) {σ : Profile P} {k : Fin P.K}
    (h : PosDemand P σ k) : ∃ γ ∈ Set.Ioo 1 P.β, Enters P σ k γ := by
  obtain ⟨γ, hγ, hγN⟩ := exists_good_point h hnull
  exact ⟨γ, by simpa using hγN, hγ⟩

theorem exists_eq (hK : 2 ≤ P.K) (hprob : P.μ Set.univ = 1)
    (hnull : P.μ (Set.Ioo 1 P.β)ᶜ = 0) : ∃ σ : Profile P, IsCompEq P S.Tech σ := by
  obtain ⟨t0, a0, hg⟩ := S.exGood
  obtain ⟨hne0, hT0, ht0, ha0, hua0, htp0, hap0, hvb0, hvg0, hθt0, hθa0⟩ := S.good t0 a0 hg
  obtain ⟨hm0, hsells0, hpr0⟩ := good_pair S hg
  let σ0 : Profile P := fun _ => {t0, a0}
  have henter : ∀ k, ∀ γ ∈ Set.Ioo 1 P.β, Enters P σ0 k γ := by
    intro k γ hγ
    obtain ⟨hp, he⟩ := hpr0 γ hγ
    refine ⟨?_, ?_, ?_⟩
    · show (Pred P {t0, a0} γ).Nonempty
      rw [hp]; exact Finset.singleton_nonempty _
    · show 0 ≤ ExpSurplus P {t0, a0} γ
      rw [he]; exact S.hV
    · intro k' _
      show ExpSurplus P {t0, a0} γ ≤ ExpSurplus P {t0, a0} γ
      exact le_refl _
  have hpos : ∀ k, PosDemand P σ0 k := fun k => pos_of_sup hprob hnull (fun γ hγ => henter k γ hγ)
  -- the key deviation fact
  have hdev : ∀ k (M' : Finset Product), S.Tech M' →
      PosDemand P (Function.update σ0 k M') k →
      ∃ γ, (Pred P M' γ).Nonempty ∧ S.V ≤ ExpSurplus P M' γ := by
    intro k M' hT hpd
    obtain ⟨γ, hγ, hent⟩ := entrant hnull hpd
    obtain ⟨k', hk'⟩ := exists_other hK k
    obtain ⟨h1, _, h3⟩ := hent
    have := h3 k'
    rw [Function.update_of_ne hk', Function.update_self] at this
    rw [Function.update_self] at h1
    obtain ⟨hp, he⟩ := hpr0 γ hγ
    refine ⟨γ, h1, ?_⟩
    have hh := this (by show (Pred P {t0, a0} γ).Nonempty; rw [hp]; exact Finset.singleton_nonempty _)
    have : ExpSurplus P (σ0 k') γ = S.V := he
    linarith
  refine ⟨σ0, fun k => hT0, fun k _ => hm0, ?_, fun k h => absurd (hpos k) h, ?_⟩
  · intro k M' hT hpd
    obtain ⟨γ, h1, h2⟩ := hdev k M' hT hpd
    exact margin_nonpos S hT h1 h2
  · intro k _ M' hT hch hpd
    obtain ⟨γ, h1, h2⟩ := hdev k M' hT hpd
    obtain ⟨a, ha, _, hall⟩ := dev_bound S hT h1 h2
    have hle : margin P M' ≤ 0 := margin_le (le_refl 0) (fun t ht => (hall t ht).1)
    show margin P M' < margin P {t0, a0}
    rw [hm0]
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    exfalso
    have hBne : (Bought P M').Nonempty := bought_nonempty ⟨a, pred_sub_acc ha⟩
    obtain ⟨t, ht, htm⟩ := margin_attained hBne
    have hga : S.Good t a := (hall t ht).2 (by rw [htm, heq])
    obtain ⟨hne, _, _, _, _, _, _, _, _, hθt, hθa⟩ := S.good t a hga
    have htM : t ∈ M' := (mem_acc.1 (mem_Bought.1 ht).1).1
    have haM : a ∈ M' := (mem_acc.1 (pred_sub_acc ha)).1
    have hsub : ({t, a} : Finset Product) ⊆ M' := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact htM
      · exact haM
    have hc2 : ({t, a} : Finset Product).card = 2 := Finset.card_pair hne
    have hc0 : ({t0, a0} : Finset Product).card = 2 := Finset.card_pair hne0
    have hcM : 2 ≤ M'.card := hc2 ▸ Finset.card_le_card hsub
    have hσ : σ0 k = {t0, a0} := rfl
    rcases hch with hlt | ⟨hcard, hnd⟩
    · rw [hσ, hc0] at hlt; omega
    · rw [hσ, hc0] at hcard
      have hMeq : ({t, a} : Finset Product) = M' :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hc2])
      have hnd1 : nDist M' = 2 := by
        rw [← hMeq, nDist_eq_card, hc2]
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact hθt
        · exact hθa
      have hnd2 := nDist_le_card ({t0, a0} : Finset Product)
      rw [hσ] at hnd
      omega


theorem char_eq (hK : 2 ≤ P.K) (hprob : P.μ Set.univ = 1)
    (hnull : P.μ (Set.Ioo 1 P.β)ᶜ = 0) (σ : Profile P) (hσ : IsCompEq P S.Tech σ) :
    2 ≤ (active P σ).card ∧ (∀ k, ¬ PosDemand P σ k → σ k = ∅) ∧
      ∀ k, PosDemand P σ k → ∃ t a, S.Good t a ∧ Roles P (σ k) t a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hσ
  obtain ⟨ε0, hε0, hdev⟩ := S.dev
  refine ⟨?_, h4, ?_⟩
  · -- at least two active firms
    by_contra hlt
    have hle : (active P σ).card ≤ 1 := by omega
    have hk : ∃ k, ∀ k', k' ≠ k → σ k' = ∅ := by
      rcases (active P σ).eq_empty_or_nonempty with he | ⟨k, hk⟩
      · refine ⟨⟨0, by omega⟩, fun k' _ => h4 k' (fun hp => ?_)⟩
        have : k' ∈ active P σ := mem_active.2 hp
        rw [he] at this; exact Finset.notMem_empty _ this
      · refine ⟨k, fun k' hk' => h4 k' (fun hp => hk' ?_)⟩
        exact Finset.card_le_one.1 hle k' (mem_active.2 hp) k hk
    obtain ⟨k, hk⟩ := hk
    obtain ⟨M', hT, hmpos, hall⟩ := hdev (ε0 / 2) (by positivity) (by linarith)
    have hpd : PosDemand P (Function.update σ k M') k := by
      apply pos_of_sup hprob hnull
      intro γ hγ
      obtain ⟨hn, _, h0⟩ := hall γ hγ
      refine ⟨by rw [Function.update_self]; exact hn, by rw [Function.update_self]; exact h0, ?_⟩
      intro k'' hne
      by_cases hkk : k'' = k
      · subst hkk; exact le_refl _
      · rw [Function.update_of_ne hkk, hk k'' hkk] at hne
        exact absurd hne pred_empty
    have := h3 k M' hT hpd
    linarith
  · intro k hk
    let Sε : ℝ → Set ℝ := fun ε => {γ | γ ∈ Set.Ioo 1 P.β ∧ ∀ k' : Fin P.K,
      (Pred P (σ k') γ).Nonempty → ExpSurplus P (σ k') γ < S.V - ε}
    have hS : ∀ ε, 0 < ε → ε < ε0 → P.μ (Sε ε) = 0 := by
      intro ε hε hεlt
      by_contra hne
      obtain ⟨M', hT, hmpos, hall⟩ := hdev ε hε hεlt
      have hpd : PosDemand P (Function.update σ k M') k := by
        unfold PosDemand
        refine lt_of_lt_of_le (pos_iff_ne_zero.2 hne) (MeasureTheory.measure_mono ?_)
        intro γ hγ
        obtain ⟨hn, hV, h0⟩ := hall γ hγ.1
        refine ⟨by rw [Function.update_self]; exact hn, by rw [Function.update_self]; exact h0, ?_⟩
        intro k'' hne'
        rw [Function.update_self]
        by_cases hkk : k'' = k
        · subst hkk; rw [Function.update_self]
        · rw [Function.update_of_ne hkk] at hne' ⊢
          have := hγ.2 k'' hne'
          linarith
      have := h3 k M' hT hpd
      linarith
    let N : Set ℝ := (Set.Ioo 1 P.β)ᶜ ∪ ⋃ n : ℕ, Sε (ε0 / ((n : ℝ) + 2))
    have hN : P.μ N = 0 := by
      apply MeasureTheory.measure_union_null hnull
      apply MeasureTheory.measure_iUnion_null
      intro n
      apply hS
      · positivity
      · rw [div_lt_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
    let E : Set ℝ := {γ | Enters P σ k γ}
    have hgood : ∀ γ ∈ E, γ ∉ N → γ ∈ Set.Ioo 1 P.β ∧ S.V ≤ ExpSurplus P (σ k) γ := by
      intro γ hE hNγ
      simp only [N, Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_or, not_not,
        not_exists] at hNγ
      obtain ⟨hIoo, hnS⟩ := hNγ
      refine ⟨hIoo, ?_⟩
      by_contra hlt
      push Not at hlt
      have hδ : 0 < S.V - ExpSurplus P (σ k) γ := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (ε0 / (S.V - ExpSurplus P (σ k) γ))
      have hεn : ε0 / ((n : ℝ) + 2) < S.V - ExpSurplus P (σ k) γ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at hn
        nlinarith
      have := hnS n
      simp only [Sε, Set.mem_setOf_eq, not_and, not_forall, not_lt] at this
      obtain ⟨k', hne, hge⟩ := this hIoo
      have := hE.2.2 k' hne
      linarith
    have hpair : ∀ γ ∈ E, γ ∉ N → ∀ t ∈ Bought P (σ k), t.p - P.c t.q = 0 →
        ∃ a ∈ Pred P (σ k) γ, S.Good t a ∧ u a = ExpSurplus P (σ k) γ := by
      intro γ hE hNγ t ht ht0
      obtain ⟨a, ha, hua, hall⟩ := dev_bound S (h1 k) hE.1 (hgood γ hE hNγ).2
      exact ⟨a, ha, (hall t ht).2 ht0, hua⟩
    obtain ⟨γ0, hE0, hN0⟩ := exists_good_point hk hN
    have hBne : (Bought P (σ k)).Nonempty := by
      obtain ⟨j, hj⟩ := hE0.1
      exact bought_nonempty ⟨j, pred_sub_acc hj⟩
    obtain ⟨t, htB, htm⟩ := margin_attained hBne
    rw [h2 k hk] at htm
    obtain ⟨a, haP, hga, hua⟩ := hpair γ0 hE0 hN0 t htB htm
    obtain ⟨hne, hTta, _, _, _, _, _, _, _, _, _⟩ := S.good t a hga
    obtain ⟨hmta, hsells, hprta⟩ := good_pair S hga
    have htM : t ∈ σ k := (mem_acc.1 (mem_Bought.1 htB).1).1
    have haM : a ∈ σ k := (mem_acc.1 (pred_sub_acc haP)).1
    have hsub : ({t, a} : Finset Product) ⊆ σ k := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact htM
      · exact haM
    have hc2 : ({t, a} : Finset Product).card = 2 := Finset.card_pair hne
    have hpd : PosDemand P (Function.update σ k {t, a}) k := by
      unfold PosDemand
      have hEN : P.μ (E \ N) = P.μ E := MeasureTheory.measure_diff_null hN
      have hk' : 0 < P.μ (E \ N) := by rw [hEN]; exact hk
      refine lt_of_lt_of_le hk' (MeasureTheory.measure_mono ?_)
      intro γ ⟨hE, hNγ⟩
      obtain ⟨hIoo, _⟩ := hgood γ hE hNγ
      obtain ⟨a', _, hga', hua'⟩ := hpair γ hE hNγ t htB htm
      have hVeq : ExpSurplus P (σ k) γ = S.V := by
        rw [← hua']; exact (S.good t a' hga').2.2.2.2.1
      obtain ⟨hp, he⟩ := hprta γ hIoo
      refine ⟨?_, ?_, ?_⟩
      · rw [Function.update_self, hp]; exact Finset.singleton_nonempty _
      · rw [Function.update_self, he]; exact S.hV
      · intro k'' hne''
        rw [Function.update_self, he]
        by_cases hkk : k'' = k
        · subst hkk; rw [Function.update_self, he]
        · rw [Function.update_of_ne hkk] at hne'' ⊢
          have := hE.2.2 k'' hne''
          linarith
    have hnotch : ¬ Cheaper ({t, a} : Finset Product) (σ k) := by
      intro hch
      have := h5 k hk {t, a} hTta hch hpd
      rw [hmta, h2 k hk] at this
      exact lt_irrefl 0 this
    have hcard : (σ k).card ≤ 2 := by
      by_contra hc
      exact hnotch (Or.inl (by omega))
    have heq : ({t, a} : Finset Product) = σ k :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    refine ⟨t, a, hga, heq.symm, hne, by rw [← heq]; exact hsells, ?_⟩
    intro γ hγ
    rw [← heq]
    exact (hprta γ hγ).1


/-! ### The concrete pairs -/

lemma dev_pair {Tech : Finset Product → Prop} {V ε : ℝ} (t a : Product) (hT : Tech {t, a})
    (ht : Acceptable P t) (ha : Acceptable P a) (hv : val P.β a ≤ val P.β t)
    (hg : ∀ γ ∈ Set.Ioo 1 P.β, val γ t < val γ a) (hm : 0 < t.p - P.c t.q)
    (hu : u a = V - ε) (h0 : 0 ≤ V - ε) :
    ∃ M', Tech M' ∧ 0 < margin P M' ∧ ∀ γ ∈ Set.Ioo 1 P.β, (Pred P M' γ).Nonempty ∧
      V - ε ≤ ExpSurplus P M' γ ∧ 0 ≤ ExpSurplus P M' γ := by
  refine ⟨{t, a}, hT, lt_of_lt_of_le hm (margin_ge (bought_pair ht ha hv)), ?_⟩
  intro γ hγ
  rw [pred_pair ht ha (hg γ hγ), exp_pair ht ha (hg γ hγ), hu]
  exact ⟨Finset.singleton_nonempty _, le_refl _, h0⟩

lemma pairQ (F : Facts P) : tQ P ≠ aQ P ∧ StoreWide {tQ P, aQ P} ∧ Acceptable P (tQ P) ∧
    Acceptable P (aQ P) ∧ u (aQ P) = nuQQ P ∧ (tQ P).p = P.c (tQ P).q ∧
    (aQ P).p - P.c (aQ P).q < 0 ∧ val P.β (aQ P) = val P.β (tQ P) ∧
    (∀ γ ∈ Set.Ioo 1 P.β, val γ (tQ P) < val γ (aQ P)) ∧ (tQ P).θ ≠ Ctx.N ∧
    (aQ P).θ ≠ Ctx.N := by
  have hβ := F.hβ
  have hlQ : P.qlow < P.qQ := by linarith [F.hlowP, F.hPS, F.hSQ]
  have hm : 0 < P.β * (P.qQ - P.qlow) := mul_pos (by linarith) (by linarith)
  refine ⟨?_, ?_, ⟨le_of_lt hlQ, F.hcQb⟩, ⟨le_refl _, ?_⟩, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Product.q h
    simp only [tQ, aQ] at this
    linarith
  · intro j hj j' hj'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hj'
    rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl <;> rfl
  · simp only [aQ]; linarith [F.hcQb]
  · simp only [u, aQ, nuQQ]; ring
  · simp only [aQ]
    have := F.hBs P.qlow (le_of_lt F.hqlow) (ne_of_lt hlQ)
    linarith
  · simp only [val, aQ, tQ]; ring
  · intro γ hγ
    simp only [val, aQ, tQ]
    have : 0 < (P.β - γ) * (P.qQ - P.qlow) := mul_pos (by linarith [hγ.2]) (by linarith)
    nlinarith
  · simp [tQ]
  · simp [aQ]

lemma pairP (F : Facts P) : tP P ≠ aP P ∧ StoreWide {tP P, aP P} ∧ Acceptable P (tP P) ∧
    Acceptable P (aP P) ∧ u (aP P) = nuPP P ∧ (tP P).p = P.c (tP P).q ∧
    (aP P).p - P.c (aP P).q < 0 ∧ val P.β (aP P) = val P.β (tP P) ∧
    (∀ γ ∈ Set.Ioo 1 P.β, val γ (tP P) < val γ (aP P)) ∧ (tP P).θ ≠ Ctx.N ∧
    (aP P).θ ≠ Ctx.N := by
  have hβ := F.hβ
  have hcP : P.c P.qP < P.b :=
    lt_of_lt_of_le (F.hcmono _ _ (le_of_lt F.hqP) (by linarith [F.hPS, F.hSQ])) F.hcQb
  have hm : 0 < P.β * (P.b - P.c P.qP) := mul_pos (by linarith) (by linarith)
  refine ⟨?_, ?_, ⟨F.hlowP, by simp only [tP]; linarith⟩, ⟨?_, le_refl _⟩, ?_, rfl, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro h
    have := congrArg Product.q h
    simp only [tP, aP] at this
    linarith
  · intro j hj j' hj'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hj'
    rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl <;> rfl
  · simp only [aP]; linarith [F.hlowP]
  · simp only [u, aP, nuPP]; ring
  · simp only [aP]
    have hq0 : 0 ≤ P.qP + P.β * (P.b - P.c P.qP) := by linarith [F.hqP]
    have := F.hCs _ hq0 (by intro h; linarith)
    nlinarith
  · simp only [val, aP, tP]; ring
  · intro γ hγ
    simp only [val, aP, tP]
    have : 0 < (P.β - γ) * (P.b - P.c P.qP) := mul_pos (by linarith [hγ.2]) (by linarith)
    nlinarith
  · simp [tP]
  · simp [aP]

lemma pairPQ (F : Facts P) : tPQ P ≠ aPQ P ∧ ProductSpecific {tPQ P, aPQ P} ∧
    Acceptable P (tPQ P) ∧
    Acceptable P (aPQ P) ∧ u (aPQ P) = nuPQ P ∧ (tPQ P).p = P.c (tPQ P).q ∧
    (aPQ P).p - P.c (aPQ P).q < 0 ∧ val P.β (aPQ P) = val P.β (tPQ P) ∧
    (∀ γ ∈ Set.Ioo 1 P.β, val γ (tPQ P) < val γ (aPQ P)) ∧ (tPQ P).θ ≠ Ctx.N ∧
    (aPQ P).θ ≠ Ctx.N := by
  obtain ⟨hAQ, hAQQ, hQQPQ, hPPPQ, hCA, hQQpos, hB0⟩ := facts2 F
  have hβ := F.hβ
  have hlQ : P.qlow < P.qQ := by linarith [F.hlowP, F.hPS, F.hSQ]
  have hQ0 : 0 < P.qQ := by linarith [F.hqlow]
  have h1 : 0 ≤ (P.β - 1) * P.qQ := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (P.β - 1) * P.b := mul_nonneg (by linarith) (by linarith [F.hb])
  have hgap : P.qQ ≤ P.β * (P.qQ + P.b) - P.c P.qQ := by nlinarith [F.hcQb]
  refine ⟨?_, trivial, ⟨le_of_lt hlQ, F.hcQb⟩, ⟨by simp only [aPQ]; linarith, le_refl _⟩, ?_,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Product.θ h
    simp [tPQ, aPQ] at this
  · simp only [u, aPQ, nuPQ]; ring
  · simp only [aPQ]
    have hq0 : 0 ≤ P.β * (P.qQ + P.b) - P.c P.qQ := by linarith
    have hB := F.hB _ hq0
    have h3 : 0 < (P.β ^ 2 - 1) * P.b := mul_pos (by nlinarith) F.hb
    have h4 : 0 ≤ (P.β - 1) * (P.β * P.qQ - P.c P.qQ) := mul_nonneg (by linarith) hB0
    nlinarith
  · simp only [val, aPQ, tPQ]; ring
  · intro γ hγ
    simp only [val, aPQ, tPQ]
    have : 0 < (P.β - γ) * (P.qQ + P.b) := mul_pos (by linarith [hγ.2]) (by linarith [F.hb])
    nlinarith
  · simp [tPQ]
  · simp [aPQ]


lemma devQ (F : Facts P) : ∃ ε0 > 0, ∀ ε, 0 < ε → ε < ε0 → ∃ M', StoreWide M' ∧
    0 < margin P M' ∧ ∀ γ ∈ Set.Ioo 1 P.β, (Pred P M' γ).Nonempty ∧
      nuQQ P - ε ≤ ExpSurplus P M' γ ∧ 0 ≤ ExpSurplus P M' γ := by
  obtain ⟨hAQ, hAQQ, hQQPQ, hPPPQ, hCA, hQQpos, hB0⟩ := facts2 F
  have hβ := F.hβ
  have hlQ : P.qlow < P.qQ := by linarith [F.hlowP, F.hPS, F.hSQ]
  refine ⟨min (P.qQ - P.qlow) (nuQQ P), lt_min (by linarith) hQQpos, fun ε hε hlt => ?_⟩
  have hε1 : ε < P.qQ - P.qlow := lt_of_lt_of_le hlt (min_le_left _ _)
  have hε2 : ε < nuQQ P := lt_of_lt_of_le hlt (min_le_right _ _)
  set δ := ε / P.β with hδdef
  have hδ : P.β * δ = ε := by rw [hδdef]; field_simp
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by rw [hδdef, div_lt_iff₀ (by linarith)]; nlinarith
  apply dev_pair (Tech := StoreWide) ⟨P.qQ - δ, P.c P.qQ, Ctx.Q⟩
    ⟨P.qlow, P.c P.qQ - P.β * (P.qQ - P.qlow) + ε, Ctx.Q⟩
  · intro j hj j' hj'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hj'
    rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl <;> rfl
  · exact ⟨by simp only; linarith, F.hcQb⟩
  · refine ⟨le_refl _, ?_⟩
    simp only
    have : ε ≤ P.β * (P.qQ - P.qlow) := by nlinarith
    linarith [F.hcQb]
  · simp only [val]; nlinarith
  · intro γ hγ
    simp only [val]
    have : 0 < (P.β - γ) * (P.qQ - P.qlow - δ) := mul_pos (by linarith [hγ.2]) (by linarith)
    nlinarith
  · simp only
    have := F.hcmono (P.qQ - δ) P.qQ (by linarith [F.hqlow]) (by linarith)
    linarith
  · simp only [u, nuQQ]; ring
  · linarith

lemma devP (F : Facts P) (hpos : 0 < nuPP P) : ∃ ε0 > 0, ∀ ε, 0 < ε → ε < ε0 → ∃ M',
    StoreWide M' ∧ 0 < margin P M' ∧ ∀ γ ∈ Set.Ioo 1 P.β, (Pred P M' γ).Nonempty ∧
      nuPP P - ε ≤ ExpSurplus P M' γ ∧ 0 ≤ ExpSurplus P M' γ := by
  have hβ := F.hβ
  have hcP : P.c P.qP < P.b :=
    lt_of_lt_of_le (F.hcmono _ _ (le_of_lt F.hqP) (by linarith [F.hPS, F.hSQ])) F.hcQb
  refine ⟨min (P.b - P.c P.qP) (nuPP P), lt_min (by linarith) hpos, fun ε hε hlt => ?_⟩
  have hε1 : ε < P.b - P.c P.qP := lt_of_lt_of_le hlt (min_le_left _ _)
  have hε2 : ε < nuPP P := lt_of_lt_of_le hlt (min_le_right _ _)
  set δ := ε / P.β with hδdef
  have hδ : P.β * δ = ε := by rw [hδdef]; field_simp
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by rw [hδdef, div_lt_iff₀ (by linarith)]; nlinarith
  have hm : ε < P.β * (P.b - P.c P.qP) := by nlinarith
  apply dev_pair (Tech := StoreWide) ⟨P.qP, P.c P.qP + δ, Ctx.P⟩
    ⟨P.qP + P.β * (P.b - P.c P.qP) - ε, P.b, Ctx.P⟩
  · intro j hj j' hj'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hj'
    rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl <;> rfl
  · exact ⟨F.hlowP, by simp only; linarith⟩
  · refine ⟨?_, le_refl _⟩
    simp only
    linarith [F.hlowP]
  · simp only [val]; nlinarith
  · intro γ hγ
    simp only [val]
    have : 0 < (P.β - γ) * (P.b - P.c P.qP - δ) := mul_pos (by linarith [hγ.2]) (by linarith)
    nlinarith
  · simp only; linarith
  · simp only [u, nuPP]; ring
  · linarith

lemma devPQ (F : Facts P) : ∃ ε0 > 0, ∀ ε, 0 < ε → ε < ε0 → ∃ M', ProductSpecific M' ∧
    0 < margin P M' ∧ ∀ γ ∈ Set.Ioo 1 P.β, (Pred P M' γ).Nonempty ∧
      nuPQ P - ε ≤ ExpSurplus P M' γ ∧ 0 ≤ ExpSurplus P M' γ := by
  obtain ⟨hAQ, hAQQ, hQQPQ, hPPPQ, hCA, hQQpos, hB0⟩ := facts2 F
  have hβ := F.hβ
  have hlQ : P.qlow < P.qQ := by linarith [F.hlowP, F.hPS, F.hSQ]
  refine ⟨min (P.qQ - P.qlow) (nuPQ P), lt_min (by linarith) (by linarith),
    fun ε hε hlt => ?_⟩
  have hε1 : ε < P.qQ - P.qlow := lt_of_lt_of_le hlt (min_le_left _ _)
  have hε2 : ε < nuPQ P := lt_of_lt_of_le hlt (min_le_right _ _)
  set δ := ε / P.β with hδdef
  have hδ : P.β * δ = ε := by rw [hδdef]; field_simp
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by rw [hδdef, div_lt_iff₀ (by linarith)]; nlinarith
  have h1 : 0 ≤ (P.β - 1) * P.qQ := mul_nonneg (by linarith) (by linarith [F.hqlow])
  have h2 : 0 ≤ (P.β - 1) * P.b := mul_nonneg (by linarith) (by linarith [F.hb])
  have hgap : P.qQ ≤ P.β * (P.qQ + P.b) - P.c P.qQ := by nlinarith [F.hcQb]
  apply dev_pair (Tech := ProductSpecific) ⟨P.qQ - δ, P.c P.qQ, Ctx.Q⟩
    ⟨P.β * (P.qQ + P.b) - P.c P.qQ - ε, P.b, Ctx.P⟩ trivial
  · exact ⟨by simp only; linarith, F.hcQb⟩
  · refine ⟨?_, le_refl _⟩
    simp only
    linarith
  · simp only [val]; nlinarith
  · intro γ hγ
    simp only [val]
    have : 0 < (P.β - γ) * (P.qQ + P.b - δ) := mul_pos (by linarith [hγ.2])
      (by linarith [F.hb, F.hqlow])
    nlinarith
  · simp only
    have := F.hcmono (P.qQ - δ) P.qQ (by linarith [F.hqlow]) (by linarith)
    linarith
  · simp only [u, nuPQ]; ring
  · linarith

def setupSW (hP : P.Standing) : Setup P where
  Tech := StoreWide
  Compat := fun a t => a.θ = t.θ
  V := max (nuQQ P) (nuPP P)
  Good := GoodSW P
  hV := le_trans (le_of_lt (facts2 (facts hP)).2.2.2.2.2.1) (le_max_left _ _)
  compat := fun M a t hT ha ht => hT a ha t ht
  bound := fun a t ha ht hc hv hu => bound_sw (facts hP) a t ha ht hc hv hu
  good := by
    have F := facts hP
    intro t a hg
    rcases hg with ⟨rfl, rfl, hle⟩ | ⟨rfl, rfl, hle⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := pairQ F
      exact ⟨h1, h2, h3, h4, by rw [h5, max_eq_left hle], h6, h7, h8, h9, h10, h11⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := pairP F
      exact ⟨h1, h2, h3, h4, by rw [h5, max_eq_right hle], h6, h7, h8, h9, h10, h11⟩
  exGood := by
    rcases le_total (nuPP P) (nuQQ P) with h | h
    · exact ⟨tQ P, aQ P, Or.inl ⟨rfl, rfl, h⟩⟩
    · exact ⟨tP P, aP P, Or.inr ⟨rfl, rfl, h⟩⟩
  dev := by
    have F := facts hP
    rcases le_total (nuPP P) (nuQQ P) with h | h
    · rw [max_eq_left h]; exact devQ F
    · rw [max_eq_right h]
      exact devP F (lt_of_lt_of_le (facts2 F).2.2.2.2.2.1 h)

def setupPS (hP : P.Standing) : Setup P where
  Tech := ProductSpecific
  Compat := fun _ _ => True
  V := nuPQ P
  Good := GoodPS P
  hV := le_of_lt (lt_trans (facts2 (facts hP)).2.2.2.2.2.1 (facts2 (facts hP)).2.2.1)
  compat := fun _ _ _ _ _ _ => trivial
  bound := fun a t ha ht _ hv hu => bound_ps (facts hP) a t ha ht hv hu
  good := by
    have F := facts hP
    intro t a hg
    obtain ⟨rfl, rfl⟩ := hg
    exact pairPQ F
  exGood := ⟨tPQ P, aPQ P, rfl, rfl⟩
  dev := devPQ (facts hP)

end Prop2Aux

end ContextFooling.FoolingEq

open ContextFooling.FoolingEq ContextFooling.FoolingEq.Prop2Aux in
theorem solution (P : Params) (hP : P.Standing) (hopt : P.μ (Set.Iio P.β)ᶜ = 0) :
    -- a) store-wide distortions
    (∃ σ : Profile P, IsCompEq P StoreWide σ) ∧
    (∀ σ : Profile P, IsCompEq P StoreWide σ →
      2 ≤ (active P σ).card ∧ (∀ k, ¬ PosDemand P σ k → σ k = ∅) ∧
      ∀ k, PosDemand P σ k →
        (nuPP P < nuQQ P → Roles P (σ k) (tQ P) (aQ P)) ∧
        (nuQQ P < nuPP P → Roles P (σ k) (tP P) (aP P)) ∧
        (nuQQ P = nuPP P → Roles P (σ k) (tQ P) (aQ P) ∨ Roles P (σ k) (tP P) (aP P))) ∧
    -- b) product-specific distortions
    (∃ σ : Profile P, IsCompEq P ProductSpecific σ) ∧
    (∀ σ : Profile P, IsCompEq P ProductSpecific σ →
      2 ≤ (active P σ).card ∧ (∀ k, ¬ PosDemand P σ k → σ k = ∅) ∧
      ∀ k, PosDemand P σ k → Roles P (σ k) (tPQ P) (aPQ P)) ∧
    -- the comparisons the proposition states about these products
    P.qS < P.qQ ∧ P.qP < P.qS ∧
    (aQ P).q < (tQ P).q ∧ (aQ P).p < (tQ P).p ∧ (aQ P).p < P.c (aQ P).q ∧
    (tP P).q < (aP P).q ∧ (tP P).p < (aP P).p ∧ (aP P).p < P.c (aP P).q ∧
    (tPQ P).q < (aPQ P).q ∧ (tPQ P).p ≤ (aPQ P).p ∧ (P.c P.qQ < P.b → (tPQ P).p < (aPQ P).p) ∧
    (aPQ P).p < P.c (aPQ P).q := by
  have F := facts hP
  have hP' := hP
  obtain ⟨hβ, _, _, hK, _, _, _, _, _, _, _, _, _, _, _, _, _, hprobI, _, hlow⟩ := hP'
  have hprob : P.μ Set.univ = 1 := MeasureTheory.measure_univ
  have hnull : P.μ (Set.Ioo 1 P.β)ᶜ = 0 := by
    rw [← Set.Ioi_inter_Iio, Set.compl_inter]
    exact MeasureTheory.measure_union_null hlow hopt
  have exA := exists_eq (setupSW hP) hK hprob hnull
  have chA := char_eq (setupSW hP) hK hprob hnull
  have exB := exists_eq (setupPS hP) hK hprob hnull
  have chB := char_eq (setupPS hP) hK hprob hnull
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := pairQ F
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := pairP F
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := pairPQ F
  have hlQ : P.qlow < P.qQ := by linarith [F.hlowP, F.hPS, F.hSQ]
  have hcP : P.c P.qP < P.b :=
    lt_of_lt_of_le (F.hcmono _ _ (le_of_lt F.hqP) (by linarith [F.hPS, F.hSQ])) F.hcQb
  refine ⟨exA, ?_, exB, ?_, F.hSQ, F.hPS, ?_, ?_, by linarith, ?_, ?_, by linarith, ?_,
    ?_, ?_, by linarith⟩
  · intro σ hσ
    obtain ⟨c1, c2, c3⟩ := chA σ hσ
    refine ⟨c1, c2, fun k hk => ?_⟩
    obtain ⟨t, a, hg, hr⟩ := c3 k hk
    rcases hg with ⟨rfl, rfl, hle⟩ | ⟨rfl, rfl, hle⟩
    · refine ⟨fun _ => hr, fun h => absurd hle (not_le.2 h), fun _ => Or.inl hr⟩
    · refine ⟨fun h => absurd hle (not_le.2 h), fun _ => hr, fun _ => Or.inr hr⟩
  · intro σ hσ
    obtain ⟨c1, c2, c3⟩ := chB σ hσ
    refine ⟨c1, c2, fun k hk => ?_⟩
    obtain ⟨t, a, ⟨rfl, rfl⟩, hr⟩ := c3 k hk
    exact hr
  · simp only [aQ, tQ]; exact hlQ
  · simp only [aQ, tQ]
    have : 0 < P.β * (P.qQ - P.qlow) := mul_pos (by linarith) (by linarith)
    linarith
  · simp only [aP, tP]
    have : 0 < P.β * (P.b - P.c P.qP) := mul_pos (by linarith) (by linarith)
    linarith
  · simp only [aP, tP]; exact hcP
  · simp only [aPQ, tPQ]
    have h1 : 0 ≤ (P.β - 1) * P.qQ := mul_nonneg (by linarith) (by linarith [F.hqlow])
    have h2 : 0 < (P.β - 1) * P.b := mul_pos (by linarith) F.hb
    nlinarith [F.hcQb]
  · simp only [aPQ, tPQ]; exact F.hcQb
  · intro h; simp only [aPQ, tPQ]; exact h
