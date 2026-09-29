-- Prove2me | solution 1 for CursoEDO.picard_global_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T15:45:23.276022+00:00
-- url     : https://prove2.me/submissions/688506b5-c65a-45fb-b8c9-46a2fac8d8de

import Mathlib
import Definitions.Def_CursoEDO_Defs

/-!
# Corolário 2.1.3 — existence and uniqueness on a whole interval

Submission for the Prove2Me milestone "Corolário 2.1.3 — solution on the whole interval"
of the mission "Curso de EDO I: Picard Existence and Uniqueness".
-/

open CursoEDO Metric Set Function

namespace GlobalPicardAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Short-step existence.** On a compact subinterval `[u,v]` of `I` of length at most
`1/(2c)`, the Cauchy problem starting at any time `t₁ ∈ [u,v]` from any point `x₁` has a
solution on `[u,v]`.  The radius of the ball used in Picard–Lindelöf is `2 C (v-u)`, where
`C` bounds `‖f t x₁‖` on `[u,v]`. -/
theorem exists_sol_short [CompleteSpace E]
    {f : ℝ → E → E} {I : Set ℝ} {c : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) (I ×ˢ (univ : Set E)))
    (hlip : ∀ t ∈ I, ∀ x y : E, ‖f t x - f t y‖ ≤ c * ‖x - y‖)
    {u v t₁ : ℝ} (hsub : Icc u v ⊆ I) (ht₁ : t₁ ∈ Icc u v) (hshort : c * (v - u) ≤ 1 / 2)
    (x₁ : E) :
    ∃ α : ℝ → E, α t₁ = x₁ ∧ ∀ t ∈ Icc u v, HasDerivWithinAt α (f t (α t)) (Icc u v) t := by
  have hmap : ∀ x : E, MapsTo (fun t : ℝ => (t, x)) (Icc u v) (I ×ˢ (univ : Set E)) :=
    fun x t ht => ⟨hsub ht, mem_univ _⟩
  have hcontx : ∀ x : E, ContinuousOn (fun t : ℝ => f t x) (Icc u v) := fun x =>
    hcont.comp (Continuous.continuousOn (by fun_prop)) (hmap x)
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := u) (b := v)).exists_bound_of_continuousOn (hcontx x₁)
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ t ∈ Icc u v, ‖f t x₁‖ ≤ C := fun t ht => (hC₀ t ht).trans (le_max_left _ _)
  have huv : u ≤ v := ht₁.1.trans ht₁.2
  set T : ℝ := v - u with hTdef
  have hT0 : 0 ≤ T := by simp [hTdef]; linarith
  set a : ℝ := 2 * C * T with hadef
  have ha0 : 0 ≤ a := by positivity
  set L : ℝ := C + c * a with hLdef
  have hL0 : 0 ≤ L := by positivity
  obtain ⟨an, han⟩ : ∃ an : NNReal, (an : ℝ) = a := ⟨a.toNNReal, Real.coe_toNNReal a ha0⟩
  obtain ⟨Ln, hLn⟩ : ∃ Ln : NNReal, (Ln : ℝ) = L := ⟨L.toNNReal, Real.coe_toNNReal L hL0⟩
  obtain ⟨cn, hcn⟩ : ∃ cn : NNReal, (cn : ℝ) = c := ⟨c.toNNReal, Real.coe_toNNReal c hc.le⟩
  have hball : ∀ x ∈ closedBall x₁ (an : ℝ), ‖x - x₁‖ ≤ a := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, han] at hx
    exact hx
  have hPL : IsPicardLindelof f (⟨t₁, ht₁⟩ : Icc u v) x₁ an 0 Ln cn := by
    constructor
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      rw [dist_eq_norm, dist_eq_norm, hcn]
      exact hlip t (hsub ht) x y
    · intro x _
      exact hcontx x
    · intro t ht x hx
      have h1 : ‖f t x - f t x₁‖ ≤ c * ‖x - x₁‖ := hlip t (hsub ht) x x₁
      have h2 : ‖f t x‖ ≤ ‖f t x₁‖ + ‖f t x - f t x₁‖ := by
        simpa using norm_add_le (f t x₁) (f t x - f t x₁)
      have h3 : c * ‖x - x₁‖ ≤ c * a := by
        have := hball x hx
        nlinarith [norm_nonneg (x - x₁)]
      rw [hLn, hLdef]
      have := hC t ht
      linarith
    · have hmax : max (v - (⟨t₁, ht₁⟩ : Icc u v) : ℝ) ((⟨t₁, ht₁⟩ : Icc u v) - u) ≤ T := by
        have h1 : ((⟨t₁, ht₁⟩ : Icc u v) : ℝ) = t₁ := rfl
        rw [h1, hTdef]
        exact max_le (by linarith [ht₁.1]) (by linarith [ht₁.2])
      have hLT : L * T ≤ a := by
        have hCT : 0 ≤ C * T := by positivity
        nlinarith
      calc (Ln : ℝ) * max (v - (⟨t₁, ht₁⟩ : Icc u v) : ℝ) ((⟨t₁, ht₁⟩ : Icc u v) - u)
          ≤ (Ln : ℝ) * T := by rw [hLn]; exact mul_le_mul_of_nonneg_left hmax hL0
        _ ≤ (an : ℝ) - 0 := by rw [hLn, han]; simpa using hLT
  obtain ⟨α, hα₀, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα₀, hα⟩

/-- **Gluing.** Two solutions on adjacent intervals that match at the common endpoint
combine into a solution on the union. -/
theorem exists_glue {f : ℝ → E → E} {u w v : ℝ} (huw : u ≤ w) (hwv : w ≤ v)
    {φ₁ φ₂ : ℝ → E}
    (h1 : ∀ t ∈ Icc u w, HasDerivWithinAt φ₁ (f t (φ₁ t)) (Icc u w) t)
    (h2 : ∀ t ∈ Icc w v, HasDerivWithinAt φ₂ (f t (φ₂ t)) (Icc w v) t)
    (hmatch : φ₂ w = φ₁ w) :
    ∃ φ : ℝ → E, EqOn φ φ₁ (Icc u w) ∧ EqOn φ φ₂ (Icc w v) ∧
      ∀ t ∈ Icc u v, HasDerivWithinAt φ (f t (φ t)) (Icc u v) t := by
  classical
  set φ : ℝ → E := fun t => if t ≤ w then φ₁ t else φ₂ t with hφdef
  have e1 : EqOn φ φ₁ (Icc u w) := fun t ht => by simp [hφdef, ht.2]
  have e2 : EqOn φ φ₂ (Icc w v) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · simp [hφdef, ← h, hmatch]
    · simp [hφdef, not_le.2 h]
  have d1 : ∀ t ∈ Icc u w, HasDerivWithinAt φ (f t (φ t)) (Icc u w) t := by
    intro t ht
    have h := (h1 t ht).congr (fun y hy => e1 hy) (e1 ht)
    rwa [e1 ht]
  have d2 : ∀ t ∈ Icc w v, HasDerivWithinAt φ (f t (φ t)) (Icc w v) t := by
    intro t ht
    have h := (h2 t ht).congr (fun y hy => e2 hy) (e2 ht)
    rwa [e2 ht]
  refine ⟨φ, e1, e2, ?_⟩
  intro t ht
  rcases lt_trichotomy t w with h | h | h
  · refine (d1 t ⟨ht.1, h.le⟩).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds h))
      (fun y hy => ⟨hy.1.1, hy.2.le⟩)
  · subst h
    have := (d1 t ⟨ht.1, le_rfl⟩).union (d2 t ⟨le_rfl, ht.2⟩)
    rwa [Icc_union_Icc_eq_Icc huw hwv] at this
  · refine (d2 t ⟨h.le, ht.2⟩).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds h))
      (fun y hy => ⟨hy.2.le, hy.1.2⟩)

/-- **Chaining to the right.** Any right endpoint `v ∈ I` at distance at most `n` steps from
`t₀` is reached. -/
theorem exists_sol_right [CompleteSpace E]
    {f : ℝ → E → E} {I : Set ℝ} {c : ℝ} (hc : 0 < c) (hIconv : Convex ℝ I)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) (I ×ˢ (univ : Set E)))
    (hlip : ∀ t ∈ I, ∀ x y : E, ‖f t x - f t y‖ ≤ c * ‖x - y‖)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (x₀ : E) {T : ℝ} (hT : 0 < T) (hTc : c * T ≤ 1 / 2) :
    ∀ n : ℕ, ∀ v ∈ I, t₀ ≤ v → v - t₀ ≤ n * T →
      ∃ φ : ℝ → E, φ t₀ = x₀ ∧
        ∀ t ∈ Icc t₀ v, HasDerivWithinAt φ (f t (φ t)) (Icc t₀ v) t := by
  have hIcc : ∀ p ∈ I, ∀ q ∈ I, Icc p q ⊆ I := fun p hp q hq => hIconv.ordConnected.out hp hq
  intro n
  induction n with
  | zero =>
    intro v _ htv hlen
    have hv0 : v = t₀ := by
      simp only [Nat.cast_zero, zero_mul] at hlen
      linarith
    subst hv0
    exact exists_sol_short hc hcont hlip
      (by rw [Set.Icc_self]; simpa using ht₀) ⟨le_rfl, le_rfl⟩ (by norm_num) x₀
  | succ n ih =>
    intro v hv htv hlen
    by_cases hcase : v - t₀ ≤ n * T
    · exact ih v hv htv hcase
    push Not at hcase
    have hnT : (0 : ℝ) ≤ n * T := by positivity
    set w : ℝ := t₀ + n * T with hwdef
    have hw1 : t₀ ≤ w := by simp [hwdef]; linarith
    have hw2 : w ≤ v := by simp [hwdef]; linarith
    have hwI : w ∈ I := hIcc t₀ ht₀ v hv ⟨hw1, hw2⟩
    obtain ⟨φ₁, h₁₀, h₁⟩ := ih w hwI hw1 (by simp [hwdef])
    have hlenv : v - w ≤ T := by
      have : ((n : ℝ) + 1) * T = n * T + T := by ring
      simp only [hwdef]
      push_cast at hlen
      linarith
    obtain ⟨φ₂, h₂₀, h₂⟩ := exists_sol_short hc hcont hlip (u := w) (v := v) (t₁ := w)
      (hIcc w hwI v hv) ⟨le_rfl, hw2⟩
      (by nlinarith) (φ₁ w)
    obtain ⟨φ, e1, _, hd⟩ := exists_glue hw1 hw2 h₁ h₂ h₂₀
    exact ⟨φ, by rw [e1 ⟨le_rfl, hw1⟩, h₁₀], hd⟩

/-- **Chaining to the left.** -/
theorem exists_sol_left [CompleteSpace E]
    {f : ℝ → E → E} {I : Set ℝ} {c : ℝ} (hc : 0 < c) (hIconv : Convex ℝ I)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) (I ×ˢ (univ : Set E)))
    (hlip : ∀ t ∈ I, ∀ x y : E, ‖f t x - f t y‖ ≤ c * ‖x - y‖)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (x₀ : E) {T : ℝ} (hT : 0 < T) (hTc : c * T ≤ 1 / 2) :
    ∀ n : ℕ, ∀ u ∈ I, u ≤ t₀ → t₀ - u ≤ n * T →
      ∃ φ : ℝ → E, φ t₀ = x₀ ∧
        ∀ t ∈ Icc u t₀, HasDerivWithinAt φ (f t (φ t)) (Icc u t₀) t := by
  have hIcc : ∀ p ∈ I, ∀ q ∈ I, Icc p q ⊆ I := fun p hp q hq => hIconv.ordConnected.out hp hq
  intro n
  induction n with
  | zero =>
    intro u _ hut hlen
    have hu0 : u = t₀ := by
      simp only [Nat.cast_zero, zero_mul] at hlen
      linarith
    subst hu0
    exact exists_sol_short hc hcont hlip
      (by rw [Set.Icc_self]; simpa using ht₀) ⟨le_rfl, le_rfl⟩ (by norm_num) x₀
  | succ n ih =>
    intro u hu hut hlen
    by_cases hcase : t₀ - u ≤ n * T
    · exact ih u hu hut hcase
    push Not at hcase
    have hnT : (0 : ℝ) ≤ n * T := by positivity
    set w : ℝ := t₀ - n * T with hwdef
    have hw2 : w ≤ t₀ := by simp [hwdef]; linarith
    have hw1 : u ≤ w := by simp [hwdef]; linarith
    have hwI : w ∈ I := hIcc u hu t₀ ht₀ ⟨hw1, hw2⟩
    obtain ⟨φ₁, h₁₀, h₁⟩ := ih w hwI hw2 (by simp [hwdef])
    have hlenu : w - u ≤ T := by
      simp only [hwdef]
      push_cast at hlen
      linarith
    obtain ⟨φ₂, h₂₀, h₂⟩ := exists_sol_short hc hcont hlip (u := u) (v := w) (t₁ := w)
      (hIcc u hu w hwI) ⟨hw1, le_rfl⟩
      (by nlinarith) (φ₁ w)
    obtain ⟨φ, _, e2, hd⟩ := exists_glue hw1 hw2 h₂ h₁ h₂₀.symm
    exact ⟨φ, by rw [e2 ⟨hw2, le_rfl⟩, h₁₀], hd⟩

/-- **Existence on any compact subinterval of `I` containing `t₀`.** -/
theorem exists_sol_Icc [CompleteSpace E]
    {f : ℝ → E → E} {I : Set ℝ} {c : ℝ} (hc : 0 < c) (hIconv : Convex ℝ I)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) (I ×ˢ (univ : Set E)))
    (hlip : ∀ t ∈ I, ∀ x y : E, ‖f t x - f t y‖ ≤ c * ‖x - y‖)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (x₀ : E) {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I)
    (hut : u ≤ t₀) (htv : t₀ ≤ v) :
    ∃ φ : ℝ → E, φ t₀ = x₀ ∧ ∀ t ∈ Icc u v, HasDerivWithinAt φ (f t (φ t)) (Icc u v) t := by
  set T : ℝ := 1 / (2 * c) with hTdef
  have hT : 0 < T := by rw [hTdef]; positivity
  have hTc : c * T ≤ 1 / 2 := by
    rw [hTdef]
    field_simp
    linarith
  obtain ⟨n, hn⟩ := exists_nat_ge ((v - t₀) / T)
  obtain ⟨m, hm⟩ := exists_nat_ge ((t₀ - u) / T)
  obtain ⟨φ₂, h₂₀, h₂⟩ := exists_sol_right hc hIconv hcont hlip ht₀ x₀ hT hTc n v hv htv
    ((div_le_iff₀ hT).mp hn)
  obtain ⟨φ₁, h₁₀, h₁⟩ := exists_sol_left hc hIconv hcont hlip ht₀ x₀ hT hTc m u hu hut
    ((div_le_iff₀ hT).mp hm)
  obtain ⟨φ, e1, _, hd⟩ := exists_glue hut htv h₁ h₂ (by rw [h₂₀, h₁₀])
  exact ⟨φ, by rw [e1 ⟨hut, le_rfl⟩, h₁₀], hd⟩

/-- **Uniqueness on a convex subset.** Two solutions on a convex `S ⊆ I` that agree at one
point of `S` agree on `S`; this is Grönwall's inequality. -/
theorem eqOn_of_convex
    {f : ℝ → E → E} {I : Set ℝ} {c : ℝ} (hc : 0 < c)
    (hlip : ∀ t ∈ I, ∀ x y : E, ‖f t x - f t y‖ ≤ c * ‖x - y‖)
    {S : Set ℝ} (hSconv : Convex ℝ S) (hSI : S ⊆ I) {s₀ : ℝ} (hs₀ : s₀ ∈ S) {φ ψ : ℝ → E}
    (hφ : ∀ t ∈ S, HasDerivWithinAt φ (f t (φ t)) S t)
    (hψ : ∀ t ∈ S, HasDerivWithinAt ψ (f t (ψ t)) S t)
    (heq : φ s₀ = ψ s₀) : EqOn φ ψ S := by
  obtain ⟨cn, hcn⟩ : ∃ cn : NNReal, (cn : ℝ) = c := ⟨c.toNNReal, Real.coe_toNNReal c hc.le⟩
  have hSIcc : ∀ p ∈ S, ∀ q ∈ S, Icc p q ⊆ S := fun p hp q hq => hSconv.ordConnected.out hp hq
  have hlipS : ∀ r ∈ S, LipschitzOnWith cn (f r) (univ : Set E) := by
    intro r hr
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [dist_eq_norm, dist_eq_norm, hcn]
    exact hlip r (hSI hr) x y
  intro t ht
  rcases le_total s₀ t with h | h
  · have hJ : Icc s₀ t ⊆ S := hSIcc s₀ hs₀ t ht
    have hnhds : ∀ r ∈ Ico s₀ t, Icc s₀ t ∈ nhdsWithin r (Ici r) := by
      intro r hr
      exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds hr.2))
        (fun y hy => ⟨hr.1.trans hy.1, hy.2.le⟩)
    refine ODE_solution_unique_of_mem_Icc_right (v := f) (s := fun _ => (univ : Set E))
      (K := cn) (a := s₀) (b := t)
      (fun r hr => hlipS r (hJ (Ico_subset_Icc_self hr)))
      (fun r hr => ((hφ r (hJ hr)).mono hJ).continuousWithinAt)
      (fun r hr => ((hφ r (hJ (Ico_subset_Icc_self hr))).mono hJ).mono_of_mem_nhdsWithin
        (hnhds r hr))
      (fun r _ => mem_univ _)
      (fun r hr => ((hψ r (hJ hr)).mono hJ).continuousWithinAt)
      (fun r hr => ((hψ r (hJ (Ico_subset_Icc_self hr))).mono hJ).mono_of_mem_nhdsWithin
        (hnhds r hr))
      (fun r _ => mem_univ _) heq ⟨h, le_rfl⟩
  · have hJ : Icc t s₀ ⊆ S := hSIcc t ht s₀ hs₀
    have hnhds : ∀ r ∈ Ioc t s₀, Icc t s₀ ∈ nhdsWithin r (Iic r) := by
      intro r hr
      exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds hr.1))
        (fun y hy => ⟨hy.2.le, hy.1.trans hr.2⟩)
    refine ODE_solution_unique_of_mem_Icc_left (v := f) (s := fun _ => (univ : Set E))
      (K := cn) (a := t) (b := s₀)
      (fun r hr => hlipS r (hJ (Ioc_subset_Icc_self hr)))
      (fun r hr => ((hφ r (hJ hr)).mono hJ).continuousWithinAt)
      (fun r hr => ((hφ r (hJ (Ioc_subset_Icc_self hr))).mono hJ).mono_of_mem_nhdsWithin
        (hnhds r hr))
      (fun r _ => mem_univ _)
      (fun r hr => ((hψ r (hJ hr)).mono hJ).continuousWithinAt)
      (fun r hr => ((hψ r (hJ (Ioc_subset_Icc_self hr))).mono hJ).mono_of_mem_nhdsWithin
        (hnhds r hr))
      (fun r _ => mem_univ _) heq ⟨le_rfl, h⟩

/-- For every `t` in a nondegenerate interval `I` there is a compact subinterval `[p,q] ⊆ I`
containing both `t` and `t₀` which is a neighbourhood of `t` relative to `I`. -/
theorem exists_good_pair {I : Set ℝ} (hIne : (interior I).Nonempty)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) {t : ℝ} (ht : t ∈ I) :
    ∃ p q : ℝ, p ∈ I ∧ q ∈ I ∧ p ≤ t ∧ p ≤ t₀ ∧ t ≤ q ∧ t₀ ≤ q ∧ Icc p q ∈ nhdsWithin t I := by
  have hmin : ∀ x ∈ I, ∀ y ∈ I, min x y ∈ I := by
    intro x hx y hy
    rcases le_total x y with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hmax : ∀ x ∈ I, ∀ y ∈ I, max x y ∈ I := by
    intro x hx y hy
    rcases le_total x y with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  by_cases hleft : ∃ s ∈ I, s < t
  · obtain ⟨s₁, hs₁I, hs₁⟩ := hleft
    have hp : min s₁ t₀ < t := lt_of_le_of_lt (min_le_left _ _) hs₁
    by_cases hright : ∃ s ∈ I, t < s
    · obtain ⟨s₂, hs₂I, hs₂⟩ := hright
      have hq : t < max s₂ t₀ := lt_of_lt_of_le hs₂ (le_max_left _ _)
      exact ⟨min s₁ t₀, max s₂ t₀, hmin s₁ hs₁I t₀ ht₀, hmax s₂ hs₂I t₀ ht₀, hp.le,
        min_le_right _ _, hq.le, le_max_right _ _,
        nhdsWithin_le_nhds (Icc_mem_nhds hp hq)⟩
    · push Not at hright
      refine ⟨min s₁ t₀, t, hmin s₁ hs₁I t₀ ht₀, ht, hp.le, min_le_right _ _, le_rfl,
        hright t₀ ht₀, ?_⟩
      exact Filter.mem_of_superset (inter_mem_nhdsWithin I (Ioi_mem_nhds hp))
        (fun y hy => ⟨hy.2.le, hright y hy.1⟩)
  · push Not at hleft
    by_cases hright : ∃ s ∈ I, t < s
    · obtain ⟨s₂, hs₂I, hs₂⟩ := hright
      have hq : t < max s₂ t₀ := lt_of_lt_of_le hs₂ (le_max_left _ _)
      refine ⟨t, max s₂ t₀, ht, hmax s₂ hs₂I t₀ ht₀, le_rfl, hleft t₀ ht₀, hq.le,
        le_max_right _ _, ?_⟩
      exact Filter.mem_of_superset (inter_mem_nhdsWithin I (Iio_mem_nhds hq))
        (fun y hy => ⟨hleft y hy.1, hy.2.le⟩)
    · exfalso
      push Not at hright
      have hsub : I ⊆ {t} := fun s hs => le_antisymm (hright s hs) (hleft s hs)
      obtain ⟨z, hz⟩ := hIne
      have : z ∈ interior ({t} : Set ℝ) := interior_mono hsub hz
      rw [interior_singleton] at this
      exact this

end GlobalPicardAux

/-- **Corolário 2.1.3.** -/
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (I : Set ℝ) (hIconv : Convex ℝ I) (hIne : (interior I).Nonempty)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (x₀ : E) (f : ℝ → E → E) (c : ℝ)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) (I ×ˢ (Set.univ : Set E)))
    (hlip : LipschitzInSecondVar (I ×ˢ (Set.univ : Set E)) (fun p : ℝ × E => f p.1 p.2) c) :
    ∃ φ : ℝ → E, IsCauchySolutionOn f (I ×ˢ (Set.univ : Set E)) t₀ x₀ I φ ∧
      ∀ ψ : ℝ → E, IsCauchySolutionOn f (I ×ˢ (Set.univ : Set E)) t₀ x₀ I ψ →
        Set.EqOn φ ψ I := by
  classical
  obtain ⟨hc, hlip'⟩ := hlip
  have hlipf : ∀ t ∈ I, ∀ x y : E, ‖f t x - f t y‖ ≤ c * ‖x - y‖ := fun t ht x y =>
    hlip' t x y ⟨ht, mem_univ _⟩ ⟨ht, mem_univ _⟩
  have hIcc : ∀ p ∈ I, ∀ q ∈ I, Icc p q ⊆ I := fun p hp q hq => hIconv.ordConnected.out hp hq
  -- a chosen solution on every admissible compact subinterval
  have hex : ∀ p q : ℝ, (p ∈ I ∧ q ∈ I ∧ p ≤ t₀ ∧ t₀ ≤ q) →
      ∃ ψ : ℝ → E, ψ t₀ = x₀ ∧ ∀ t ∈ Icc p q, HasDerivWithinAt ψ (f t (ψ t)) (Icc p q) t := by
    rintro p q ⟨hp, hq, hpt, htq⟩
    exact GlobalPicardAux.exists_sol_Icc hc hIconv hcont hlipf ht₀ x₀ hp hq hpt htq
  choose! g hg0 hg using hex
  -- any two chosen solutions agree where both are defined
  have hcoh : ∀ p q p' q' : ℝ, (p ∈ I ∧ q ∈ I ∧ p ≤ t₀ ∧ t₀ ≤ q) →
      (p' ∈ I ∧ q' ∈ I ∧ p' ≤ t₀ ∧ t₀ ≤ q') → ∀ t ∈ Icc p q, t ∈ Icc p' q' →
      g p q t = g p' q' t := by
    intro p q p' q' h h' t ht ht'
    have hs1 : Icc (max p p') (min q q') ⊆ Icc p q :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hs2 : Icc (max p p') (min q q') ⊆ Icc p' q' :=
      Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    have hmem₀ : t₀ ∈ Icc (max p p') (min q q') :=
      ⟨max_le h.2.2.1 h'.2.2.1, le_min h.2.2.2 h'.2.2.2⟩
    refine GlobalPicardAux.eqOn_of_convex hc hlipf (convex_Icc _ _)
      (hs1.trans (hIcc p h.1 q h.2.1)) hmem₀
      (fun r hr => (hg p q h r (hs1 hr)).mono hs1)
      (fun r hr => (hg p' q' h' r (hs2 hr)).mono hs2)
      (by rw [hg0 p q h, hg0 p' q' h']) ?_
    exact ⟨max_le ht.1 ht'.1, le_min ht.2 ht'.2⟩
  -- for every `t ∈ I`, a compact subinterval around it
  choose! lo hi hloI hhiI hlot hlot₀ hthi ht₀hi hnhds using
    fun t (ht : t ∈ I) => GlobalPicardAux.exists_good_pair hIne ht₀ ht
  have hP : ∀ t ∈ I, (lo t ∈ I ∧ hi t ∈ I ∧ lo t ≤ t₀ ∧ t₀ ≤ hi t) := fun t ht =>
    ⟨hloI t ht, hhiI t ht, hlot₀ t ht, ht₀hi t ht⟩
  have hmem : ∀ t ∈ I, t ∈ Icc (lo t) (hi t) := fun t ht => ⟨hlot t ht, hthi t ht⟩
  set φ : ℝ → E := fun t => g (lo t) (hi t) t with hφdef
  have hagree : ∀ t ∈ I, ∀ r ∈ Icc (lo t) (hi t), φ r = g (lo t) (hi t) r := by
    intro t ht r hr
    have hrI : r ∈ I := hIcc _ (hloI t ht) _ (hhiI t ht) hr
    exact hcoh (lo r) (hi r) (lo t) (hi t) (hP r hrI) (hP t ht) r (hmem r hrI) hr
  have hφ₀ : φ t₀ = x₀ := hg0 (lo t₀) (hi t₀) (hP t₀ ht₀)
  have hderiv : ∀ t ∈ I, HasDerivWithinAt φ (f t (φ t)) I t := by
    intro t ht
    have hd := hg (lo t) (hi t) (hP t ht) t (hmem t ht)
    have heq := hagree t ht
    have hd2 : HasDerivWithinAt φ (f t (g (lo t) (hi t) t)) (Icc (lo t) (hi t)) t :=
      hd.congr (fun y hy => heq y hy) (heq t (hmem t ht))
    rw [← heq t (hmem t ht)] at hd2
    exact hd2.mono_of_mem_nhdsWithin (hnhds t ht)
  refine ⟨φ, ⟨ht₀, hφ₀, fun t ht => ⟨ht, mem_univ _⟩, hderiv⟩, ?_⟩
  rintro ψ ⟨-, hψ₀, -, hψd⟩
  exact GlobalPicardAux.eqOn_of_convex hc hlipf hIconv (subset_refl I) ht₀ hderiv hψd (by rw [hφ₀, hψ₀])
