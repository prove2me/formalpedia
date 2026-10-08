-- Prove2me | solution 1 for Balinski61.Connectivity.convexHull_vertices_not_in_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:12:29.396729+00:00
-- url     : https://prove2.me/submissions/1e0a02cc-e422-41eb-8730-d84579c2e71c

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace


namespace Balinski61.Connectivity

section
variable {n m : ℕ} {a : Fin m → EuclideanSpace ℝ (Fin n)} {b : Fin m → ℝ}

lemma bal_convex : Convex ℝ (Hirsch.Hpoly a b) := by
  intro x hx y hy s t hs ht hst i
  have h1 := hx i
  have h2 := hy i
  simp only [inner_add_right, inner_smul_right]
  have e1 := mul_le_mul_of_nonneg_left h1 hs
  have e2 := mul_le_mul_of_nonneg_left h2 ht
  have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

lemma bal_closed : IsClosed (Hirsch.Hpoly a b) := by
  have : Hirsch.Hpoly a b = ⋂ i, {x | ⟪a i, x⟫ ≤ b i} := by
    ext x; simp [Hirsch.Hpoly]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

lemma bal_bounded (hS : StandingAssumptions a b) : Bornology.IsBounded (Hirsch.Hpoly a b) := by
  by_cases hsub : Subsingleton (EuclideanSpace ℝ (Fin n))
  · exact (Set.toFinite _).isBounded
  · have hne : ∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 := by
      by_contra h; push_neg at h; exact hsub ⟨fun x y => by rw [h x, h y]⟩
    obtain ⟨x1, hx1⟩ := hne
    have hm : m ≠ 0 := by
      rintro rfl
      exact hx1 (hS.only_zero x1 (fun i => i.elim0))
    haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪a i, x⟫)
    have fcont : Continuous f := by
      apply Continuous.finset_sup'_apply
      intro i _; fun_prop
    have hsph : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_sphere _ _
    have hsne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
      ⟨(‖x1‖⁻¹) • x1, by simp [norm_smul, hx1]⟩
    obtain ⟨x0, hx0, hmin⟩ := hsph.exists_isMinOn hsne fcont.continuousOn
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    have hpos : 0 < f x0 := by
      by_contra hle; push_neg at hle
      have : ∀ i, ⟪a i, x0⟫ ≤ 0 := fun i =>
        le_trans (Finset.le_sup' (fun i => ⟪a i, x0⟫) (Finset.mem_univ i)) hle
      have := hS.only_zero x0 this
      rw [this] at hx0n; simp at hx0n
    set δ := f x0 with hδ
    set B : ℝ := Finset.univ.sup' Finset.univ_nonempty b with hB
    rw [isBounded_iff_forall_norm_le]
    refine ⟨|B| / δ, fun x hx => ?_⟩
    by_cases hx0' : x = 0
    · subst hx0'
      simp only [norm_zero]
      positivity
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0'
      set u : EuclideanSpace ℝ (Fin n) := (‖x‖⁻¹) • x with hu
      have hun : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simp [hu, norm_smul, hxpos.ne']
      have hfu : δ ≤ f u := hmin hun
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin m)) (fun i => ⟪a i, u⟫)
      have hxu : x = ‖x‖ • u := by
        simp [hu, smul_smul, hxpos.ne']
      have h1 : ⟪a i, x⟫ = ‖x‖ * ⟪a i, u⟫ := by
        conv_lhs => rw [hxu]
        rw [inner_smul_right]
      have h2 : δ ≤ ⟪a i, u⟫ := by
        have : f u = ⟪a i, u⟫ := hi
        linarith
      have h3 : ⟪a i, x⟫ ≤ b i := hx i
      have h4 : b i ≤ B := Finset.le_sup' b (Finset.mem_univ i)
      have h5 : ‖x‖ * δ ≤ B := by
        have := mul_le_mul_of_nonneg_left h2 hxpos.le
        linarith
      rw [le_div_iff₀ hpos]
      have := le_abs_self B
      linarith

lemma bal_small_step (x w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Hirsch.Hpoly a b)
    (hw : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, w⟫ = 0) :
    ∃ ε : ℝ, ε > 0 ∧ x + ε • w ∈ Hirsch.Hpoly a b ∧ x - ε • w ∈ Hirsch.Hpoly a b := by
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ i, ⟪a i, x + t • w⟫ ≤ b i ∧ ⟪a i, x - t • w⟫ ≤ b i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · have := hw i hi
      refine Filter.Eventually.of_forall fun t => ?_
      simp [inner_add_right, inner_sub_right, inner_smul_right, this, hi]
    · have hlt : ⟪a i, x⟫ < b i := lt_of_le_of_ne (hx i) hi
      have hc1 : Continuous fun t : ℝ => ⟪a i, x + t • w⟫ := by fun_prop
      have hc2 : Continuous fun t : ℝ => ⟪a i, x - t • w⟫ := by fun_prop
      have e1 : ∀ᶠ t in nhds (0:ℝ), ⟪a i, x + t • w⟫ < b i :=
        hc1.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
      have e2 : ∀ᶠ t in nhds (0:ℝ), ⟪a i, x - t • w⟫ < b i :=
        hc2.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
      filter_upwards [e1, e2] with t h1 h2 using ⟨h1.le, h2.le⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have key : ∀ t : ℝ, |t| < ε → ∀ i, ⟪a i, x + t • w⟫ ≤ b i ∧ ⟪a i, x - t • w⟫ ≤ b i :=
    fun t ht => hball (by simpa [Real.dist_eq] using ht)
  have hk := key (ε/2) (by rw [abs_of_pos (by positivity)]; linarith)
  exact ⟨ε/2, by positivity, fun i => (hk i).1, fun i => (hk i).2⟩

lemma bal_ext_tight (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, w⟫ = 0) : w = 0 := by
  obtain ⟨hxS, hext⟩ := mem_extremePoints.mp hx
  obtain ⟨ε, hε, h1, h2⟩ := bal_small_step x w hxS hw
  have hmem : x ∈ openSegment ℝ (x + ε • w) (x - ε • w) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have := (hext _ h1 _ h2 hmem).1
  have h3 : ε • w = 0 := by simpa using this
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h hε.ne'
  · exact h

lemma bal_ext_finite (hS : StandingAssumptions a b) :
    (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Finite := by
  classical
  let T : EuclideanSpace ℝ (Fin n) → Set (Fin m) := fun x => {i | ⟪a i, x⟫ = b i}
  have hinj : Set.InjOn T (Set.extremePoints ℝ (Hirsch.Hpoly a b)) := by
    intro x hx y hy hT
    have hxy : x - y = 0 := by
      apply bal_ext_tight x hx
      intro i hi
      have hi' : i ∈ T y := by rw [← hT]; exact hi
      have hi'' : ⟪a i, y⟫ = b i := hi'
      simp [inner_sub_right, hi, hi'']
    exact sub_eq_zero.mp hxy
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

lemma bal_hull (hS : StandingAssumptions a b) :
    convexHull ℝ (Set.extremePoints ℝ (Hirsch.Hpoly a b)) = Hirsch.Hpoly a b := by
  have hcomp : IsCompact (Hirsch.Hpoly a b) :=
    Metric.isCompact_of_isClosed_isBounded bal_closed (bal_bounded hS)
  have := closure_convexHull_extremePoints hcomp bal_convex
  have hfin := bal_ext_finite hS
  rw [(hfin.isCompact_convexHull ℝ).isClosed.closure_eq] at this
  exact this

lemma bal_not_hyperplane (hS : StandingAssumptions a b) (c : EuclideanSpace ℝ (Fin n)) (d : ℝ)
    (hc : c ≠ 0) : ∃ x ∈ Hirsch.Hpoly a b, ⟪c, x⟫ ≠ d := by
  obtain ⟨x0, hx0⟩ := hS.strict_point
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ i, ⟪a i, x0 + t • c⟫ ≤ b i := by
    rw [Filter.eventually_all]
    intro i
    have hc1 : Continuous fun t : ℝ => ⟪a i, x0 + t • c⟫ := by fun_prop
    have e1 : ∀ᶠ t in nhds (0:ℝ), ⟪a i, x0 + t • c⟫ < b i :=
      hc1.continuousAt.eventually_lt continuousAt_const (by simpa using hx0 i)
    exact e1.mono fun t h => h.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have key : ∀ t : ℝ, |t| < ε → ∀ i, ⟪a i, x0 + t • c⟫ ≤ b i :=
    fun t ht => hball (by simpa [Real.dist_eq] using ht)
  have hp : x0 + (ε/2) • c ∈ Hirsch.Hpoly a b :=
    key (ε/2) (by rw [abs_of_pos (by positivity)]; linarith)
  have hq : x0 + (-(ε/2)) • c ∈ Hirsch.Hpoly a b :=
    key (-(ε/2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  by_contra hcon
  push_neg at hcon
  have e1 := hcon _ hp
  have e2 := hcon _ hq
  simp only [inner_add_right, inner_smul_right] at e1 e2
  have : ε * ⟪c, c⟫ = 0 := by linarith
  have hcc : 0 < ⟪c, c⟫ := real_inner_self_pos.mpr hc
  have := mul_pos hε hcc
  linarith

lemma bal_nonempty (hS : StandingAssumptions a b) : (Hirsch.Hpoly a b).Nonempty := by
  obtain ⟨x0, hx0⟩ := hS.strict_point
  exact ⟨x0, fun i => (hx0 i).le⟩

lemma bal_card (hS : StandingAssumptions a b) :
    (n : ℕ∞) + 1 ≤ (Set.extremePoints ℝ (Hirsch.Hpoly a b)).encard := by
  classical
  by_contra hlt
  push_neg at hlt
  have hfin := bal_ext_finite hS
  set E := hfin.toFinset with hE
  have hcard : (E.card : ℕ∞) = (Set.extremePoints ℝ (Hirsch.Hpoly a b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard, hE, Set.Finite.coe_toFinset]
  rw [← hcard] at hlt
  have hk : E.card ≤ n := by
    have : E.card < n + 1 := by exact_mod_cast hlt
    omega
  have hhull := bal_hull hS
  have hEne : E.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := bal_nonempty hS
    rw [← hhull, show Set.extremePoints ℝ (Hirsch.Hpoly a b) = (E : Set _) by simp [hE], h] at hx
    simp at hx
  obtain ⟨e0, he0⟩ := hEne
  let D : Finset (EuclideanSpace ℝ (Fin n)) := (E.erase e0).image (fun e => e - e0)
  let W := Submodule.span ℝ (D : Set (EuclideanSpace ℝ (Fin n)))
  have hW : Module.finrank ℝ W ≤ E.card - 1 := by
    calc Module.finrank ℝ W ≤ D.card := finrank_span_finset_le_card D
      _ ≤ (E.erase e0).card := Finset.card_image_le
      _ = E.card - 1 := Finset.card_erase_of_mem he0
  have hpos : 0 < E.card := Finset.card_pos.mpr ⟨e0, he0⟩
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have horth := Submodule.finrank_add_finrank_orthogonal W
  have hpos2 : 0 < Module.finrank ℝ Wᗮ := by omega
  obtain ⟨c, hcW, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Wᗮ)
    (fun h => by rw [h] at hpos2; simp at hpos2)
  have hall : ∀ e ∈ E, ⟪c, e⟫ = ⟪c, e0⟫ := by
    intro e he
    by_cases hee : e = e0
    · rw [hee]
    · have hmem : e - e0 ∈ W := Submodule.subset_span (by
        simp only [D, Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨e, Finset.mem_erase.mpr ⟨hee, he⟩, rfl⟩)
      have := (Submodule.mem_orthogonal' W c).mp hcW _ hmem
      rw [inner_sub_right] at this
      linarith
  obtain ⟨x, hxS, hxne⟩ := bal_not_hyperplane hS c ⟪c, e0⟫ hc0
  apply hxne
  rw [← hhull] at hxS
  have hsub : (Set.extremePoints ℝ (Hirsch.Hpoly a b)) ⊆ {y | ⟪c, y⟫ = ⟪c, e0⟫} := by
    intro y hy
    have : y ∈ E := by simp [hE, hy]
    exact hall y this
  have hconv : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | ⟪c, y⟫ = ⟪c, e0⟫} := by
    intro y hy z hz s t hs ht hst
    simp only [Set.mem_setOf_eq, inner_add_right, inner_smul_right] at hy hz ⊢
    rw [hy, hz, ← add_mul, hst, one_mul]
  exact convexHull_min hsub hconv hxS

theorem bal_m1_core (hS : StandingAssumptions a b) :
    (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Finite ∧
      convexHull ℝ (Set.extremePoints ℝ (Hirsch.Hpoly a b)) = Hirsch.Hpoly a b ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (d : ℝ), c ≠ 0 →
        ∃ x ∈ Hirsch.Hpoly a b, ⟪c, x⟫ ≠ d :=
  ⟨bal_ext_finite hS, bal_hull hS, fun c d hc => bal_not_hyperplane hS c d hc⟩

theorem bal_m2_core (hS : StandingAssumptions a b) :
    (n : ℕ∞) + 1 ≤ (Set.extremePoints ℝ (Hirsch.Hpoly a b)).encard := bal_card hS
end

end Balinski61.Connectivity

open Balinski61.Connectivity


theorem solution (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) :
    (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Finite ∧
      convexHull ℝ (Set.extremePoints ℝ (Hirsch.Hpoly a b)) = Hirsch.Hpoly a b ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (d : ℝ), c ≠ 0 →
        ∃ x ∈ Hirsch.Hpoly a b, ⟪c, x⟫ ≠ d := by
  exact bal_m1_core hS
