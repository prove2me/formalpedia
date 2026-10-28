-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:29.113994+00:00
-- url     : https://prove2.me/submissions/9824959e-fe32-485b-af3e-78e1702f1929

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Inverse
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_mem_closure_range_of_inner_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_le_of_gap_readable

section
noncomputable section
open scoped LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- The domain of `adjointComp T`, in the form `LinearPMap.domRestrict` produces it. -/
theorem FunctionalInequalities.Analysis.Semigroup.adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) :
    (adjointComp T).domain = adjointCompDomain T ⊓ T.domain := rfl
end
end
end

section
noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
omit [CompleteSpace H₁] in
include hd in
/-- On the operator domain, `A y = 0` exactly when `T y = 0`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff (y : (adjointComp T).domain) :
    adjointComp T y = 0 ↔ T ⟨y, y.2.2⟩ = 0 := by
  constructor
  · intro hA
    have hnorm2 : ‖T ⟨(y : H₀), y.2.2⟩‖ ^ 2 = 0 := by
      rw [← inner_adjointComp_self hd y, hA, inner_zero_left]
    have hnorm : ‖T ⟨(y : H₀), y.2.2⟩‖ = 0 := by
      nlinarith [hnorm2]
    exact norm_eq_zero.mp hnorm
  · intro h
    refine hd.eq_zero_of_inner_left ℝ (fun z hz => ?_)
    rw [inner_adjointComp hd y hz, h, inner_zero_left]
omit [CompleteSpace H₁] in
include hd in
/-- A form-domain vector killed by `T` lies in the operator domain and is killed by `A`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_of_map_eq_zero (x : T.domain) (hx : T x = 0) :
    ∃ h : (x : H₀) ∈ (adjointComp T).domain, adjointComp T ⟨x, h⟩ = 0 := by
  have hmem : (x : H₀) ∈ (adjointComp T).domain := by
    rw [adjointComp_domain]
    refine ⟨mem_adjointCompDomain.2 ⟨x.2, ?_⟩, x.2⟩
    have hTx : T ⟨(x : H₀), x.2⟩ = T x := rfl
    rw [hTx, hx]
    exact Submodule.zero_mem _
  refine ⟨hmem, ?_⟩
  apply (adjointComp_eq_zero_iff T hd ⟨x, hmem⟩).2
  show T ⟨(x : H₀), _⟩ = 0
  exact hx
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
open Filter Topology Set
omit [CompleteSpace H₁] in
include hT hd in
private theorem FunctionalInequalities.Analysis.Semigroup.Generated.exists_orthogonal_ker_adjointComp_eq (y : (adjointComp T).domain) :
    ∃ v : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(v : H₀), (k : H₀)⟫ = 0) ∧
        adjointComp T v = adjointComp T y := by
  classical
  let K : Submodule ℝ H₀ :=
    T.graph.comap
      ((LinearMap.id : H₀ →ₗ[ℝ] H₀).prod (0 : H₀ →ₗ[ℝ] H₁))
  have hK (x : H₀) :
      x ∈ K ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = 0 := by
    change (x, (0 : H₁)) ∈ T.graph ↔ _
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨a, ha, hTa⟩
      change (a : H₀) = x at ha
      change T a = 0 at hTa
      subst x
      exact ⟨a.2, hTa⟩
    · rintro ⟨hx, hTx⟩
      exact ⟨⟨x, hx⟩, rfl, hTx⟩
  have hKclosed : IsClosed (K : Set H₀) := by
    change IsClosed
      ((fun x : H₀ => (x, (0 : H₁))) ⁻¹' (T.graph : Set (H₀ × H₁)))
    exact hT.preimage (continuous_id.prodMk continuous_const)
  let _ : CompleteSpace K := hKclosed.completeSpace_coe
  let p : H₀ := K.starProjection (y : H₀)
  obtain ⟨hp, hTp⟩ :=
    (hK p).1 (K.starProjection_apply_mem (y : H₀))
  obtain ⟨hpA, hAp⟩ :=
    exists_mem_adjointComp_domain_of_map_eq_zero
      T hd (⟨p, hp⟩ : T.domain) hTp
  let v : (adjointComp T).domain := y - ⟨p, hpA⟩
  refine ⟨v, ?_, ?_⟩
  · intro k hk
    exact
      K.starProjection_inner_eq_zero (y : H₀) (k : H₀)
        ((hK k).2 ⟨k.2, hk⟩)
  · change adjointComp T (y - ⟨p, hpA⟩) = adjointComp T y
    rw [LinearPMap.map_sub, hAp, sub_zero]
include hT hd in
/-- Existence: under the gap inequality, every `g ⊥ ker T` is `A u` for some `u ⊥ ker T` in the
operator domain. -/
theorem solution {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (g : H₀) (hg : ∀ k : T.domain, T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    ∃ u : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) ∧ FunctionalInequalities.Analysis.Semigroup.adjointComp T u = g := by
  classical
  have hgcl :
      g ∈ closure
        (Set.range fun y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain => FunctionalInequalities.Analysis.Semigroup.adjointComp T y) := by
    apply FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_readable T hT hd g
    intro k hk
    exact
      hg ⟨(k : H₀), k.2.2⟩
        ((FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff T hd k).1 hk)
  obtain ⟨a, ha, halim⟩ := mem_closure_iff_seq_limit.1 hgcl
  have hrep (n : ℕ) :
      ∃ u : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain,
        (∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) ∧
          FunctionalInequalities.Analysis.Semigroup.adjointComp T u = a n := by
    obtain ⟨y, hy⟩ := ha n
    obtain ⟨v, hv, hvA⟩ := FunctionalInequalities.Analysis.Semigroup.Generated.exists_orthogonal_ker_adjointComp_eq T hT hd y
    exact ⟨v, hv, hvA.trans hy⟩
  choose u hu hAu using hrep
  have hbound (n m : ℕ) :
      ‖(u n : H₀) - (u m : H₀)‖ ≤
        max C 0 * ‖a n - a m‖ := by
    have horth : ∀ k : T.domain, T k = 0 →
        ⟪((u n - u m : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) : H₀), (k : H₀)⟫ = 0 := by
      intro k hk
      change ⟪(u n : H₀) - (u m : H₀), (k : H₀)⟫ = 0
      rw [inner_sub_left, hu n k hk, hu m k hk, sub_self]
    have hnorm :=
      (FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_readable T hd hgap (u n - u m) horth).1
    change
      ‖(u n : H₀) - (u m : H₀)‖ ≤
        C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T (u n - u m)‖ at hnorm
    rw [LinearPMap.map_sub, hAu n, hAu m] at hnorm
    exact
      hnorm.trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))
  have hc : CauchySeq (fun n => (u n : H₀)) := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    have hε' : 0 < ε / (max C 0 + 1) :=
      div_pos hε (by positivity)
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.1 halim.cauchySeq
        (ε / (max C 0 + 1)) hε'
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hnm : ‖a n - a m‖ < ε / (max C 0 + 1) := by
      simpa only [dist_eq_norm] using hN n hn m hm
    have hmul : ‖a n - a m‖ * (max C 0 + 1) < ε :=
      (lt_div_iff₀ (by positivity)).1 hnm
    rw [dist_eq_norm]
    have hnonneg : 0 ≤ ‖a n - a m‖ := norm_nonneg _
    linarith [hbound n m]
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hAclosed : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).IsClosed :=
    (FunctionalInequalities.Analysis.Semigroup.isSelfAdjoint_adjointComp T hT hd).isClosed
  have hgraph : (x, g) ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T).graph := by
    apply hAclosed.mem_of_tendsto (hx.prodMk_nhds halim)
    exact Eventually.of_forall fun n => by
      rw [← hAu n]
      exact (FunctionalInequalities.Analysis.Semigroup.adjointComp T).mem_graph (u n)
  obtain ⟨v, hvx, hvg⟩ :=
    (LinearPMap.mem_graph_iff (FunctionalInequalities.Analysis.Semigroup.adjointComp T)).1 hgraph
  refine ⟨v, ?_, hvg⟩
  intro k hk
  have hinner :
      Tendsto (fun n => ⟪(u n : H₀), (k : H₀)⟫)
        atTop (𝓝 ⟪x, (k : H₀)⟫) :=
    hx.inner tendsto_const_nhds
  have hzero :
      Tendsto (fun n => ⟪(u n : H₀), (k : H₀)⟫)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [hu _ k hk] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  rw [hvx]
  exact tendsto_nhds_unique hinner hzero
