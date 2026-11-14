-- Prove2me | solution 1 for ConformalBoundary.caratheodory_torhorst_exterior
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:04:35.125298+00:00
-- url     : https://prove2.me/submissions/27b047ea-37ed-45c5-926a-2a5276b7f18f

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs
import Theorems.Thm_AhlforsComplexAnalysis_riemann_mapping_theorem
import Theorems.Thm_janiszewski_compact_preconnected_intersection

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
/-- The exterior domain `|w| > 1`. -/
def E : Set ℂ := {w | 1 < ‖w‖}

/-- The outer complementary region of a set `K`. -/
def Om (K : Set ℂ) : Set ℂ :=
  {z | z ∉ K ∧ ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z)}

/-- Facts about the outer region of a nondegenerate curve image. -/
structure OmFacts (K : Set ℂ) : Prop where
  compact : IsCompact K
  nontriv : K.Nontrivial
  isOpen : IsOpen (Om K)
  connected : IsConnected (Om K)
  far : ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → z ∈ Om K
  compl_compact : IsCompact (Om K)ᶜ
  frontier_sub : frontier (Om K) ⊆ K

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
open Set Metric
namespace ConformalBoundary.Dev.CT.PartO
open ConformalBoundary.Dev.CT
/-- The complement of a closed ball in `ℂ` is connected. -/
theorem isConnected_compl_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (closedBall c r)ᶜ := by
  let f : ℝ × ℝ → ℂ := fun p => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  have heq : (closedBall c r)ᶜ = f '' (Ioi r ×ˢ univ) := by
    ext z
    simp only [mem_compl_iff, mem_closedBall, not_le, mem_image, mem_prod, mem_Ioi,
      mem_univ, and_true, Prod.exists, f]
    constructor
    · intro hz
      refine ⟨‖z - c‖, Complex.arg (z - c), by rwa [← dist_eq_norm], ?_⟩
      rw [Complex.norm_mul_exp_arg_mul_I]
      ring
    · rintro ⟨t, θ, ht, rfl⟩
      rw [dist_eq_norm]
      have : c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - c
          = (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by ring
      rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_of_nonneg (hr.trans ht.le)]
      simpa using ht
  rw [heq]
  exact (isConnected_Ioi.prod isConnected_univ).image f hf.continuousOn

/-- A point of the closure of a complementary component, off `K`, lies in that component. -/
theorem mem_comp_of_mem_closure {K : Set ℂ} (hK : IsClosed K) {x y : ℂ} (hy : y ∉ K)
    (hc : y ∈ closure (connectedComponentIn Kᶜ x)) : y ∈ connectedComponentIn Kᶜ x := by
  have ho : IsOpen (connectedComponentIn Kᶜ y) := hK.isOpen_compl.connectedComponentIn
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hc _ ho (mem_connectedComponentIn hy)
  rw [connectedComponentIn_eq hw2, ← connectedComponentIn_eq hw1]
  exact mem_connectedComponentIn hy

theorem compl_closedBall_unbounded (R : ℝ) : ¬ Bornology.IsBounded (closedBall (0 : ℂ) R)ᶜ := by
  intro hb
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  have hmem : ((max R r + 1 : ℝ) : ℂ) ∈ (closedBall (0 : ℂ) R)ᶜ := by
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, Complex.norm_real, not_le]
    exact lt_of_lt_of_le (by linarith [le_max_left R r]) (le_abs_self _)
  have := hr hmem
  simp only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at this
  rw [abs_le] at this
  linarith [le_max_right R r, this.2]

/-- For closed `K` inside `closedBall 0 R`, the outer region is the component of `R + 1`. -/
theorem om_eq {K : Set ℂ} {R : ℝ} (hR : 0 ≤ R) (hKR : K ⊆ closedBall 0 R) :
    Om K = connectedComponentIn Kᶜ ((R + 1 : ℝ) : ℂ) ∧
      (closedBall (0 : ℂ) R)ᶜ ⊆ connectedComponentIn Kᶜ ((R + 1 : ℝ) : ℂ) := by
  set z₀ : ℂ := ((R + 1 : ℝ) : ℂ)
  have hz0 : z₀ ∈ (closedBall (0 : ℂ) R)ᶜ := by
    simp only [z₀, mem_compl_iff, mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, not_le]
    rw [abs_of_nonneg (by linarith)]; linarith
  have hsub : (closedBall (0 : ℂ) R)ᶜ ⊆ connectedComponentIn Kᶜ z₀ :=
    (isConnected_compl_closedBall 0 hR).isPreconnected.subset_connectedComponentIn hz0
      (compl_subset_compl.2 hKR)
  refine ⟨?_, hsub⟩
  ext z
  constructor
  · rintro ⟨hzK, hub⟩
    have : ¬ connectedComponentIn Kᶜ z ⊆ closedBall 0 R := fun h =>
      hub (isBounded_closedBall.subset h)
    obtain ⟨w, hw, hwR⟩ := not_subset.1 this
    have hw0 := hsub hwR
    rw [connectedComponentIn_eq hw0, ← connectedComponentIn_eq hw]
    exact mem_connectedComponentIn hzK
  · intro hz
    refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact fun hb => compl_closedBall_unbounded R (hb.subset hsub)

theorem om_facts (γ : unitInterval → ℂ) (hγ : Continuous γ) (hnd : ∃ a b, γ a ≠ γ b) :
    OmFacts (Set.range γ) := by
  set K := Set.range γ with hKdef
  have hKc : IsCompact K := isCompact_range hγ
  have hKcl : IsClosed K := hKc.isClosed
  obtain ⟨R₁, hR₁⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hKc.isBounded
  set R := max R₁ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : K ⊆ closedBall 0 R := hR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨heq, hsub⟩ := om_eq hR hKR
  have hfar : ∀ z : ℂ, R < ‖z‖ → z ∈ Om K := fun z hz => by
    rw [heq]; apply hsub
    simpa [mem_closedBall, dist_zero_right] using hz
  have hopen : IsOpen (Om K) := by rw [heq]; exact hKcl.isOpen_compl.connectedComponentIn
  refine ⟨hKc, ?_, hopen, ?_, ⟨R, hfar⟩, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnd
    exact ⟨γ a, mem_range_self a, γ b, mem_range_self b, hab⟩
  · rw [heq, isConnected_connectedComponentIn_iff]
    have : ((R + 1 : ℝ) : ℂ) ∈ (closedBall (0 : ℂ) R)ᶜ := by
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, not_le]
      rw [abs_of_nonneg (by linarith)]; linarith
    exact fun h => this (hKR h)
  · refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hopen.isClosed_compl ?_
    intro z hz
    by_contra h
    simp only [mem_closedBall, dist_zero_right, not_le] at h
    exact hz (hfar z h)
  · intro y hy
    by_contra hyK
    rw [hopen.frontier_eq] at hy
    apply hy.2
    rw [heq] at hy ⊢
    exact mem_comp_of_mem_closure hKcl hyK hy.1

end ConformalBoundary.Dev.CT.PartO
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias om_facts := ConformalBoundary.Dev.CT.PartO.om_facts

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT.PartU
open ConformalBoundary.Dev.CT
lemma dist_le_of_mem_uIcc {a b c : unitInterval} (hc : c ∈ Set.uIcc a b) :
    dist c b ≤ dist a b := by
  rw [Set.mem_uIcc] at hc
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : (a : ℝ) ≤ c := h1
    have h2' : (c : ℝ) ≤ b := h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1' : (b : ℝ) ≤ c := h1
    have h2' : (c : ℝ) ≤ a := h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma piece (γ : unitInterval → ℂ) (hγ : Continuous γ) (a b : unitInterval) :
    IsPreconnected (γ '' Set.uIcc a b) :=
  isPreconnected_uIcc.image _ hγ.continuousOn

theorem ulc (γ : unitInterval → ℂ) (hγ : Continuous γ) :
    ∀ ε > 0, ∃ η > 0, ∀ p ∈ Set.range γ, ∀ q ∈ Set.range γ, dist p q < η →
      ∃ C ⊆ Set.range γ, IsPreconnected C ∧ p ∈ C ∧ q ∈ C ∧ C ⊆ Metric.ball p ε := by
  intro ε hε
  by_contra hne
  push Not at hne
  have key : ∀ n : ℕ, ∃ s t : unitInterval, dist (γ s) (γ t) < 1 / ((n : ℝ) + 1) ∧
      ∀ C ⊆ Set.range γ, IsPreconnected C → γ s ∈ C → γ t ∈ C →
        ¬ C ⊆ Metric.ball (γ s) ε := by
    intro n
    obtain ⟨p, ⟨s, rfl⟩, q, ⟨t, rfl⟩, hd, hC⟩ := hne (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨s, t, hd, hC⟩
  choose s t hd hC using key
  obtain ⟨⟨s0, t0⟩, -, φ, hφ, hlim⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (unitInterval × unitInterval))).tendsto_subseq
      (x := fun n => (s n, t n)) (fun _ => Set.mem_univ _)
  have hs : Filter.Tendsto (fun n => s (φ n)) Filter.atTop (nhds s0) :=
    (continuous_fst.tendsto _).comp hlim
  have ht : Filter.Tendsto (fun n => t (φ n)) Filter.atTop (nhds t0) :=
    (continuous_snd.tendsto _).comp hlim
  -- γ s0 = γ t0
  have heq : γ s0 = γ t0 := by
    have h1 : Filter.Tendsto (fun n => dist (γ (s (φ n))) (γ (t (φ n)))) Filter.atTop
        (nhds (dist (γ s0) (γ t0))) :=
      ((hγ.tendsto _).comp hs).dist ((hγ.tendsto _).comp ht)
    have h2 : Filter.Tendsto (fun n => dist (γ (s (φ n))) (γ (t (φ n)))) Filter.atTop
        (nhds 0) := by
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hd (φ n)).le) h0
    exact dist_eq_zero.mp (tendsto_nhds_unique h1 h2)
  set x := γ s0
  obtain ⟨δ1, hδ1, hc1⟩ := Metric.continuous_iff.mp hγ s0 (ε / 3) (by positivity)
  obtain ⟨δ2, hδ2, hc2⟩ := Metric.continuous_iff.mp hγ t0 (ε / 3) (by positivity)
  have e1 := Metric.tendsto_atTop.mp hs δ1 hδ1
  have e2 := Metric.tendsto_atTop.mp ht δ2 hδ2
  obtain ⟨N1, hN1⟩ := e1
  obtain ⟨N2, hN2⟩ := e2
  set n := φ (max N1 N2)
  have hsn : dist (s n) s0 < δ1 := hN1 _ (le_max_left _ _)
  have htn : dist (t n) t0 < δ2 := hN2 _ (le_max_right _ _)
  set C := γ '' Set.uIcc (s n) s0 ∪ γ '' Set.uIcc (t n) t0
  have hCsub : C ⊆ Metric.ball x (ε / 3) := by
    rintro y (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Metric.mem_ball.mpr (hc1 a (lt_of_le_of_lt (dist_le_of_mem_uIcc ha) hsn))
    · rw [Metric.mem_ball, show x = γ t0 from heq]
      exact hc2 a (lt_of_le_of_lt (dist_le_of_mem_uIcc ha) htn)
  apply hC n C
  · rintro y (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩) <;> exact ⟨a, rfl⟩
  · exact (piece γ hγ _ _).union x ⟨s0, Set.right_mem_uIcc, rfl⟩
      ⟨t0, Set.right_mem_uIcc, heq.symm⟩ (piece γ hγ _ _)
  · exact Or.inl ⟨s n, Set.left_mem_uIcc, rfl⟩
  · exact Or.inr ⟨t n, Set.left_mem_uIcc, rfl⟩
  · intro y hy
    have h1 := hCsub hy
    have h2 : dist (γ (s n)) x < ε / 3 := hCsub (Or.inl ⟨s n, Set.left_mem_uIcc, rfl⟩)
    rw [Metric.mem_ball] at h1 ⊢
    calc dist y (γ (s n)) ≤ dist y x + dist (γ (s n)) x := dist_triangle_right _ _ _
      _ < ε := by linarith

end ConformalBoundary.Dev.CT.PartU
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias ulc := ConformalBoundary.Dev.CT.PartU.ulc

/-- An exterior conformal map onto the outer region, with the facts used later. -/
structure ExtMap (K : Set ℂ) (Φ : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ Φ E
  inj : Set.InjOn Φ E
  onto : Φ '' E = Om K
  openMap : ∀ U ⊆ E, IsOpen U → IsOpen (Φ '' U)
  bdd : Bornology.IsBounded (Φ '' {w | 1 < ‖w‖ ∧ ‖w‖ < 2})
  laurent : ∃ a : ℂ, ∃ k : ℂ → ℂ, DifferentiableOn ℂ k (Metric.ball 0 1) ∧
    (∀ ζ ∈ Metric.ball (0 : ℂ) 1, k ζ ≠ 0) ∧ ∀ w ∈ E, Φ w = a + w / k (1 / w)

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ConformalBoundary.Dev.CT.PartR
open ConformalBoundary.Dev.CT
/-- An injective holomorphic map on an open set is an open map there. -/
theorem isOpen_image_of_injOn {F : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hF : DifferentiableOn ℂ F S) (hinj : InjOn F S) :
    ∀ V ⊆ S, IsOpen V → IsOpen (F '' V) := by
  intro V hVS hV
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨w, hwV, rfl⟩
  have ha : AnalyticAt ℂ F w := hF.analyticAt (hS.mem_nhds (hVS hwV))
  rcases ha.eventually_constant_or_nhds_le_map_nhds with h | h
  · exfalso
    have h2 : ∀ᶠ z in 𝓝[≠] w, F z = F w ∧ z ∈ S :=
      nhdsWithin_le_nhds (h.and (hS.mem_nhds (hVS hwV)))
    obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := (h2.and self_mem_nhdsWithin).exists
    exact hz3 (hinj hz2 (hVS hwV) hz1)
  · exact h (image_mem_map (hV.mem_nhds hwV))

/-- The inverse of an injective holomorphic map is holomorphic, and the map has
nonvanishing derivative. -/
theorem inverse_hasDerivAt {f g : ℂ → ℂ} {U B : Set ℂ} (hU : IsOpen U) (hB : IsOpen B)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hgB : MapsTo g B U) (hfg : ∀ w ∈ B, f (g w) = w) (hgc : ContinuousOn g B) :
    ∀ w ∈ B, deriv f (g w) ≠ 0 ∧ HasDerivAt g (deriv f (g w))⁻¹ w := by
  have key : ∀ w ∈ B, deriv f (g w) ≠ 0 → HasDerivAt g (deriv f (g w))⁻¹ w := by
    intro w hw hne
    exact HasDerivAt.of_local_left_inverse (hgc.continuousAt (hB.mem_nhds hw))
      (hf.differentiableAt (hU.mem_nhds (hgB hw))).hasDerivAt hne
      (Filter.mem_of_superset (hB.mem_nhds hw) fun y hy => hfg y hy)
  intro w₀ hw₀
  suffices h : deriv f (g w₀) ≠ 0 from ⟨h, key w₀ hw₀ h⟩
  intro hzero
  set z₀ := g w₀ with hz₀
  have hz₀U : z₀ ∈ U := hgB hw₀
  have han : AnalyticAt ℂ (deriv f) z₀ := (hf.analyticAt (hU.mem_nhds hz₀U)).deriv
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · -- `f` is locally constant: contradicts injectivity
    have h2 : ∀ᶠ z in 𝓝 z₀, deriv f z = 0 ∧ z ∈ U := h.and (hU.mem_nhds hz₀U)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h2
    have hconst : ∀ x ∈ ball z₀ ε, ∀ y ∈ ball z₀ ε, f x = f y := by
      intro x hx y hy
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ ε).isPreconnected
        (hf.mono fun z hz => (hball z hz).2) (fun z hz => (hball z hz).1) hx hy
    set z₁ : ℂ := z₀ + ((ε / 2 : ℝ) : ℂ)
    have hz₁ : z₁ ∈ ball z₀ ε := by
      simp only [z₁, mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_pos (by linarith)]; linarith
    have hne : z₁ ≠ z₀ := by
      intro h'
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by simpa [z₁] using h'
      have : (ε / 2 : ℝ) = 0 := by exact_mod_cast this
      linarith
    exact hne (hinj (hball z₁ hz₁).2 hz₀U (hconst _ hz₁ _ (mem_ball_self hε)))
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (eventually_nhdsWithin_iff.mp h)
    have hgcont : ContinuousAt g w₀ := hgc.continuousAt (hB.mem_nhds hw₀)
    have h3 : ∀ᶠ w in 𝓝 w₀, g w ∈ ball z₀ ε ∧ w ∈ B :=
      (hgcont.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))).and (hB.mem_nhds hw₀)
    obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.mp h3
    have hdiff : DifferentiableOn ℂ g (ball w₀ δ) := by
      refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (isOpen_ball.mem_nhds (mem_ball_self hδ))).mp ⟨?_, hgcont⟩
      intro w hw
      have hwB := (hδball w hw.1).2
      have hgw : g w ≠ z₀ := by
        intro h'
        apply hw.2
        rw [mem_singleton_iff, ← hfg w hwB, ← hfg w₀ hw₀, h']
      exact (key w hwB (hball _ (hδball w hw.1).1 hgw)).differentiableAt.differentiableWithinAt
    have hgd : HasDerivAt g (deriv g w₀) w₀ :=
      (hdiff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).hasDerivAt
    have hfd : HasDerivAt f (deriv f z₀) z₀ :=
      (hf.differentiableAt (hU.mem_nhds hz₀U)).hasDerivAt
    have hcomp : HasDerivAt (f ∘ g) (deriv f z₀ * deriv g w₀) w₀ := hfd.comp w₀ hgd
    have hid : HasDerivAt (f ∘ g) 1 w₀ := by
      refine (hasDerivAt_id w₀).congr_of_eventuallyEq ?_
      exact Filter.mem_of_superset (hB.mem_nhds hw₀) fun y hy => hfg y hy
    have := hcomp.unique hid
    rw [hzero, zero_mul] at this
    exact zero_ne_one this

/-- Points far out lie in the outer region. -/
theorem small_mem (K : Set ℂ) (hK : OmFacts K) (a : ℂ) :
    ∃ r > 0, ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < r → a + ζ⁻¹ ∈ Om K := by
  obtain ⟨R, hR⟩ := hK.far
  have hX : 0 < |R| + ‖a‖ + 1 := by positivity
  refine ⟨(|R| + ‖a‖ + 1)⁻¹, inv_pos.mpr hX, fun ζ hζ hlt => hR _ ?_⟩
  have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have h1 : |R| + ‖a‖ + 1 < ‖ζ‖⁻¹ := (lt_inv_comm₀ hX hpos).mpr hlt
  have h2 : ‖ζ⁻¹‖ ≤ ‖a + ζ⁻¹‖ + ‖a‖ := by
    calc ‖ζ⁻¹‖ = ‖(a + ζ⁻¹) + (-a)‖ := by ring_nf
      _ ≤ ‖a + ζ⁻¹‖ + ‖-a‖ := norm_add_le _ _
      _ = ‖a + ζ⁻¹‖ + ‖a‖ := by rw [norm_neg]
  rw [norm_inv] at h2
  have := le_abs_self R
  linarith

/-- The inverted region `{0} ∪ {1/(z - a) : z ∈ Om K}`. -/
def invReg (K : Set ℂ) (a : ℂ) : Set ℂ := {ζ | ζ = 0 ∨ a + ζ⁻¹ ∈ Om K}

theorem invReg_isOpen (K : Set ℂ) (hK : OmFacts K) (a : ℂ) : IsOpen (invReg K a) := by
  obtain ⟨r, hr0, hr⟩ := small_mem K hK a
  rw [isOpen_iff_mem_nhds]
  intro ζ hζ
  by_cases h0 : ζ = 0
  · subst h0
    refine Filter.mem_of_superset (ball_mem_nhds 0 hr0) fun x hx => ?_
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr (hr x hx0 (by simpa using hx))
  · have hm : a + ζ⁻¹ ∈ Om K := hζ.resolve_left h0
    have hc : ContinuousAt (fun x : ℂ => a + x⁻¹) ζ :=
      continuousAt_const.add (continuousAt_inv₀ h0)
    exact Filter.mem_of_superset (hc.preimage_mem_nhds (hK.isOpen.mem_nhds hm))
      fun x hx => Or.inr hx

theorem invReg_isConnected (K : Set ℂ) (hK : OmFacts K) (a : ℂ) (ha : a ∉ Om K) :
    IsConnected (invReg K a) := by
  obtain ⟨r, hr0, hr⟩ := small_mem K hK a
  have hS : IsConnected ((fun z : ℂ => (z - a)⁻¹) '' Om K) := by
    refine hK.connected.image _ ?_
    intro z hz
    have hza : z - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hz)
    exact ((continuousAt_id.sub continuousAt_const).inv₀ hza).continuousWithinAt
  refine hS.subset_closure ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    right
    simpa using hz
  · intro ζ hζ
    by_cases h0 : ζ = 0
    · subst h0
      rw [Metric.mem_closure_iff]
      intro ε hε
      set t : ℝ := min r ε / 2 with ht_def
      have ht : 0 < t := by positivity
      have htr : t < r := by
        have := min_le_left r ε; rw [ht_def]; linarith
      have hte : t < ε := by
        have := min_le_right r ε; rw [ht_def]; linarith
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      have htn : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      refine ⟨(t : ℂ), ⟨a + (t : ℂ)⁻¹, hr _ htne (by rw [htn]; exact htr), by simp⟩, ?_⟩
      rw [dist_eq_norm, zero_sub, norm_neg, htn]
      exact hte
    · exact subset_closure ⟨a + ζ⁻¹, hζ.resolve_left h0, by simp⟩

theorem invReg_compl_connected (K : Set ℂ) (a : ℂ) (haK : a ∈ K)
    (hconn : IsConnected (Om K)ᶜ) :
    IsConnected (((↑) : ℂ → OnePoint ℂ) '' invReg K a)ᶜ := by
  classical
  have ha : a ∉ Om K := fun h => h.1 haK
  let h : ℂ → OnePoint ℂ := fun z => if z = a then OnePoint.infty else (((z - a)⁻¹ : ℂ) : OnePoint ℂ)
  have hcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = a
    · subst hz
      show Tendsto h (𝓝 z) (𝓝 (h z))
      have hz' : h z = OnePoint.infty := if_pos rfl
      rw [hz', OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
      rintro s ⟨-, hs⟩
      obtain ⟨M, hM⟩ := hs.isBounded.exists_norm_le
      have hM' : 0 < |M| + 1 := by positivity
      filter_upwards [ball_mem_nhds z (inv_pos.mpr hM')] with x hx
      by_cases hxz : x = z
      · right; simp [h, hxz]
      · left
        refine ⟨(x - z)⁻¹, fun hmem => ?_, by simp [h, hxz]⟩
        have h0 := hM _ hmem
        have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
        have h1 : |M| + 1 < ‖x - z‖⁻¹ :=
          (lt_inv_comm₀ hM' hpos).mpr (by simpa [dist_eq_norm] using hx)
        rw [norm_inv] at h0
        linarith [le_abs_self M]
    · have heq : h =ᶠ[𝓝 z] fun x => (((x - a)⁻¹ : ℂ) : OnePoint ℂ) := by
        filter_upwards [isOpen_ne.mem_nhds hz] with x hx
        simp [h, hx]
      refine ContinuousAt.congr ?_ heq.symm
      exact OnePoint.continuous_coe.continuousAt.comp
        ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hz))
  have himg : h '' (Om K)ᶜ = (((↑) : ℂ → OnePoint ℂ) '' invReg K a)ᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxa : x = a
      · simp [h, hxa]
      · simp only [h, if_neg hxa]
        rintro ⟨ζ, hζ, hζeq⟩
        have hζ' : ζ = (x - a)⁻¹ := OnePoint.coe_injective hζeq
        rcases hζ with h0 | h1
        · rw [hζ'] at h0; exact sub_ne_zero.mpr hxa (inv_eq_zero.mp h0)
        · rw [hζ'] at h1; simp at h1; exact hx h1
    · intro hy
      induction y using OnePoint.rec with
      | infty => exact ⟨a, ha, by simp [h]⟩
      | coe ζ =>
        have hζ : ζ ∉ invReg K a := fun hm => hy ⟨ζ, hm, rfl⟩
        have h0 : ζ ≠ 0 := fun h0 => hζ (Or.inl h0)
        have h1 : a + ζ⁻¹ ∉ Om K := fun h1 => hζ (Or.inr h1)
        refine ⟨a + ζ⁻¹, h1, ?_⟩
        have : a + ζ⁻¹ ≠ a := by simpa using h0
        simp [h, this]
  rw [← himg]
  exact hconn.image _ hcont.continuousOn

theorem isOpen_E : IsOpen E := isOpen_lt continuous_const continuous_norm

theorem mem_E_inv {w : ℂ} (hw : w ∈ E) : w ≠ 0 ∧ w⁻¹ ∈ ball (0 : ℂ) 1 ∧ w⁻¹ ≠ 0 := by
  have hw' : 1 < ‖w‖ := hw
  have h0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw'; linarith
  refine ⟨h0, ?_, inv_ne_zero h0⟩
  rw [mem_ball_zero_iff, norm_inv]
  exact inv_lt_one_of_one_lt₀ hw'

/-- The exterior Riemann map (inversion and `AhlforsComplexAnalysis.riemann_mapping_theorem`). -/
theorem exists_extMap (K : Set ℂ) (hK : OmFacts K) (hconn : IsConnected (Om K)ᶜ) :
    ∃ Φ : ℂ → ℂ, ExtMap K Φ := by
  classical
  obtain ⟨a, haK⟩ := hK.nontriv.nonempty
  have haΩ : a ∉ Om K := fun h => h.1 haK
  set U := invReg K a with hUdef
  have hUo : IsOpen U := invReg_isOpen K hK a
  have hU0 : (0 : ℂ) ∈ U := Or.inl rfl
  have hSC : AhlforsComplexAnalysis.IsSimplyConnectedRegion U :=
    ⟨⟨hUo, invReg_isConnected K hK a haΩ⟩, invReg_compl_connected K a haK hconn⟩
  have hne : U ≠ univ := by
    obtain ⟨b, hbK, hba⟩ := hK.nontriv.exists_ne a
    intro hU
    have hb : (b - a)⁻¹ ∈ U := hU ▸ mem_univ _
    rcases hb with h0 | h1
    · exact sub_ne_zero.mpr hba (inv_eq_zero.mp h0)
    · simp at h1; exact h1.1 hbK
  obtain ⟨f, hfan, hf0, -, -, hfinj, hfimg⟩ :=
    (AhlforsComplexAnalysis.riemann_mapping_theorem hSC hne hU0).1
  have hfd : DifferentiableOn ℂ f U := hfan.differentiableOn
  set g := Function.invFunOn f U with hgdef
  have hgU : MapsTo g (ball 0 1) U := by
    intro w hw
    rw [← hfimg] at hw
    exact Function.invFunOn_mem hw
  have hfg : ∀ w ∈ ball (0 : ℂ) 1, f (g w) = w := by
    intro w hw; rw [← hfimg] at hw; exact Function.invFunOn_eq hw
  have hgf : ∀ z ∈ U, g (f z) = z := fun z hz => hfinj.leftInvOn_invFunOn hz
  have hgc : ContinuousOn g (ball 0 1) := by
    rw [continuousOn_open_iff isOpen_ball]
    intro t ht
    have heq : ball (0 : ℂ) 1 ∩ g ⁻¹' t = f '' (U ∩ t) := by
      ext w; constructor
      · rintro ⟨hw, hwt⟩; exact ⟨g w, ⟨hgU hw, hwt⟩, hfg w hw⟩
      · rintro ⟨z, ⟨hzU, hzt⟩, rfl⟩
        refine ⟨hfimg ▸ mem_image_of_mem f hzU, ?_⟩
        show g (f z) ∈ t
        rw [hgf z hzU]; exact hzt
    rw [heq]
    exact isOpen_image_of_injOn hUo hfd hfinj _ inter_subset_left (hUo.inter ht)
  have hinv := inverse_hasDerivAt hUo isOpen_ball hfd hfinj hgU hfg hgc
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) := fun w hw =>
    (hinv w hw).2.differentiableAt.differentiableWithinAt
  have hginj : InjOn g (ball 0 1) := fun x hx y hy h => by
    rw [← hfg x hx, ← hfg y hy, h]
  have hg0 : g 0 = 0 := by
    have := hgf 0 hU0; rwa [hf0] at this
  have hgne : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 0 → g ζ ≠ 0 := by
    intro ζ hζ h0 hg
    apply h0
    rw [← hfg ζ hζ, hg, hf0]
  have hgΩ : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 0 → a + (g ζ)⁻¹ ∈ Om K := fun ζ hζ h0 =>
    (hgU hζ).resolve_left (hgne ζ hζ h0)
  set Φ : ℂ → ℂ := fun w => a + (g w⁻¹)⁻¹ with hΦdef
  have hΦdiff : DifferentiableOn ℂ Φ E := by
    intro w hw
    obtain ⟨h0, h1, h2⟩ := mem_E_inv hw
    have hd : DifferentiableAt ℂ (fun w : ℂ => g w⁻¹) w :=
      (hgdiff.differentiableAt (isOpen_ball.mem_nhds h1)).comp w (differentiableAt_inv h0)
    exact ((differentiableAt_const a).add (hd.inv (hgne _ h1 h2))).differentiableWithinAt
  have hΦinj : InjOn Φ E := by
    intro w hw w' hw' h
    obtain ⟨_, h1, _⟩ := mem_E_inv hw
    obtain ⟨_, h1', _⟩ := mem_E_inv hw'
    have h3 : (g w⁻¹)⁻¹ = (g w'⁻¹)⁻¹ := add_left_cancel h
    rw [inv_inj] at h3
    exact inv_inj.mp (hginj h1 h1' h3)
  refine ⟨Φ, hΦdiff, hΦinj, ?_, ?_, ?_, ?_⟩
  · -- onto
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨_, h1, h2⟩ := mem_E_inv hw
      exact hgΩ _ h1 h2
    · intro hz
      have hza : z - a ≠ 0 := sub_ne_zero.mpr fun h => haΩ (h ▸ hz)
      set ζ₀ := (z - a)⁻¹ with hζ₀
      have hζ₀0 : ζ₀ ≠ 0 := inv_ne_zero hza
      have hζ₀U : ζ₀ ∈ U := Or.inr (by simpa [hζ₀] using hz)
      have hfb : f ζ₀ ∈ ball (0 : ℂ) 1 := hfimg ▸ mem_image_of_mem f hζ₀U
      have hf0' : f ζ₀ ≠ 0 := by
        intro h
        exact hζ₀0 (hfinj hζ₀U hU0 (by rw [h, hf0]))
      refine ⟨(f ζ₀)⁻¹, ?_, ?_⟩
      · show 1 < ‖(f ζ₀)⁻¹‖
        rw [norm_inv]
        exact one_lt_inv₀ (norm_pos_iff.mpr hf0') |>.mpr (mem_ball_zero_iff.mp hfb)
      · show a + (g ((f ζ₀)⁻¹)⁻¹)⁻¹ = z
        rw [inv_inv, hgf ζ₀ hζ₀U, hζ₀, inv_inv]
        ring
  · exact isOpen_image_of_injOn isOpen_E hΦdiff hΦinj
  · -- bdd
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ), ‖f z‖ < 1 / 2 := by
      have hc : ContinuousAt f 0 := (hfd.differentiableAt (hUo.mem_nhds hU0)).continuousAt
      have := hc.eventually (isOpen_ball.mem_nhds (show f 0 ∈ ball (0 : ℂ) (1 / 2) by
        rw [hf0]; exact mem_ball_self (by norm_num)))
      filter_upwards [this] with z hz
      simpa using hz
    obtain ⟨s, hs, hsb⟩ := Metric.eventually_nhds_iff_ball.mp hev
    rw [isBounded_iff_forall_norm_le]
    refine ⟨‖a‖ + s⁻¹, ?_⟩
    rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
    obtain ⟨h0, h1, h2⟩ := mem_E_inv (show w ∈ E from hw1)
    have hgs : s ≤ ‖g w⁻¹‖ := by
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have := hsb (g w⁻¹) (by simpa using hlt)
      rw [hfg _ h1, norm_inv] at this
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr h0
      have h2w : (2 : ℝ) < ‖w‖ := by
        rw [one_div] at this
        exact (inv_lt_inv₀ hwpos (by norm_num)).mp this
      linarith
    calc ‖a + (g w⁻¹)⁻¹‖ ≤ ‖a‖ + ‖(g w⁻¹)⁻¹‖ := norm_add_le _ _
      _ ≤ ‖a‖ + s⁻¹ := by
        rw [norm_inv]
        gcongr
  · -- laurent
    refine ⟨a, dslope g 0, ?_, ?_, ?_⟩
    · exact (Complex.differentiableOn_dslope
        (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mpr hgdiff
    · intro ζ hζ
      by_cases h0 : ζ = 0
      · subst h0
        rw [dslope_same, (hinv 0 hζ).2.deriv]
        exact inv_ne_zero (hinv 0 hζ).1
      · rw [dslope_of_ne _ h0, slope_def_field, hg0, sub_zero, sub_zero]
        exact div_ne_zero (hgne ζ hζ h0) h0
    · intro w hw
      obtain ⟨h0, h1, h2⟩ := mem_E_inv hw
      rw [one_div, dslope_of_ne _ h2, slope_def_field, hg0, sub_zero, sub_zero]
      simp only [hΦdef]
      have := hgne _ h1 h2
      field_simp

end ConformalBoundary.Dev.CT.PartR
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias exists_extMap := ConformalBoundary.Dev.CT.PartR.exists_extMap

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
open Set Metric
namespace ConformalBoundary.Dev.CT.PartO
open ConformalBoundary.Dev.CT
theorem compl_connected (γ : unitInterval → ℂ) (hγ : Continuous γ) (hK : OmFacts (Set.range γ)) :
    IsConnected (Om (Set.range γ))ᶜ := by
  set K := Set.range γ with hKdef
  have hKcl : IsClosed K := hK.compact.isClosed
  have hKconn : IsConnected K := isConnected_range hγ
  have hKsub : K ⊆ (Om K)ᶜ := fun z hz h => h.1 hz
  obtain ⟨k₀, hk₀⟩ := hKconn.nonempty
  refine ⟨⟨k₀, hKsub hk₀⟩, isPreconnected_of_forall k₀ ?_⟩
  intro y hy
  by_cases hyK : y ∈ K
  · exact ⟨K, hKsub, hk₀, hyK, hKconn.isPreconnected⟩
  set B := connectedComponentIn Kᶜ y
  have hBb : Bornology.IsBounded B := by
    by_contra h; exact hy ⟨hyK, h⟩
  have hBo : IsOpen B := hKcl.isOpen_compl.connectedComponentIn
  have hclB : closure B ⊆ (Om K)ᶜ := by
    intro p hp hpΩ
    have hpB : p ∈ B := mem_comp_of_mem_closure hKcl hpΩ.1 hp
    apply hpΩ.2
    rw [← connectedComponentIn_eq hpB]; exact hBb
  have hfr : (frontier B).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨⟨y, mem_connectedComponentIn hyK⟩, fun h => ?_⟩
    rw [h] at hBb
    exact compl_closedBall_unbounded 0 (hBb.subset (subset_univ _))
  obtain ⟨p, hp⟩ := hfr
  have hpK : p ∈ K := by
    rw [hBo.frontier_eq] at hp
    by_contra h
    exact hp.2 (mem_comp_of_mem_closure hKcl h hp.1)
  refine ⟨K ∪ closure B, union_subset hKsub hclB, Or.inl hk₀,
    Or.inr (subset_closure (mem_connectedComponentIn hyK)), ?_⟩
  exact hKconn.isPreconnected.union' ⟨p, hpK, frontier_subset_closure hp⟩
    isPreconnected_connectedComponentIn.closure

end ConformalBoundary.Dev.CT.PartO
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias compl_connected := ConformalBoundary.Dev.CT.PartO.compl_connected

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT.PartA
open ConformalBoundary.Dev.CT
open MeasureTheory Set
/-- The annulus `1 < |w| < 2`. -/
def Ann : Set ℂ := {w | 1 < ‖w‖ ∧ ‖w‖ < 2}

lemma isOpen_E : IsOpen E := isOpen_lt continuous_const continuous_norm

lemma isOpen_Ann : IsOpen Ann :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma Ann_sub_E : Ann ⊆ E := fun _ hw => hw.1

/-- The area density `|Φ'|²` restricted to the annulus. -/
noncomputable def dens (Φ : ℂ → ℂ) (w : ℂ) : ENNReal :=
  Ann.indicator (fun w => ENNReal.ofReal (‖deriv Φ w‖ ^ 2)) w

lemma measurable_dens (Φ : ℂ → ℂ) : Measurable (dens Φ) :=
  ((measurable_deriv Φ).norm.pow_const 2).ennreal_ofReal.indicator isOpen_Ann.measurableSet

lemma det_restrictScalars_complex (L : ℂ →L[ℂ] ℂ) :
    (L.restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = ‖L 1‖ ^ 2 := by
  have h1 : (L : ℂ →ₗ[ℂ] ℂ) = LinearMap.mulLeft ℂ (L 1) := by
    apply LinearMap.ext_ring
    simp
  have h2 : ((L.restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) =
      (L : ℂ →ₗ[ℂ] ℂ).restrictScalars ℝ := rfl
  rw [ContinuousLinearMap.det, h2, LinearMap.det_restrictScalars, h1, LinearMap.det_mulLeft,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-- Area bound: `∫∫_Ann |Φ'|² ≤ area Φ(Ann)`. -/
lemma lintegral_dens_le (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ E) (hi : Set.InjOn Φ E) :
    ∫⁻ w, dens Φ w ≤ volume (Φ '' Ann) := by
  have hder : ∀ x ∈ Ann, HasFDerivWithinAt Φ
      ((fderiv ℂ Φ x).restrictScalars ℝ : ℂ →L[ℝ] ℂ) Ann x := fun x hx =>
    (((hd x (Ann_sub_E hx)).differentiableAt
      (isOpen_E.mem_nhds (Ann_sub_E hx))).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume isOpen_Ann.measurableSet
    hder (hi.mono Ann_sub_E) (fun _ => 1)
  rw [setLIntegral_one] at key
  rw [key]
  unfold dens
  rw [lintegral_indicator isOpen_Ann.measurableSet]
  apply le_of_eq
  apply setLIntegral_congr_fun isOpen_Ann.measurableSet
  intro x _
  dsimp only
  rw [det_restrictScalars_complex, fderiv_apply_one_eq_deriv, abs_of_nonneg (sq_nonneg _),
    mul_one]

/-- The circle parametrisation around `1`. -/
noncomputable def gam (ρ θ : ℝ) : ℂ := 1 + (ρ : ℂ) * Complex.exp (θ * Complex.I)

lemma gam_eq (ρ θ : ℝ) :
    gam ρ θ = 1 + (ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  rw [gam, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma normSq_gam (ρ θ : ℝ) : ‖gam ρ θ‖ ^ 2 = 1 + 2 * ρ * Real.cos θ + ρ ^ 2 := by
  rw [gam_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.one_im,
    Complex.mul_im]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [this]

lemma norm_gam_lt (ρ θ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) : ‖gam ρ θ‖ < 2 := by
  have : ‖gam ρ θ‖ ≤ 1 + ρ := by
    calc ‖gam ρ θ‖ ≤ ‖(1 : ℂ)‖ + ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_add_le _ _
      _ = 1 + ρ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos h0]; simp
  linarith

lemma hasDerivAt_gam (ρ θ : ℝ) :
    HasDerivAt (gam ρ) ((ρ : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I)) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
  exact (h1.cexp.const_mul (ρ : ℂ)).const_add 1

lemma continuous_gam (ρ : ℝ) : Continuous (gam ρ) := by
  unfold gam; fun_prop

/-- Integration along an arc of the circle that stays in the annulus. -/
lemma arc_bound (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ E) (ρ : ℝ) (hρ0 : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (α β : ℝ) (hαβ : α ≤ β) (hα : -Real.pi < α) (hβ : β < Real.pi)
    (hA : ∀ θ ∈ Icc α β, gam ρ θ ∈ Ann)
    (hdist : ε ≤ ‖Φ (gam ρ β) - Φ (gam ρ α)‖) :
    ENNReal.ofReal (ε ^ 2 / (2 * Real.pi)) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (ρ ^ 2) *
        dens Φ (1 + (ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) := by
  have hdcont : ContinuousOn (deriv Φ) E :=
    (hd.analyticOnNhd isOpen_E).deriv.continuousOn
  have hcd : ContinuousOn (fun θ => deriv Φ (gam ρ θ)) (Icc α β) :=
    hdcont.comp (continuous_gam ρ).continuousOn (fun θ hθ => Ann_sub_E (hA θ hθ))
  set g : ℝ → ℂ := fun θ => deriv Φ (gam ρ θ) * ((ρ : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I))
    with hg
  have hgc : ContinuousOn g (Icc α β) := hcd.mul (by fun_prop)
  have hderiv : ∀ θ ∈ uIcc α β, HasDerivAt (Φ ∘ gam ρ) (g θ) θ := by
    intro θ hθ
    rw [uIcc_of_le hαβ] at hθ
    have hE := Ann_sub_E (hA θ hθ)
    exact ((hd _ hE).differentiableAt (isOpen_E.mem_nhds hE)).hasDerivAt.comp θ
      (hasDerivAt_gam ρ θ)
  have hFTC : ∫ θ in α..β, g θ = Φ (gam ρ β) - Φ (gam ρ α) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hgc.intervalIntegrable_of_Icc hαβ)
  have hgn : ∀ θ, ‖g θ‖ = ρ * ‖deriv Φ (gam ρ θ)‖ := by
    intro θ
    rw [hg]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ0]
    ring
  set x : ℝ → ℝ := fun θ => ρ * ‖deriv Φ (gam ρ θ)‖ with hx
  have hxc : ContinuousOn x (Icc α β) := continuousOn_const.mul hcd.norm
  have h1 : ε ≤ ∫ θ in α..β, x θ := by
    calc ε ≤ ‖∫ θ in α..β, g θ‖ := by rw [hFTC]; exact hdist
      _ ≤ ∫ θ in α..β, ‖g θ‖ := intervalIntegral.norm_integral_le_integral_norm hαβ
      _ = ∫ θ in α..β, x θ := by simp only [hgn, hx]
  set c : ℝ := Real.pi / ε with hc
  have hcpos : 0 < c := div_pos Real.pi_pos hε
  have hxsc : ContinuousOn (fun θ => x θ ^ 2) (Icc α β) := hxc.pow 2
  have hq : ContinuousOn (fun θ => c * x θ ^ 2) (Icc α β) := continuousOn_const.mul hxsc
  have hq' : ContinuousOn (fun θ => c * x θ ^ 2 + ε / (4 * Real.pi)) (Icc α β) :=
    hq.add continuousOn_const
  have h2 : ∫ θ in α..β, x θ ≤ ∫ θ in α..β, (c * x θ ^ 2 + ε / (4 * Real.pi)) := by
    apply intervalIntegral.integral_mono_on hαβ (hxc.intervalIntegrable_of_Icc hαβ)
      (hq'.intervalIntegrable_of_Icc hαβ)
    intro θ _
    have key : c * x θ ^ 2 + ε / (4 * Real.pi) - x θ =
        c * (x θ - ε / (2 * Real.pi)) ^ 2 := by
      rw [hc]; field_simp; ring
    nlinarith [mul_nonneg hcpos.le (sq_nonneg (x θ - ε / (2 * Real.pi)))]
  have h3 : ∫ θ in α..β, (c * x θ ^ 2 + ε / (4 * Real.pi)) =
      c * (∫ θ in α..β, x θ ^ 2) + (β - α) * (ε / (4 * Real.pi)) := by
    rw [intervalIntegral.integral_add
      (hq.intervalIntegrable_of_Icc hαβ) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  set I2 := ∫ θ in α..β, x θ ^ 2 with hI2
  have hlen : (β - α) * (ε / (4 * Real.pi)) ≤ ε / 2 := by
    have : β - α ≤ 2 * Real.pi := by linarith
    calc (β - α) * (ε / (4 * Real.pi)) ≤ (2 * Real.pi) * (ε / (4 * Real.pi)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ε / 2 := by field_simp; ring
  have h4 : ε ^ 2 / (2 * Real.pi) ≤ I2 := by
    have : ε / 2 ≤ c * I2 := by linarith
    rw [hc] at this
    rw [div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hε] at this
    nlinarith [Real.pi_pos]
  -- pass to lintegrals
  have hint : IntegrableOn (fun θ => x θ ^ 2) (Ioc α β) := (hxsc.integrableOn_Icc).mono_set
    Ioc_subset_Icc_self
  have h5 : ENNReal.ofReal I2 = ∫⁻ θ in Ioc α β, ENNReal.ofReal (x θ ^ 2) := by
    rw [hI2, intervalIntegral.integral_of_le hαβ]
    exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)
  calc ENNReal.ofReal (ε ^ 2 / (2 * Real.pi)) ≤ ENNReal.ofReal I2 := ENNReal.ofReal_le_ofReal h4
    _ = ∫⁻ θ in Ioc α β, ENNReal.ofReal (x θ ^ 2) := h5
    _ ≤ ∫⁻ θ in Ioc α β, ENNReal.ofReal (ρ ^ 2) *
        dens Φ (1 + (ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro θ hθ
      rw [← gam_eq]
      unfold dens
      rw [indicator_of_mem (hA θ (Ioc_subset_Icc_self hθ)), hx]
      simp only
      rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ _ := lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Ioo hα hβ))

/-- Membership in `E` of circle points, in terms of the angle. -/
lemma gam_mem_E_iff (ρ θ : ℝ) (hρ : 0 < ρ) : gam ρ θ ∈ E ↔ -(ρ / 2) < Real.cos θ := by
  show 1 < ‖gam ρ θ‖ ↔ _
  rw [← one_lt_sq_iff₀ (norm_nonneg _), normSq_gam]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma gam_arg (ρ : ℝ) (w : ℂ) (hw : ‖w - 1‖ = ρ) :
    gam ρ (Complex.arg (w - 1)) = w := by
  rw [gam, ← hw, Complex.norm_mul_exp_arg_mul_I]; ring

/-- One circle: if some chord image is long, the circle carries a lot of area density. -/
lemma circle_bound (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ E) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (ε : ℝ) (hε : 0 < ε) (w w' : ℂ) (hw : w ∈ E) (hw' : w' ∈ E)
    (hr : ‖w - 1‖ = ρ) (hr' : ‖w' - 1‖ = ρ) (hdist : ε ≤ dist (Φ w) (Φ w')) :
    ENNReal.ofReal (ε ^ 2 / (2 * Real.pi)) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (ρ ^ 2) *
        dens Φ (1 + (ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) := by
  set α := Complex.arg (w - 1)
  set β := Complex.arg (w' - 1)
  have hgα : gam ρ α = w := gam_arg ρ w hr
  have hgβ : gam ρ β = w' := gam_arg ρ w' hr'
  have hcα : -(ρ / 2) < Real.cos α := (gam_mem_E_iff ρ α hρ0).1 (hgα ▸ hw)
  have hcβ : -(ρ / 2) < Real.cos β := (gam_mem_E_iff ρ β hρ0).1 (hgβ ▸ hw')
  have hlt : ∀ t : ℝ, |t| ≤ Real.pi → -(ρ / 2) < Real.cos t → |t| < Real.pi := by
    intro t ht hct
    rcases ht.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← Real.cos_abs, h, Real.cos_pi] at hct
      linarith
  have hα := hlt α (Complex.abs_arg_le_pi _) hcα
  have hβ := hlt β (Complex.abs_arg_le_pi _) hcβ
  -- every angle between α and β gives a point of the annulus
  have hmono : ∀ t s : ℝ, |s| < Real.pi → |t| ≤ |s| → Real.cos s ≤ Real.cos t := by
    intro t s hs hts
    rw [← Real.cos_abs t, ← Real.cos_abs s]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) hs.le hts
  have hA : ∀ θ ∈ Icc (min α β) (max α β), gam ρ θ ∈ Ann := by
    intro θ hθ
    refine ⟨?_, norm_gam_lt ρ θ hρ0 hρ1⟩
    show gam ρ θ ∈ E
    rw [gam_mem_E_iff ρ θ hρ0]
    have hb : |θ| ≤ |α| ∨ |θ| ≤ |β| := by
      rcases le_total α β with h | h
      · rw [min_eq_left h, max_eq_right h] at hθ
        by_cases h0 : 0 ≤ θ
        · right; rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans hθ.2)]; exact hθ.2
        · left; push Not at h0
          rw [abs_of_neg h0, abs_of_neg (lt_of_le_of_lt hθ.1 h0)]; linarith [hθ.1]
      · rw [min_eq_right h, max_eq_left h] at hθ
        by_cases h0 : 0 ≤ θ
        · left; rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans hθ.2)]; exact hθ.2
        · right; push Not at h0
          rw [abs_of_neg h0, abs_of_neg (lt_of_le_of_lt hθ.1 h0)]; linarith [hθ.1]
    rcases hb with h | h
    · exact lt_of_lt_of_le hcα (hmono θ α hα h)
    · exact lt_of_lt_of_le hcβ (hmono θ β hβ h)
  have hαlo := (abs_lt.1 hα).1
  have hαhi := (abs_lt.1 hα).2
  have hβlo := (abs_lt.1 hβ).1
  have hβhi := (abs_lt.1 hβ).2
  rcases le_total α β with h | h
  · apply arc_bound Φ hd ρ hρ0 ε hε α β h hαlo hβhi
    · intro θ hθ; apply hA; rwa [min_eq_left h, max_eq_right h]
    · rw [hgα, hgβ, ← dist_eq_norm, dist_comm]; exact hdist
  · apply arc_bound Φ hd ρ hρ0 ε hε β α h hβlo hαhi
    · intro θ hθ; apply hA; rwa [min_eq_right h, max_eq_left h]
    · rw [hgα, hgβ, ← dist_eq_norm]; exact hdist

/-- The integral of `c / r` over `(δ², δ)`. -/
lemma lintegral_inv (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∫⁻ r in Ioo (δ ^ 2) δ, ENNReal.ofReal (c / r) = ENNReal.ofReal (c * Real.log (1 / δ)) := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hcont : ContinuousOn (fun r : ℝ => c / r) (Icc (δ ^ 2) δ) :=
    continuousOn_const.div continuousOn_id (fun r hr => (hδ2.trans_le hr.1).ne')
  have hint : IntegrableOn (fun r : ℝ => c / r) (Ioo (δ ^ 2) δ) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo]
    have hle : δ ^ 2 ≤ δ := by nlinarith
    rw [← intervalIntegral.integral_of_le hle]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hδ2 hδ]
    congr 2
    field_simp
  · exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun r hr =>
      div_nonneg hc (hδ2.trans hr.1).le)

/-- The case `w₀ = 1`, with an explicit area bound `V`. -/
lemma core (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ E) (hi : Set.InjOn Φ E) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : volume (Φ '' Ann) ≤ ENNReal.ofReal V) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hbig : V < ε ^ 2 / (2 * Real.pi) * Real.log (1 / δ)) :
    ∃ ρ ∈ Ioo (δ ^ 2) δ, ∀ w ∈ E, ∀ w' ∈ E, ‖w - 1‖ = ρ → ‖w' - 1‖ = ρ →
      dist (Φ w) (Φ w') < ε := by
  by_contra hcon
  push Not at hcon
  set C := ε ^ 2 / (2 * Real.pi) with hC
  have hCpos : 0 < C := by positivity
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  let G : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal p.1 *
    dens Φ (1 + (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I))
  have hGm : Measurable G := by
    apply Measurable.mul measurable_fst.ennreal_ofReal
    exact (measurable_dens Φ).comp (Continuous.measurable (by fun_prop))
  have hinner : ∀ r ∈ Ioo (δ ^ 2) δ,
      ENNReal.ofReal (C / r) ≤ ∫⁻ θ in Ioo (-Real.pi) Real.pi, G (r, θ) := by
    intro r hr
    obtain ⟨w, hw, w', hw', h1, h2, h3⟩ := hcon r hr
    have hr0 : 0 < r := hδ2.trans hr.1
    have hb := circle_bound Φ hd r hr0 (hr.2.trans hδ1) ε hε w w' hw hw' h1 h2 h3
    have heq : ∀ θ : ℝ, G (r, θ) = ENNReal.ofReal (1 / r) * (ENNReal.ofReal (r ^ 2) *
        dens Φ (1 + (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))) := by
      intro θ
      simp only [G]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (C / r) = ENNReal.ofReal (1 / r) * ENNReal.ofReal C := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      _ ≤ _ := mul_le_mul_right hb _
  have hchain : ENNReal.ofReal (C * Real.log (1 / δ)) ≤ ENNReal.ofReal V := by
    calc ENNReal.ofReal (C * Real.log (1 / δ))
        = ∫⁻ r in Ioo (δ ^ 2) δ, ENNReal.ofReal (C / r) :=
          (lintegral_inv C δ hCpos.le hδ0 hδ1).symm
      _ ≤ ∫⁻ r in Ioo (δ ^ 2) δ, ∫⁻ θ in Ioo (-Real.pi) Real.pi, G (r, θ) :=
          setLIntegral_mono' measurableSet_Ioo hinner
      _ = ∫⁻ p in Ioo (δ ^ 2) δ ×ˢ Ioo (-Real.pi) Real.pi, G p := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hGm.aemeasurable]
      _ ≤ ∫⁻ p in polarCoord.target, G p := by
          apply lintegral_mono_set
          rw [polarCoord_target]
          exact prod_mono (fun r hr => hδ2.trans hr.1) le_rfl
      _ = ∫⁻ z, dens Φ (1 + z) := by
          rw [← Complex.lintegral_comp_polarCoord_symm (fun z => dens Φ (1 + z))]
          congr 1
          funext p
          simp only [G, Complex.polarCoord_symm_apply, smul_eq_mul]
      _ = ∫⁻ w, dens Φ w := lintegral_add_left_eq_self (dens Φ) 1
      _ ≤ volume (Φ '' Ann) := lintegral_dens_le Φ hd hi
      _ ≤ ENNReal.ofReal V := hV
  have := (ENNReal.ofReal_le_ofReal_iff hV0).1 hchain
  linarith

/-- Length–area: around each boundary point there are short crosscuts of small image. -/
theorem length_area (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ E) (hi : Set.InjOn Φ E)
    (hb : Bornology.IsBounded (Φ '' {w | 1 < ‖w‖ ∧ ‖w‖ < 2})) :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ w₀ : ℂ, ‖w₀‖ = 1 → ∀ δ ∈ Set.Ioo 0 δ₀,
      ∃ ρ ∈ Set.Ioo (δ ^ 2) δ, ∀ w ∈ E, ∀ w' ∈ E, ‖w - w₀‖ = ρ → ‖w' - w₀‖ = ρ →
        dist (Φ w) (Φ w') < ε := by
  intro ε hε
  have hfin : volume (Φ '' Ann) ≠ ⊤ := hb.measure_lt_top.ne
  set V := (volume (Φ '' Ann)).toReal with hVdef
  have hV : volume (Φ '' Ann) ≤ ENNReal.ofReal V := (ENNReal.ofReal_toReal hfin).ge
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set C := ε ^ 2 / (2 * Real.pi) with hC
  have hCpos : 0 < C := by positivity
  set K := V / C + 1 with hK
  refine ⟨min (1 / 2) (Real.exp (-K)), lt_min (by norm_num) (Real.exp_pos _), ?_⟩
  intro w₀ hw₀ δ hδ
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ.2 ((min_le_left _ _).trans (by norm_num))
  have hδK : δ < Real.exp (-K) := lt_of_lt_of_le hδ.2 (min_le_right _ _)
  have hlog : K < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_lt_log hδ.1 hδK
    rw [Real.log_exp] at this
    linarith
  have hbig : V < C * Real.log (1 / δ) := by
    have h1 : C * K = V + C := by rw [hK]; field_simp
    have h2 := mul_lt_mul_of_pos_left hlog hCpos
    linarith
  have hw0 : w₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hw₀; exact zero_ne_one hw₀
  have hmul : ∀ u : ℂ, ‖w₀ * u‖ = ‖u‖ := by intro u; rw [norm_mul, hw₀, one_mul]
  set Ψ : ℂ → ℂ := fun u => Φ (w₀ * u) with hΨ
  have hmaps : MapsTo (fun u : ℂ => w₀ * u) E E := by
    intro u hu; show 1 < ‖w₀ * u‖; rw [hmul]; exact hu
  have hΨd : DifferentiableOn ℂ Ψ E := hd.comp (differentiableOn_id.const_mul w₀) hmaps
  have hΨi : Set.InjOn Ψ E := by
    intro u hu v hv h
    exact mul_left_cancel₀ hw0 (hi (hmaps hu) (hmaps hv) h)
  have hΨV : volume (Ψ '' Ann) ≤ ENNReal.ofReal V := by
    refine le_trans (measure_mono ?_) hV
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨w₀ * u, ⟨?_, ?_⟩, rfl⟩
    · show 1 < ‖w₀ * u‖; rw [hmul]; exact hu.1
    · show ‖w₀ * u‖ < 2; rw [hmul]; exact hu.2
  obtain ⟨ρ, hρ, hρ'⟩ := core Ψ hΨd hΨi V hV0 hΨV ε hε δ hδ.1 hδ1 hbig
  refine ⟨ρ, hρ, ?_⟩
  intro w hw w' hw' hr hr'
  have key : ∀ z : ℂ, Ψ (w₀⁻¹ * z) = Φ z := fun z => by
    simp only [hΨ, mul_inv_cancel_left₀ hw0]
  have hnorm : ∀ z : ℂ, ‖w₀⁻¹ * z‖ = ‖z‖ := by
    intro z; rw [norm_mul, norm_inv, hw₀, inv_one, one_mul]
  have hsub : ∀ z : ℂ, ‖w₀⁻¹ * z - 1‖ = ‖z - w₀‖ := by
    intro z
    rw [show w₀⁻¹ * z - 1 = w₀⁻¹ * (z - w₀) by rw [mul_sub, inv_mul_cancel₀ hw0], hnorm]
  rw [← key w, ← key w']
  exact hρ' _ (by show 1 < ‖w₀⁻¹ * w‖; rw [hnorm]; exact hw) _
    (by show 1 < ‖w₀⁻¹ * w'‖; rw [hnorm]; exact hw') (by rw [hsub]; exact hr)
    (by rw [hsub]; exact hr')

end ConformalBoundary.Dev.CT.PartA
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias length_area := ConformalBoundary.Dev.CT.PartA.length_area

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
open Set Metric
namespace ConformalBoundary.Dev.CT.PartS
open ConformalBoundary.Dev.CT
/-- The complement of a closed ball in `ℂ` is connected. -/
theorem isConnected_compl_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (closedBall c r)ᶜ := by
  let f : ℝ × ℝ → ℂ := fun p => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  have heq : (closedBall c r)ᶜ = f '' (Ioi r ×ˢ univ) := by
    ext z
    simp only [mem_compl_iff, mem_closedBall, not_le, mem_image, mem_prod, mem_Ioi,
      mem_univ, and_true, Prod.exists, f]
    constructor
    · intro hz
      refine ⟨‖z - c‖, Complex.arg (z - c), by rwa [← dist_eq_norm], ?_⟩
      rw [Complex.norm_mul_exp_arg_mul_I]
      ring
    · rintro ⟨t, θ, ht, rfl⟩
      rw [dist_eq_norm]
      have : c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - c
          = (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by ring
      rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_of_nonneg (hr.trans ht.le)]
      simpa using ht
  rw [heq]
  exact (isConnected_Ioi.prod isConnected_univ).image f hf.continuousOn

/-- Images of small boundary sectors are small (Janiszewski). -/
theorem sector_small (K : Set ℂ) (hK : OmFacts K)
    (hu : ∀ ε > 0, ∃ η > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < η →
      ∃ C ⊆ K, IsPreconnected C ∧ p ∈ C ∧ q ∈ C ∧ C ⊆ Metric.ball p ε)
    (Φ : ℂ → ℂ) (hΦ : ExtMap K Φ) :
    ∀ ε > 0, ∀ w₀ : ℂ, ‖w₀‖ = 1 → ∃ ρ > 0, ∃ c : ℂ, ∀ w ∈ E, ‖w - w₀‖ < ρ →
      dist (Φ w) c < ε := by
  intro ε hε w₀ hw₀
  obtain ⟨η, hη, hhu⟩ := hu (ε / 4) (by positivity)
  set ε' := min η ε / 8 with hε'
  have hmin : 0 < min η ε := lt_min hη hε
  have hε'pos : 0 < ε' := by positivity
  have hε'η : 2 * ε' < η := by
    have := min_le_left η ε; rw [hε']; linarith
  have hε'ε : ε' ≤ ε / 8 := by
    have := min_le_right η ε; rw [hε']; linarith
  obtain ⟨δ₀, hδ₀, hLA⟩ := length_area Φ hΦ.diff hΦ.inj hΦ.bdd ε' hε'pos
  obtain ⟨ρ, ⟨hρ1, hρ2⟩, hρ⟩ := hLA w₀ hw₀ (min (δ₀ / 2) (1 / 4))
    ⟨lt_min (by positivity) (by norm_num), (min_le_left _ _).trans_lt (by linarith)⟩
  have hρpos : 0 < ρ := lt_of_le_of_lt (sq_nonneg _) hρ1
  have hρ14 : ρ < 1 / 4 := hρ2.trans_le (min_le_right _ _)
  refine ⟨ρ, hρpos, ?_⟩
  have hEopen : IsOpen E := isOpen_lt continuous_const continuous_norm
  set Ω := Om K with hΩdef
  set A : Set ℂ := {w | w ∈ E ∧ ‖w - w₀‖ = ρ} with hAdef
  set Q := Φ '' A with hQdef
  set w₁ : ℂ := w₀ * ((1 + ρ : ℝ) : ℂ) with hw₁
  have hw₁A : w₁ ∈ A := by
    have h1 : w₁ - w₀ = w₀ * ((ρ : ℝ) : ℂ) := by rw [hw₁]; push_cast; ring
    have hn : ‖w₁‖ = 1 + ρ := by
      rw [hw₁, norm_mul, hw₀, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; ring
    refine ⟨?_, ?_⟩
    · show 1 < ‖w₁‖
      rw [hn]; linarith
    · rw [h1, norm_mul, hw₀, Complex.norm_real, Real.norm_of_nonneg hρpos.le]; ring
  set q₀ := Φ w₁ with hq₀
  refine ⟨q₀, ?_⟩
  have hQball : Q ⊆ ball q₀ ε' := by
    rintro _ ⟨w, hw, rfl⟩
    exact hρ w hw.1 w₁ hw₁A.1 hw.2 hw₁A.2
  have hclQ : closure Q ⊆ closedBall q₀ ε' :=
    closure_minimal (hQball.trans ball_subset_closedBall) isClosed_closedBall
  have hQann : Q ⊆ Φ '' {w | 1 < ‖w‖ ∧ ‖w‖ < 2} := by
    refine image_mono ?_
    rintro w ⟨hwE, hwρ⟩
    refine ⟨hwE, ?_⟩
    have := norm_sub_norm_le w w₀
    linarith
  have hQcpt : IsCompact (closure Q) := (hΦ.bdd.subset hQann).isCompact_closure
  have hQΩ : Q ⊆ Ω := by
    rw [hΩdef, ← hΦ.onto]
    exact image_mono fun w hw => hw.1
  have hKΩ : K ⊆ Ωᶜ := fun z hz hzΩ => hzΩ.1 hz
  set Y := closure Q ∩ Ωᶜ with hYdef
  have hYK : Y ⊆ K := by
    rintro y ⟨hyQ, hyΩ⟩
    apply hK.frontier_sub
    rw [hK.isOpen.frontier_eq]
    exact ⟨closure_mono hQΩ hyQ, hyΩ⟩
  -- the connecting continuum inside `K`
  obtain ⟨C, hCcpt, hCK, hCpc, hYC, hCball⟩ : ∃ C : Set ℂ, IsCompact C ∧ C ⊆ K ∧
      IsPreconnected C ∧ Y ⊆ C ∧ C ⊆ closedBall q₀ (3 * ε / 8) := by
    by_cases hY : Y.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hY
      have hy₀q : dist y₀ q₀ ≤ ε' := hclQ hy₀.1
      have key : ∀ y ∈ Y, ∃ C ⊆ K, IsPreconnected C ∧ y₀ ∈ C ∧ y ∈ C ∧
          C ⊆ Metric.ball y₀ (ε / 4) := by
        intro y hy
        refine hhu y₀ (hYK hy₀) y (hYK hy) ?_
        have hyq : dist y q₀ ≤ ε' := hclQ hy.1
        have := dist_triangle_right y₀ y q₀
        linarith
      choose! Cf hCfK hCfpc hCf0 hCfy hCfb using key
      let C0 : Set ℂ := ⋃ y : Y, Cf y
      have hC0b : C0 ⊆ ball y₀ (ε / 4) := iUnion_subset fun y => hCfb y y.property
      refine ⟨closure C0, (isBounded_ball.subset hC0b).isCompact_closure,
        closure_minimal (iUnion_subset fun y => hCfK y y.property) hK.compact.isClosed,
        (isPreconnected_iUnion (s := fun y : Y => Cf y)
          ⟨y₀, mem_iInter.2 fun (y : Y) => hCf0 y.1 y.2⟩
          fun (y : Y) => hCfpc y.1 y.2).closure, ?_, ?_⟩
      · intro y hy
        exact subset_closure (mem_iUnion.2 ⟨⟨y, hy⟩, hCfy y hy⟩)
      · refine (closure_minimal (hC0b.trans ball_subset_closedBall) isClosed_closedBall).trans
          (closedBall_subset_closedBall' ?_)
        linarith
    · rw [not_nonempty_iff_eq_empty] at hY
      refine ⟨∅, isCompact_empty, empty_subset _, isPreconnected_empty, hY ▸ subset_rfl,
        empty_subset _⟩
  set S := closure Q ∪ C with hSdef
  set T := Ωᶜ with hTdef
  have hSball : S ⊆ closedBall q₀ (ε / 2) := by
    apply union_subset
    · exact hclQ.trans (closedBall_subset_closedBall (by linarith))
    · exact hCball.trans (closedBall_subset_closedBall (by linarith))
  have hST : S ∩ T = C := by
    ext x
    constructor
    · rintro ⟨hxS | hxC, hxT⟩
      · exact hYC ⟨hxS, hxT⟩
      · exact hxC
    · intro hx
      exact ⟨Or.inr hx, hKΩ (hCK hx)⟩
  intro w hw hwρ
  by_contra hfar
  push Not at hfar
  obtain ⟨R, hR⟩ := hK.far
  obtain ⟨B, hB⟩ := hΦ.bdd.subset_closedBall 0
  have hB0 : 0 ≤ B := by
    have hmem : Φ (w₀ * ((3 / 2 : ℝ) : ℂ)) ∈ closedBall (0 : ℂ) B := by
      refine hB ⟨_, ⟨?_, ?_⟩, rfl⟩ <;>
        rw [norm_mul, hw₀, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] <;> norm_num
    exact dist_nonneg.trans (mem_closedBall.1 hmem)
  set r : ℝ := max R B + ‖q₀‖ + ε + 1 with hr
  have hrB : B < r := by have := le_max_right R B; have := norm_nonneg q₀; linarith
  have hrR : R < r := by have := le_max_left R B; have := norm_nonneg q₀; linarith
  have hnr : ‖((r : ℝ) : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    have := norm_nonneg q₀; have := le_max_right R B
    linarith
  have hyΩ : ((r : ℝ) : ℂ) ∈ Ω := hR _ (by rw [hnr]; exact hrR)
  have hyΩ' := hyΩ
  rw [hΩdef, ← hΦ.onto] at hyΩ'
  obtain ⟨w', hw'E, hw'y⟩ := hyΩ'
  have hw'2 : 2 ≤ ‖w'‖ := by
    by_contra h
    push Not at h
    have h1 : Φ w' ∈ closedBall (0 : ℂ) B := hB ⟨w', ⟨hw'E, h⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right, hw'y, hnr] at h1
    linarith
  have hw'ρ : ρ < ‖w' - w₀‖ := by
    have := norm_sub_norm_le w' w₀
    linarith
  have hyfar : ε < dist (Φ w') q₀ := by
    rw [hw'y, dist_eq_norm]
    have := norm_sub_norm_le ((r : ℝ) : ℂ) q₀
    rw [hnr] at this
    have := le_max_right R B
    linarith
  have hzS : Φ w ∉ closedBall q₀ (ε / 2) := by
    rw [mem_closedBall, not_le]; linarith
  have hyS : Φ w' ∉ closedBall q₀ (ε / 2) := by
    rw [mem_closedBall, not_le]; linarith
  have hzΩ : Φ w ∈ Ω := by rw [hΩdef, ← hΦ.onto]; exact mem_image_of_mem Φ hw
  have hyΩ2 : Φ w' ∈ Ω := hw'y ▸ hyΩ
  have ha : Φ w ∉ S ∪ T := by
    rintro (h | h)
    · exact hzS (hSball h)
    · exact h hzΩ
  have hb : Φ w' ∉ S ∪ T := by
    rintro (h | h)
    · exact hyS (hSball h)
    · exact h hyΩ2
  have habS : Φ w' ∈ connectedComponentIn Sᶜ (Φ w) :=
    (isConnected_compl_closedBall q₀ (by linarith : (0 : ℝ) ≤ ε / 2)).isPreconnected.subset_connectedComponentIn
      hzS (compl_subset_compl.2 hSball) hyS
  have habT : Φ w' ∈ connectedComponentIn Tᶜ (Φ w) := by
    rw [hTdef, compl_compl]
    exact hK.connected.isPreconnected.subset_connectedComponentIn hzΩ subset_rfl hyΩ2
  have J := janiszewski_compact_preconnected_intersection S T (Φ w) (Φ w')
    (hQcpt.union hCcpt) hK.compl_compact (hST ▸ hCpc) ha hb habS habT
  -- the two sides of the crosscut
  set N : Set ℂ := E ∩ {v | ‖v - w₀‖ < ρ} with hN
  set N' : Set ℂ := E ∩ {v | ρ < ‖v - w₀‖} with hN'
  have hNo : IsOpen N := hEopen.inter (isOpen_lt (by fun_prop) continuous_const)
  have hN'o : IsOpen N' := hEopen.inter (isOpen_lt continuous_const (by fun_prop))
  have hU : IsOpen (Φ '' N) := hΦ.openMap N inter_subset_left hNo
  have hV : IsOpen (Φ '' N') := hΦ.openMap N' inter_subset_left hN'o
  have hdisj : Disjoint (Φ '' N) (Φ '' N') := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba := hΦ.inj hb.1 ha.1 hab
    have h1 : ‖a - w₀‖ < ρ := ha.2
    have h2 : ρ < ‖b - w₀‖ := hb.2
    rw [hba] at h2
    linarith
  have hcover : connectedComponentIn (S ∪ T)ᶜ (Φ w) ⊆ Φ '' N ∪ Φ '' N' := by
    intro p hp
    have hp' : p ∉ S ∪ T := connectedComponentIn_subset _ _ hp
    have hpΩ : p ∈ Ω := by
      by_contra h
      exact hp' (Or.inr h)
    rw [hΩdef, ← hΦ.onto] at hpΩ
    obtain ⟨v, hvE, rfl⟩ := hpΩ
    rcases lt_trichotomy ‖v - w₀‖ ρ with h | h | h
    · exact Or.inl ⟨v, ⟨hvE, h⟩, rfl⟩
    · exact (hp' (Or.inl (Or.inl (subset_closure
        (mem_image_of_mem Φ (show v ∈ A from ⟨hvE, h⟩)))))).elim
    · exact Or.inr ⟨v, ⟨hvE, h⟩, rfl⟩
  have hne : (connectedComponentIn (S ∪ T)ᶜ (Φ w) ∩ Φ '' N).Nonempty :=
    ⟨Φ w, mem_connectedComponentIn ha, mem_image_of_mem Φ (show w ∈ N from ⟨hw, hwρ⟩)⟩
  have hsub := IsPreconnected.subset_left_of_subset_union hU hV hdisj hcover hne
    isPreconnected_connectedComponentIn
  exact Set.disjoint_left.1 hdisj (hsub J) ⟨w', ⟨hw'E, hw'ρ⟩, rfl⟩

end ConformalBoundary.Dev.CT.PartS
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias sector_small := ConformalBoundary.Dev.CT.PartS.sector_small

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT.PartE
open ConformalBoundary.Dev.CT
open Filter Topology Set Metric Real
lemma E_eq : E = (closedBall (0 : ℂ) 1)ᶜ := by
  ext w; simp [E, not_le]

lemma closure_E : closure E = {w : ℂ | 1 ≤ ‖w‖} := by
  rw [E_eq, closure_compl, interior_closedBall _ one_ne_zero]
  ext w; simp [not_lt]

lemma neBot_E {w : ℂ} (hw : 1 ≤ ‖w‖) : (𝓝[E] w).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, closure_E]; exact hw

lemma tendsto_of_hs (Φ : ℂ → ℂ)
    (hs : ∀ ε > 0, ∀ w₀ : ℂ, ‖w₀‖ = 1 → ∃ ρ > 0, ∃ c : ℂ, ∀ w ∈ E, ‖w - w₀‖ < ρ →
      dist (Φ w) c < ε) (w₀ : ℂ) (hw : ‖w₀‖ = 1) : ∃ y, Tendsto Φ (𝓝[E] w₀) (𝓝 y) := by
  have := neBot_E (le_of_eq hw.symm)
  have hC : Cauchy (map Φ (𝓝[E] w₀)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨ρ, hρ, c, hc⟩ := hs (ε / 2) (half_pos hε) w₀ hw
    refine ⟨Φ '' (E ∩ ball w₀ ρ),
      image_mem_map (inter_mem_nhdsWithin _ (ball_mem_nhds _ hρ)), ?_⟩
    rintro _ ⟨x, ⟨hxE, hx⟩, rfl⟩ _ ⟨y, ⟨hyE, hy⟩, rfl⟩
    have h1 := hc x hxE (by rwa [mem_ball, dist_eq_norm] at hx)
    have h2 := hc y hyE (by rwa [mem_ball, dist_eq_norm] at hy)
    calc dist (Φ x) (Φ y) ≤ dist (Φ x) c + dist (Φ y) c := dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε
  obtain ⟨y, hy⟩ := CompleteSpace.complete hC
  exact ⟨y, hy⟩

/-- `|Φ w| → ∞` as `|w| → ∞`, from the Laurent form. -/
lemma growth (K : Set ℂ) (Φ : ℂ → ℂ) (hΦ : ExtMap K Φ) (B : ℝ) :
    ∃ R : ℝ, ∀ w ∈ E, R < ‖w‖ → B ≤ ‖Φ w‖ := by
  obtain ⟨a, k, hk, hk0, hΦk⟩ := hΦ.laurent
  have hkc : ContinuousAt k 0 :=
    (hk.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt
  obtain ⟨δ, hδ, hδk⟩ := Metric.continuousAt_iff.mp hkc 1 one_pos
  set M := ‖k 0‖ + 1 with hM_def
  have hM : 0 < M := by positivity
  refine ⟨max (1 / δ) (M * (‖a‖ + B)), fun w hwE hw => ?_⟩
  have hw1 : 1 / δ < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
  have hw2 : M * (‖a‖ + B) < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hw
  have hwE' : 1 < ‖w‖ := hwE
  have hwpos : 0 < ‖w‖ := by linarith
  have hζ : ‖1 / w‖ < δ := by
    rw [norm_div, norm_one, div_lt_iff₀ hwpos]
    rw [div_lt_iff₀ hδ] at hw1
    linarith [mul_comm δ ‖w‖]
  have hζ1 : (1 / w) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, norm_one, div_lt_iff₀ hwpos]; linarith
  have hkb : ‖k (1 / w)‖ < M := by
    have h := hδk (by rwa [dist_zero_right])
    rw [dist_eq_norm] at h
    have := norm_sub_norm_le (k (1 / w)) (k 0)
    rw [hM_def]; linarith
  have hkpos : 0 < ‖k (1 / w)‖ := norm_pos_iff.mpr (hk0 _ hζ1)
  rw [hΦk w hwE]
  have h1 : ‖w‖ / M ≤ ‖w / k (1 / w)‖ := by
    rw [norm_div]; exact div_le_div_of_nonneg_left hwpos.le hkpos hkb.le
  have h2 : ‖a‖ + B < ‖w‖ / M := by
    rw [lt_div_iff₀ hM]; linarith [mul_comm M (‖a‖ + B)]
  have h3 : ‖w / k (1 / w)‖ ≤ ‖a + w / k (1 / w)‖ + ‖a‖ := by
    have := norm_sub_le (a + w / k (1 / w)) a
    rwa [add_sub_cancel_left] at this
  linarith

/-- Continuous extension to the closed exterior disk, mapping the circle onto the frontier. -/
theorem extend (K : Set ℂ) (hK : OmFacts K) (Φ : ℂ → ℂ) (hΦ : ExtMap K Φ)
    (hs : ∀ ε > 0, ∀ w₀ : ℂ, ‖w₀‖ = 1 → ∃ ρ > 0, ∃ c : ℂ, ∀ w ∈ E, ‖w - w₀‖ < ρ →
      dist (Φ w) c < ε) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ {w | 1 ≤ ‖w‖} ∧ Set.EqOn Ψ Φ E ∧
      Ψ '' Metric.sphere 0 1 = frontier (Om K) := by
  have hcont : ContinuousOn Φ E := hΦ.diff.continuousOn
  have hlim : ∀ x ∈ {w : ℂ | 1 ≤ ‖w‖}, ∃ y, Tendsto Φ (𝓝[E] x) (𝓝 y) := by
    intro x hx
    rcases (show (1 : ℝ) ≤ ‖x‖ from hx).lt_or_eq with h | h
    · exact ⟨Φ x, hcont x h⟩
    · exact tendsto_of_hs Φ hs x h.symm
  have hΨc : ContinuousOn (extendFrom E Φ) {w | 1 ≤ ‖w‖} :=
    continuousOn_extendFrom (by rw [closure_E]) hlim
  have hΨe : EqOn (extendFrom E Φ) Φ E := fun x hx => extendFrom_extends hcont x hx
  have hT : ∀ x : ℂ, 1 ≤ ‖x‖ → Tendsto Φ (𝓝[E] x) (𝓝 (extendFrom E Φ x)) :=
    fun x hx => tendsto_extendFrom (hlim x hx)
  refine ⟨extendFrom E Φ, hΨc, hΨe, ?_⟩
  generalize extendFrom E Φ = Ψ at hΨc hΨe hT
  rw [hK.isOpen.frontier_eq]
  apply Subset.antisymm
  · rintro _ ⟨w₀, hw₀, rfl⟩
    have hw : ‖w₀‖ = 1 := by simpa using hw₀
    have := neBot_E hw.ge
    have hmap : ∀ᶠ w in 𝓝[E] w₀, Φ w ∈ Om K :=
      eventually_nhdsWithin_of_forall fun w hw => hΦ.onto ▸ mem_image_of_mem Φ hw
    refine ⟨mem_closure_of_tendsto (hT w₀ hw.ge) hmap, ?_⟩
    intro hmem
    rw [← hΦ.onto] at hmem
    obtain ⟨w₁, hw₁, hΦw₁⟩ := hmem
    have hw₁' : 1 < ‖w₁‖ := hw₁
    set r := (‖w₁‖ - 1) / 2 with hr_def
    have hr : 0 < r := by rw [hr_def]; linarith
    have hNE : ball w₁ r ⊆ E := by
      intro w hw'
      have := norm_sub_norm_le w₁ w
      rw [mem_ball, dist_eq_norm, norm_sub_rev] at hw'
      show 1 < ‖w‖
      rw [hr_def] at hw'
      linarith
    have hopen := hΦ.openMap _ hNE isOpen_ball
    have h1 : ∀ᶠ w in 𝓝[E] w₀, Φ w ∈ Φ '' ball w₁ r :=
      hT w₀ hw.ge (hopen.mem_nhds ⟨w₁, mem_ball_self hr, hΦw₁⟩)
    have h2 : ∀ᶠ w in 𝓝[E] w₀, w ∈ E ∧ w ∈ ball w₀ r :=
      (eventually_nhdsWithin_of_forall fun w hw => hw).and (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hr))
    obtain ⟨w, ⟨w', hw', hΦw'⟩, hwE, hwb⟩ := (h1.and h2).exists
    have hww : w' = w := hΦ.inj (hNE hw') hwE hΦw'
    subst hww
    rw [mem_ball] at hw' hwb
    have := dist_triangle w₁ w' w₀
    have h3 : ‖w₁‖ - 1 ≤ dist w₁ w₀ := by
      rw [dist_eq_norm]
      have := norm_sub_norm_le w₁ w₀
      rw [hw] at this; exact this
    rw [dist_comm] at hw'
    rw [hr_def] at hw' hwb
    linarith
  · rintro z ⟨hzc, hzn⟩
    obtain ⟨R, hR⟩ := growth K Φ hΦ (‖z‖ + 1)
    set C := {w : ℂ | 1 ≤ ‖w‖} ∩ closedBall 0 R with hC_def
    have hCc : IsCompact C :=
      (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_norm)
    have hC2 : IsCompact (Ψ '' C) := hCc.image_of_continuousOn (hΨc.mono inter_subset_left)
    have hsub : ball z 1 ∩ Om K ⊆ Ψ '' C := by
      rintro y ⟨hyb, hy⟩
      rw [← hΦ.onto] at hy
      obtain ⟨w, hwE, rfl⟩ := hy
      refine ⟨w, ⟨(show (1 : ℝ) < ‖w‖ from hwE).le, ?_⟩, hΨe hwE⟩
      rw [mem_closedBall, dist_zero_right]
      by_contra hcon
      push Not at hcon
      have h1 := hR w hwE hcon
      rw [mem_ball, dist_eq_norm] at hyb
      have := norm_sub_norm_le (Φ w) z
      linarith
    have hzC : z ∈ Ψ '' C := by
      have : z ∈ closure (ball z 1 ∩ Om K) :=
        isOpen_ball.inter_closure ⟨mem_ball_self one_pos, hzc⟩
      exact hC2.isClosed.closure_subset_iff.mpr hsub this
    obtain ⟨w, ⟨hw1, -⟩, rfl⟩ := hzC
    refine ⟨w, ?_, rfl⟩
    rcases (show (1 : ℝ) ≤ ‖w‖ from hw1).lt_or_eq with h | h
    · exact absurd (by rw [← hΦ.onto]; exact ⟨w, h, (hΨe h).symm⟩) hzn
    · simpa using h.symm

end ConformalBoundary.Dev.CT.PartE
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias extend := ConformalBoundary.Dev.CT.PartE.extend

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT.PartE
open ConformalBoundary.Dev.CT
open Filter Topology Set Metric Real
/-- Every point of the unit circle is rotated into the arc `e^{-iθ}`, `θ ∈ [α, β]`, by some
power of `e^{2πi/N}`. -/
lemma arc_cover (α β : ℝ) (N : ℕ) (hN : 0 < N) (hd : 2 * π / N < β - α) (ζ : ℂ)
    (hζ : ‖ζ‖ = 1) :
    ∃ j ∈ Finset.range N, ∃ θ ∈ Icc α β,
      Complex.exp (((2 * π / N : ℝ) : ℂ) * Complex.I) ^ j * ζ =
        Complex.exp (-(θ * Complex.I)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set d : ℝ := 2 * π / N with hd_def
  have hdpos : 0 < d := by rw [hd_def]; positivity
  set φ : ℝ := -Complex.arg ζ with hφ
  set m : ℤ := ⌊(φ - α) / d⌋ with hm_def
  have hm1 : (m : ℝ) ≤ (φ - α) / d := Int.floor_le _
  have hm2 : (φ - α) / d < m + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hdpos] at hm1
  rw [div_lt_iff₀ hdpos] at hm2
  have hm3 := add_mul (m : ℝ) 1 d
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmod0 : 0 ≤ m % N := Int.emod_nonneg _ hNz
  have hmodlt : m % N < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
  have hj : (((m % N).toNat : ℕ) : ℤ) = m % N := Int.toNat_of_nonneg hmod0
  refine ⟨(m % N).toNat, ?_, φ - m * d, ⟨by linarith, by linarith⟩, ?_⟩
  · rw [Finset.mem_range]; omega
  · have hζe : ζ = Complex.exp (Complex.arg ζ * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
      rw [hζ]; simp
    rw [hζe, ← Complex.exp_nat_mul, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-(m / N), ?_⟩
    have hsplit : m = ((m % N).toNat : ℤ) + N * (m / N) := by
      rw [hj]; exact (Int.emod_add_mul_ediv m N).symm
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hmC : (m : ℂ) = (((m % N).toNat : ℕ) : ℂ) + (N : ℂ) * ((m / N : ℤ) : ℂ) := by
      exact_mod_cast hsplit
    rw [hφ, hd_def]
    push_cast
    rw [hmC]
    field_simp
    ring

/-- The boundary values are constant on no arc (rotation product and maximum modulus). -/
theorem light (K : Set ℂ) (Φ : ℂ → ℂ) (hΦ : ExtMap K Φ) (Ψ : ℂ → ℂ)
    (hc : ContinuousOn Ψ {w | 1 ≤ ‖w‖}) (he : Set.EqOn Ψ Φ E) :
    ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β,
      Ψ (Complex.exp (θ * Complex.I)) ≠ Ψ (Complex.exp (α * Complex.I)) := by
  intro α β hαβ
  by_contra hcon
  push Not at hcon
  obtain ⟨a, k, hk, hk0, hΦk⟩ := hΦ.laurent
  obtain ⟨p, hp⟩ : ∃ p : ℂ, p = Ψ (Complex.exp (α * Complex.I)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = fun ζ => ζ * (a - p) + 1 / k ζ := ⟨_, rfl⟩
  obtain ⟨Hc, hHc⟩ : ∃ Hc : ℂ → ℂ,
      Hc = fun ζ => if ζ = 0 then 1 / k 0 else ζ * (Ψ (1 / ζ) - p) := ⟨_, rfl⟩
  have hHd : DifferentiableOn ℂ H (ball 0 1) := by
    rw [hH]
    exact (differentiableOn_id.mul_const _).add ((differentiableOn_const 1).div hk hk0)
  have hHcH : EqOn Hc H (ball 0 1) := by
    intro ζ hζ
    have hkζ := hk0 ζ hζ
    rw [hHc, hH]
    dsimp only
    split_ifs with h0
    · subst h0; simp
    · have hE : 1 / ζ ∈ E := by
        show 1 < ‖1 / ζ‖
        rw [mem_ball_zero_iff] at hζ
        rw [norm_div, norm_one, lt_div_iff₀ (norm_pos_iff.mpr h0)]; linarith
      rw [he hE, hΦk _ hE, one_div_one_div]
      field_simp
      ring
  have hHcc : ContinuousOn Hc (closedBall 0 1) := by
    intro ζ hζ
    by_cases h0 : ζ = 0
    · subst h0
      have hH0 : ContinuousAt H 0 :=
        (hHd.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt
      have : Hc =ᶠ[𝓝 0] H := Filter.eventually_of_mem (ball_mem_nhds 0 one_pos) hHcH
      exact (hH0.congr this.symm).continuousWithinAt
    · have hG : ContinuousOn (fun ζ : ℂ => ζ * (Ψ (1 / ζ) - p)) (closedBall 0 1 ∩ {0}ᶜ) := by
        refine continuousOn_id.mul ((hc.comp (continuousOn_const.div continuousOn_id
          fun x hx => hx.2) ?_).sub continuousOn_const)
        intro x hx
        have h1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx.1
        have h2 : 0 < ‖x‖ := norm_pos_iff.mpr hx.2
        show 1 ≤ ‖1 / x‖
        rw [norm_div, norm_one, le_div_iff₀ h2]; linarith
      have hHcG : ContinuousOn Hc (closedBall 0 1 ∩ {0}ᶜ) :=
        hG.congr fun x hx => by rw [hHc]; exact if_neg hx.2
      exact (continuousWithinAt_inter (isOpen_compl_singleton.mem_nhds h0)).mp
        (hHcG ζ ⟨hζ, h0⟩)
  have hzero : ∀ θ ∈ Icc α β, Hc (Complex.exp (-(θ * Complex.I))) = 0 := by
    intro θ hθ
    rw [hHc]
    dsimp only
    rw [if_neg (Complex.exp_ne_zero _), one_div, ← Complex.exp_neg, neg_neg, hcon θ hθ, ← hp,
      sub_self, mul_zero]
  -- the rotation product
  have hβα : 0 < β - α := sub_pos.mpr hαβ
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * π / (β - α))
  have hNpos : 0 < N := by
    have : 0 < 2 * π / (β - α) := by positivity
    exact_mod_cast this.trans hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hd : 2 * π / N < β - α := by
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hβα] at hN
    linarith [mul_comm (β - α) (N : ℝ)]
  set ω := Complex.exp (((2 * π / N : ℝ) : ℂ) * Complex.I) with hω_def
  have hω : ∀ j : ℕ, ‖ω ^ j‖ = 1 := by
    intro j; rw [norm_pow, hω_def, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hmapc : ∀ j : ℕ, MapsTo (fun ζ => ω ^ j * ζ) (closedBall 0 1) (closedBall 0 1) := by
    intro j ζ hζ
    simp only [mem_closedBall_zero_iff, norm_mul, hω] at hζ ⊢
    linarith
  have hmapb : ∀ j : ℕ, MapsTo (fun ζ => ω ^ j * ζ) (ball 0 1) (ball 0 1) := by
    intro j ζ hζ
    simp only [mem_ball_zero_iff, norm_mul, hω] at hζ ⊢
    linarith
  set P : ℂ → ℂ := fun ζ => ∏ j ∈ Finset.range N, Hc (ω ^ j * ζ) with hP_def
  have hPc : ContinuousOn P (closedBall 0 1) :=
    continuousOn_finsetProd _ fun j _ =>
      hHcc.comp (continuousOn_const.mul continuousOn_id) (hmapc j)
  have hPd : DifferentiableOn ℂ P (ball 0 1) := by
    have : DifferentiableOn ℂ (fun ζ => ∏ j ∈ Finset.range N, H (ω ^ j * ζ)) (ball 0 1) :=
      DifferentiableOn.fun_finsetProd fun j _ =>
        hHd.comp ((differentiableOn_const _).mul differentiableOn_id) (hmapb j)
    exact this.congr fun ζ hζ => Finset.prod_congr rfl fun j _ => hHcH (hmapb j hζ)
  have hDC : DiffContOnCl ℂ P (ball 0 1) :=
    ⟨hPd, by rw [closure_ball 0 one_ne_zero]; exact hPc⟩
  have hle : ‖P 0‖ ≤ 0 := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hDC ?_
      (subset_closure (mem_ball_self one_pos))
    intro ζ hζ
    rw [frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hζ
    obtain ⟨j, hj, θ, hθ, heq⟩ := arc_cover α β N hNpos hd ζ hζ
    have : P ζ = 0 := Finset.prod_eq_zero hj (by rw [heq]; exact hzero θ hθ)
    rw [this, norm_zero]
  have hP0 : P 0 = (1 / k 0) ^ N := by
    rw [hP_def]
    simp only [mul_zero]
    rw [Finset.prod_const, Finset.card_range, hHc]
    simp
  have hk00 : k 0 ≠ 0 := hk0 0 (mem_ball_self one_pos)
  have : P 0 ≠ 0 := by
    rw [hP0]; exact pow_ne_zero _ (one_div_ne_zero hk00)
  exact this (norm_le_zero_iff.mp hle)

end ConformalBoundary.Dev.CT.PartE
end

section
set_option autoImplicit false
namespace ConformalBoundary.Dev.CT
alias light := ConformalBoundary.Dev.CT.PartE.light

theorem caratheodory_torhorst_exterior_dev (γ : unitInterval → ℂ)
    (continuous : Continuous γ) (nondegenerate : ∃ a b, γ a ≠ γ b) :
    ∃ Φ : ℂ → ℂ,
      ContinuousOn Φ {w | 1 ≤ ‖w‖} ∧
      DifferentiableOn ℂ Φ {w | 1 < ‖w‖} ∧
      Set.InjOn Φ {w | 1 < ‖w‖} ∧
      Φ '' {w | 1 < ‖w‖} = {z | z ∉ Set.range γ ∧
        ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)} ∧
      Φ '' Metric.sphere 0 1 = frontier {z | z ∉ Set.range γ ∧
        ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)} ∧
      ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β,
        Φ (Complex.exp (θ * Complex.I)) ≠ Φ (Complex.exp (α * Complex.I)) := by
  have hK := om_facts γ continuous nondegenerate
  obtain ⟨Φ, hΦ⟩ := exists_extMap _ hK (compl_connected γ continuous hK)
  have hs := sector_small _ hK (ulc γ continuous) Φ hΦ
  obtain ⟨Ψ, hc, he, hfr⟩ := extend _ hK Φ hΦ hs
  have hE : IsOpen E := isOpen_lt continuous_const continuous_norm
  refine ⟨Ψ, hc, ?_, ?_, ?_, hfr, light _ Φ hΦ Ψ hc he⟩
  · exact (hΦ.diff.congr fun w hw => he hw)
  · exact (hΦ.inj.congr fun w hw => (he hw).symm)
  · have : Ψ '' E = Φ '' E := Set.image_congr fun w hw => he hw
    exact this.trans hΦ.onto

end ConformalBoundary.Dev.CT
end

section
set_option autoImplicit false
namespace ConformalBoundary
theorem chk_caratheodory_torhorst_exterior (γ : unitInterval → ℂ)
    (continuous : Continuous γ) (nondegenerate : ∃ a b, γ a ≠ γ b) :
    ∃ Φ : ℂ → ℂ,
      ContinuousOn Φ {w | 1 ≤ ‖w‖} ∧
      DifferentiableOn ℂ Φ {w | 1 < ‖w‖} ∧
      Set.InjOn Φ {w | 1 < ‖w‖} ∧
      Φ '' {w | 1 < ‖w‖} = {z | z ∉ Set.range γ ∧
        ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)} ∧
      Φ '' Metric.sphere 0 1 = frontier {z | z ∉ Set.range γ ∧
        ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)} ∧
      ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β,
        Φ (Complex.exp (θ * Complex.I)) ≠ Φ (Complex.exp (α * Complex.I)) :=
  ConformalBoundary.Dev.CT.caratheodory_torhorst_exterior_dev γ continuous nondegenerate

end ConformalBoundary
end

theorem solution : type_of% @ConformalBoundary.chk_caratheodory_torhorst_exterior :=
  @ConformalBoundary.chk_caratheodory_torhorst_exterior
