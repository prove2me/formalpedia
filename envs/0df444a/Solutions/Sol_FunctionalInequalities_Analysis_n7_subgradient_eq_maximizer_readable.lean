-- Prove2me | solution 1 for FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:46.433138+00:00
-- url     : https://prove2.me/submissions/8fdd005f-26dd-454e-9183-ab7611cc00cf

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_convexOn_truncatedConjugate_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F3TruncatedConjugateSubgradients
open scoped RealInnerProductSpace Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.n7_isClosed_bad_maximizers [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) {C : Set E} (hC : IsClosed C) :
    IsClosed {p : E | ∃ x ∈ closedBall (0 : E) M,
      x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
  let B := closedBall (0 : E) M
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 M)
  have hT : Continuous (truncatedConjugate u M) :=
    continuousOn_univ.mp ((convexOn_truncatedConjugate_readable hu hM).continuousOn isOpen_univ)
  let D : Set (B × E) :=
    {q | (q.1 : E) ∈ C ∧ truncatedConjugate u M q.2 = ⟪q.2, (q.1 : E)⟫ - u q.1}
  have hD : IsClosed D :=
    (hC.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isClosed_eq (hT.comp continuous_snd)
        ((continuous_snd.inner (continuous_subtype_val.comp continuous_fst)).sub
          (hu.comp (continuous_subtype_val.comp continuous_fst))))
  have he : Prod.snd '' D =
      {p : E | ∃ x ∈ closedBall (0 : E) M,
        x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hx, rfl⟩
      exact ⟨x, x.property, hx⟩
    · rintro ⟨x, hx, hc, he⟩
      exact ⟨(⟨x, hx⟩, p), ⟨hc, he⟩, rfl⟩
  rw [← he]
  exact isClosedMap_snd_of_compactSpace D hD
private lemma FunctionalInequalities.Analysis.n7_support_min {u : E → ℝ} {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    IsMinOn (fun y => u y - ⟪p, y⟫) univ x := by
  intro y _
  have h := hp y
  rw [inner_sub_right] at h
  dsimp
  linarith
private lemma FunctionalInequalities.Analysis.n7_conjugate_eq_of_support {u : E → ℝ} {M : ℝ} {x p : E}
    (hx : x ∈ closedBall (0 : E) M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    truncatedConjugate u M p = ⟪p, x⟫ - u x := by
  have hb : ∀ y, ⟪p, y⟫ - u y ≤ ⟪p, x⟫ - u x := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h
    linarith
  apply le_antisymm
  · exact csSup_le ⟨_, ⟨x, hx, rfl⟩⟩ (by
      rintro _ ⟨y, _, rfl⟩
      exact hb y)
  · exact le_csSup ⟨_, by
      rintro _ ⟨y, _, rfl⟩
      exact hb y⟩ ⟨x, hx, rfl⟩
/-- For strictly convex `u`, a subgradient `p` at a point `x` of the open ball has `x` as its only ball
maximiser. -/
theorem FunctionalInequalities.Analysis.eq_of_truncatedConjugate_eq_of_subgradient [FiniteDimensional ℝ E] {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} {x p : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {x' : E} (hx' : x' ∈ closedBall (0 : E) M)
    (heq : truncatedConjugate u M p = ⟪p, x'⟫ - u x') : x' = x := by
  have hxeq := n7_conjugate_eq_of_support (mem_closedBall_zero_iff.mpr hx.le) hp
  have hp' : ∀ y, u x' + ⟪p, y - x'⟫ ≤ u y := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h ⊢
    linarith [heq, hxeq]
  exact (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
    (n7_support_min hp') (n7_support_min hp)
    ((subset_univ (closedBall (0 : E) M)) hx') (mem_univ x)
section FiniteDimensional
variable [FiniteDimensional ℝ E]
 lemma solution {u : E → ℝ}
    (hu : Continuous u) (hstrict : StrictConvexOn ℝ univ u)
    {M : ℝ} (hM : 0 ≤ M) {p x g : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (heq : FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x)
    (hg : ∀ q, FunctionalInequalities.Analysis.truncatedConjugate u M p + ⟪g, q - p⟫ ≤ FunctionalInequalities.Analysis.truncatedConjugate u M q) :
    g = x := by
  classical
  by_contra hne
  let v := g - x
  have hv : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  have hgap : ⟪v, x⟫ < ⟪v, g⟫ := by
    have hh : ⟪v, v⟫ = ⟪v, g⟫ - ⟪v, x⟫ := by
      dsimp [v]
      rw [inner_sub_right]
    linarith
  let c : ℝ := (⟪v, x⟫ + ⟪v, g⟫) / 2
  have hxc : ⟪v, x⟫ < c := by dsimp [c]; linarith
  have hcg : c < ⟪v, g⟫ := by dsimp [c]; linarith
  let C : Set E := {z | c ≤ ⟪v, z⟫}
  let A : Set E := {q | ∃ z ∈ closedBall (0 : E) M,
    z ∈ C ∧ FunctionalInequalities.Analysis.truncatedConjugate u M q = ⟪q, z⟫ - u z}
  have hA : IsClosed A :=
    FunctionalInequalities.Analysis.n7_isClosed_bad_maximizers hu hM
      (isClosed_le continuous_const (continuous_const.inner continuous_id))
  have hpA : p ∈ Aᶜ := by
    rintro ⟨z, hz, hc, hzmax⟩
    have hzx := FunctionalInequalities.Analysis.eq_of_truncatedConjugate_eq_of_subgradient hstrict hx hp hz hzmax
    subst z
    exact (not_le_of_gt hxc) hc
  have hpath : Continuous (fun t : ℝ => p + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun t : ℝ => p + t • v) ⁻¹' Aᶜ ∈ 𝓝 (0 : ℝ) :=
    hpath.continuousAt.preimage_mem_nhds
      (hA.isOpen_compl.mem_nhds (by simpa only [zero_smul, add_zero] using hpA))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htε : t < ε := by dsimp [t]; linarith
  have hqA : p + t • v ∈ Aᶜ := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htε
  obtain ⟨z, hz, hzmax⟩ := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM (p + t • v)).1
  have hzc : ⟪v, z⟫ < c := by
    by_contra hn
    exact hqA ⟨z, hz, le_of_not_gt hn, hzmax⟩
  have hbase := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).2 z hz
  have hsub := hg (p + t • v)
  rw [hzmax, add_sub_cancel_left, inner_smul_right] at hsub
  rw [inner_add_left, real_inner_smul_left] at hsub
  have hgv : ⟪g, v⟫ = ⟪v, g⟫ := real_inner_comm v g
  have hle : t * ⟪v, g⟫ ≤ t * ⟪v, z⟫ := by
    rw [heq] at hbase hsub
    rw [hgv] at hsub
    linarith
  have hgz : ⟪v, g⟫ ≤ ⟪v, z⟫ := (mul_le_mul_iff_right₀ ht).mp hle
  linarith
