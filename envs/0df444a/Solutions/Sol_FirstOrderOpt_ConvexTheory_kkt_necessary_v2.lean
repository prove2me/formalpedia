-- Prove2me | solution 1 for FirstOrderOpt.ConvexTheory.kkt_necessary_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:35:23.273648+00:00
-- url     : https://prove2.me/submissions/4f968c68-6276-49b3-bd6e-d3a6d2736605

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

set_option autoImplicit false

open scoped RealInnerProductSpace

lemma cvxRay {a b u : ℝ} (h : ∀ k : ℝ, 0 ≤ k → u ≤ a + -k * b) : b ≤ 0 := by
  by_contra hb
  push Not at hb
  have h0 := h 0 le_rfl
  have h1 := h ((a - u + 1) / b) (div_nonneg (by linarith) hb.le)
  rw [neg_mul, div_mul_cancel₀ _ hb.ne'] at h1
  linarith

lemma cvxLine {a b u : ℝ} (h : ∀ k : ℝ, u ≤ a + k * b) : b = 0 := by
  by_contra hb
  have h1 := h ((u - a - 1) / b)
  rw [div_mul_cancel₀ _ hb] at h1
  linarith

lemma cvxDecomp {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : StrongDual ℝ (ℝ × (Fin m → ℝ) × E)) (t : ℝ) (σ : Fin m → ℝ) (v : E) :
    ℓ (t, σ, v) = t * ℓ (1, 0, 0) + ∑ i, σ i * ℓ (0, Pi.single i 1, 0) + ℓ (0, 0, v) := by
  have hv : ((t, σ, v) : ℝ × (Fin m → ℝ) × E) =
      t • ((1 : ℝ), (0 : Fin m → ℝ), (0 : E)) +
      ∑ i, σ i • ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : E)) +
      ((0 : ℝ), (0 : Fin m → ℝ), v) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [Prod.fst_sum]
    · funext k
      simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [hv, map_add, map_add, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul]

lemma cvxCore {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (c : ℝ) (barx : EuclideanSpace ℝ (Fin n)) (hbarxX : barx ∈ X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0)
    (hfeas : ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → c ≤ f x)
    (hloc : ∀ᶠ v in nhds (0 : EuclideanSpace ℝ (Fin n)), ∃ x ∈ X, f x < f barx + 1 / 2 ∧
        (∀ i, g i x < g i barx / 2) ∧ ∀ j, h j x = inner ℝ (w j) v) :
    ∃ lam : Fin m → ℝ, ∃ y : Fin p → ℝ, (∀ i, 0 ≤ lam i) ∧
      ∀ x ∈ X, c ≤ f x + ∑ i, lam i * g i x + ∑ j, y j * h j x := by
  let A : Set (ℝ × (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) :=
    {q | ∃ x ∈ X, f x ≤ q.1 ∧ (∀ i, g i x ≤ q.2.1 i) ∧ ∀ j, h j x = inner ℝ (w j) q.2.2}
  let B : Set (ℝ × (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) :=
    {q | q.1 < c ∧ (∀ i, q.2.1 i ≤ 0) ∧ ∀ j, inner ℝ (w j) q.2.2 = 0}
  have hAconv : Convex ℝ A := by
    refine convex_iff_forall_pos.2 ?_
    intro q1 hq1 q2 hq2 a μ ha hμ hab
    obtain ⟨x1, hx1, hf1, hg1, hh1⟩ := hq1
    obtain ⟨x2, hx2, hf2, hg2, hh2⟩ := hq2
    refine ⟨a • x1 + μ • x2, hXconv hx1 hx2 ha.le hμ.le hab, ?_, fun i => ?_, fun j => ?_⟩
    · have := hfconv.2 hx1 hx2 ha.le hμ.le hab
      simp only [smul_eq_mul] at this
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith
    · have := (hgconv i).2 hx1 hx2 ha.le hμ.le hab
      simp only [smul_eq_mul] at this
      simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      nlinarith [hg1 i, hg2 i]
    · simp only [Prod.snd_add, Prod.smul_snd, inner_add_right, inner_smul_right, ← hh1 j,
        ← hh2 j, hh, inner_add_right, inner_smul_right]
      linear_combination (-(b j)) * hab
  have hBconv : Convex ℝ B := by
    refine convex_iff_forall_pos.2 ?_
    intro q1 hq1 q2 hq2 a μ ha hμ hab
    obtain ⟨h1, h2, h3⟩ := hq1
    obtain ⟨k1, k2, k3⟩ := hq2
    refine ⟨?_, fun i => ?_, fun j => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have e1 := mul_lt_mul_of_pos_left h1 ha
      have e2 := mul_lt_mul_of_pos_left k1 hμ
      have e3 : a * c + μ * c = c := by rw [← add_mul, hab, one_mul]
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      nlinarith [h2 i, k2 i]
    · simp only [Prod.snd_add, Prod.smul_snd, inner_add_right, inner_smul_right, h3 j, k3 j]
      ring
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    rintro q ⟨x, hx, hfx, hgx, hhx⟩ ⟨hq1, hq2, hq3⟩
    have := hfeas x hx (fun i => (hgx i).trans (hq2 i)) (fun j => (hhx j).trans (hq3 j))
    linarith
  have hP0 : ((f barx + 1 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) ∈
      interior A := by
    rw [mem_interior_iff_mem_nhds]
    have t1 : ∀ᶠ q in nhds ((f barx + 1 : ℝ), (0 : Fin m → ℝ),
        (0 : EuclideanSpace ℝ (Fin n))), f barx + 1 / 2 < q.1 :=
      (continuous_fst.tendsto _).eventually (lt_mem_nhds (by norm_num))
    have t2 : ∀ᶠ q in nhds ((f barx + 1 : ℝ), (0 : Fin m → ℝ),
        (0 : EuclideanSpace ℝ (Fin n))), ∀ i, g i barx / 2 < q.2.1 i := by
      rw [Filter.eventually_all]
      intro i
      have hc : Continuous (fun q : ℝ × (Fin m → ℝ) × EuclideanSpace ℝ (Fin n) => q.2.1 i) :=
        (continuous_apply i).comp (continuous_fst.comp continuous_snd)
      exact (hc.tendsto _).eventually (lt_mem_nhds (by simp; linarith [hbarx_g i]))
    have t3 : ∀ᶠ q in nhds ((f barx + 1 : ℝ), (0 : Fin m → ℝ),
        (0 : EuclideanSpace ℝ (Fin n))), ∃ x ∈ X, f x < f barx + 1 / 2 ∧
        (∀ i, g i x < g i barx / 2) ∧ ∀ j, h j x = inner ℝ (w j) q.2.2 := by
      have hc : Filter.Tendsto (fun q : ℝ × (Fin m → ℝ) × EuclideanSpace ℝ (Fin n) => q.2.2)
          (nhds ((f barx + 1 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))))
          (nhds (0 : EuclideanSpace ℝ (Fin n))) :=
        (continuous_snd.comp continuous_snd).tendsto _
      exact hc.eventually hloc
    filter_upwards [t1, t2, t3] with q hq1 hq2 hq3
    obtain ⟨x, hx, hfx, hgx, hhx⟩ := hq3
    exact ⟨x, hx, by linarith, fun i => by linarith [hgx i, hq2 i], hhx⟩
  obtain ⟨ℓ, u, hℓA, hℓB⟩ := geometric_hahn_banach_open hAconv.interior isOpen_interior hBconv
    (Disjoint.mono_left interior_subset hdisj)
  have hAle : ∀ a ∈ A, ℓ a ≤ u := by
    intro a ha
    have hne : (interior A).Nonempty := ⟨_, hP0⟩
    apply closure_minimal (fun x hx => le_of_lt (hℓA x hx)) (isClosed_Iic.preimage ℓ.continuous)
    simpa [hAconv.closure_interior_eq_closure_of_nonempty_interior hne] using subset_closure ha
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = ℓ ((1 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) :=
    ⟨_, rfl⟩
  have hdec0 : ∀ t : ℝ, ℓ (t, (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) = t * α := by
    intro t
    have : ((t, (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) :
        ℝ × (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) =
        t • ((1 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) := by simp
    rw [this, map_smul, smul_eq_mul, hαdef]
  have hbarxc : c ≤ f barx := hfeas barx hbarxX (fun i => (hbarx_g i).le) hbarx_h
  have hαneg : α < 0 := by
    have e1 := hℓA _ hP0
    have e2 := hℓB ((c - 1 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n)))
      ⟨by simp, fun i => by simp, fun j => by simp⟩
    rw [hdec0] at e1 e2
    nlinarith
  have hβ : ∀ i, ℓ ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ),
      (0 : EuclideanSpace ℝ (Fin n))) ≤ 0 := by
    intro i
    apply cvxRay (a := (c - 1) * α) (u := u)
    intro k hk
    have hmem := hℓB (((c - 1 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) +
      (-k) • ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))))
      ⟨by simp, fun i' => by
        simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        split_ifs <;> simp <;> linarith, fun j => by simp⟩
    rw [map_add, map_smul, hdec0, smul_eq_mul] at hmem
    exact hmem
  let ℓ₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ℓ.comp ((ContinuousLinearMap.inr ℝ ℝ ((Fin m → ℝ) × EuclideanSpace ℝ (Fin n))).comp
      (ContinuousLinearMap.inr ℝ (Fin m → ℝ) (EuclideanSpace ℝ (Fin n))))
  have hℓ₂def : ∀ v, ℓ₂ v = ℓ ((0 : ℝ), (0 : Fin m → ℝ), v) := fun v => rfl
  have hℓ₂K : ∀ v, (∀ j, inner ℝ (w j) v = 0) → ℓ₂ v = 0 := by
    intro v hv
    apply cvxLine (a := (c - 1) * α) (u := u)
    intro k
    have hmem := hℓB (((c - 1 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) +
      k • ((0 : ℝ), (0 : Fin m → ℝ), v))
      ⟨by simp, fun i' => by simp, fun j => by simp [inner_smul_right, hv j]⟩
    rw [map_add, map_smul, hdec0, smul_eq_mul, ← hℓ₂def] at hmem
    exact hmem
  have hspan : (ℓ₂ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ∈
      Submodule.span ℝ (Set.range (fun j => innerₛₗ ℝ (w j))) := by
    apply mem_span_of_iInf_ker_le_ker
    intro v hv
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, innerₛₗ_apply_apply] at hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact hℓ₂K v hv
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hspan
  have hℓ₂ : ∀ v, ℓ₂ v = ∑ j, z j * inner ℝ (w j) v := by
    intro v
    have := congrArg (fun F : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ => F v) hz
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      innerₛₗ_apply_apply, smul_eq_mul, ContinuousLinearMap.coe_coe] at this
    exact this.symm
  refine ⟨fun i => ℓ ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ),
      (0 : EuclideanSpace ℝ (Fin n))) / α, fun j => z j / α,
    fun i => div_nonneg_of_nonpos (hβ i) hαneg.le, ?_⟩
  intro x hx
  have hApt : ((f x, fun i => g i x, x - barx) : ℝ × (Fin m → ℝ) × EuclideanSpace ℝ (Fin n))
      ∈ A := by
    refine ⟨x, hx, le_rfl, fun i => le_rfl, fun j => ?_⟩
    have e := hbarx_h j
    rw [hh] at e ⊢
    simp only [inner_sub_right]
    linarith
  have hle := hAle _ hApt
  rw [cvxDecomp ℓ, ← hαdef, ← hℓ₂def, hℓ₂] at hle
  have hwh : ∀ j, inner ℝ (w j) (x - barx) = h j x := by
    intro j
    have e := hbarx_h j
    rw [hh] at e ⊢
    simp only [inner_sub_right]
    linarith
  simp only [hwh] at hle
  have hLag : α * (f x + ∑ i, ℓ ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ),
      (0 : EuclideanSpace ℝ (Fin n))) / α * g i x + ∑ j, z j / α * h j x) =
      f x * α + ∑ i, g i x * ℓ ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ),
      (0 : EuclideanSpace ℝ (Fin n))) + ∑ j, z j * h j x := by
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    have hα0 : α ≠ 0 := hαneg.ne
    have e1 : ∀ i, α * (ℓ ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ),
        (0 : EuclideanSpace ℝ (Fin n))) / α * g i x) = g i x * ℓ ((0 : ℝ),
        (Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n))) := by
      intro i
      field_simp
    have e2 : ∀ j, α * (z j / α * h j x) = z j * h j x := by
      intro j
      field_simp
    simp only [e1, e2]
    ring
  by_contra hcon
  push Not at hcon
  set L := f x + ∑ i, ℓ ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ),
      (0 : EuclideanSpace ℝ (Fin n))) / α * g i x + ∑ j, z j / α * h j x with hL
  have e2 := hℓB (((L + c) / 2 : ℝ), (0 : Fin m → ℝ), (0 : EuclideanSpace ℝ (Fin n)))
      ⟨by simp; linarith, fun i => by simp, fun j => by simp⟩
  rw [hdec0] at e2
  nlinarith

lemma riBall {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (barx : EuclideanSpace ℝ (Fin n))
    (hb : barx ∈ intrinsicInterior ℝ X) :
    ∃ ε > 0, ∀ z ∈ affineSpan ℝ X, dist z barx < ε → z ∈ X := by
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hb
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
  obtain ⟨ε, hε, hball⟩ := hy
  refine ⟨ε, hε, fun z hz hd => ?_⟩
  have hm : (⟨z, hz⟩ : affineSpan ℝ X) ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact hd
  exact hball hm

lemma cvxShift {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : Convex ℝ X)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ConvexOn ℝ X φ)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ {u : V | c + (u : EuclideanSpace ℝ (Fin n)) ∈ X}
      (fun u : V => φ (c + (u : EuclideanSpace ℝ (Fin n)))) := by
  have key : ∀ (u u' : V) (a b : ℝ), a + b = 1 →
      c + ((a • u + b • u' : V) : EuclideanSpace ℝ (Fin n)) =
        a • (c + (u : EuclideanSpace ℝ (Fin n))) + b • (c + (u' : EuclideanSpace ℝ (Fin n))) := by
    intro u u' a b hab
    have e : a • (c + (u : EuclideanSpace ℝ (Fin n))) + b • (c + (u' : EuclideanSpace ℝ (Fin n)))
        = (a + b) • c + (a • (u : EuclideanSpace ℝ (Fin n)) + b • (u' : EuclideanSpace ℝ (Fin n))) := by
      module
    rw [e, hab, one_smul]
    simp
  refine ⟨fun u hu u' hu' a b ha hb hab => ?_, fun u hu u' hu' a b ha hb hab => ?_⟩
  · show c + ((a • u + b • u' : V) : EuclideanSpace ℝ (Fin n)) ∈ X
    rw [key u u' a b hab]
    exact hX hu hu' ha hb hab
  · show φ (c + ((a • u + b • u' : V) : EuclideanSpace ℝ (Fin n))) ≤ _
    rw [key u u' a b hab]
    exact hφ.2 hu hu' ha hb hab

lemma riLoc {n m : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (barx : EuclideanSpace ℝ (Fin n)) (hb : barx ∈ intrinsicInterior ℝ X)
    (hbarx_g : ∀ i, g i barx < 0) :
    ∀ᶠ v in nhds (0 : EuclideanSpace ℝ (Fin n)), ∃ x ∈ X, f x < f barx + 1 / 2 ∧
        (∀ i, g i x < g i barx / 2) ∧
        x = barx + (affineSpan ℝ X).direction.starProjection v := by
  set V := (affineSpan ℝ X).direction with hV
  obtain ⟨ε, hε, hball⟩ := riBall X barx hb
  have hbX : barx ∈ X := intrinsicInterior_subset hb
  have hbA : barx ∈ affineSpan ℝ X := mem_affineSpan ℝ hbX
  let C : Set V := {u | barx + (u : EuclideanSpace ℝ (Fin n)) ∈ X}
  have hC0 : C ∈ nhds (0 : V) := by
    rw [Metric.mem_nhds_iff]
    refine ⟨ε, hε, fun u hu => ?_⟩
    have hA : barx + (u : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ X := by
      have := AffineSubspace.vadd_mem_of_mem_direction u.2 hbA
      rwa [vadd_eq_add, add_comm] at this
    apply hball _ hA
    rw [mem_ball_zero_iff] at hu
    rw [dist_self_add_left]
    exact hu
  have hCint : interior C ∈ nhds (0 : V) := interior_mem_nhds.2 hC0
  have hcF : ContinuousAt (fun u : V => f (barx + (u : EuclideanSpace ℝ (Fin n)))) 0 :=
    (cvxShift hXconv hfconv V barx).continuousOn_interior.continuousAt hCint
  have e1 : Filter.Eventually (fun u : V => f (barx + (u : EuclideanSpace ℝ (Fin n))) < f barx + 1 / 2)
      (nhds 0) :=
    hcF.eventually (gt_mem_nhds (show f (barx + ((0 : V) : EuclideanSpace ℝ (Fin n))) < f barx + 1 / 2
      by simp))
  have e2 : Filter.Eventually (fun u : V => ∀ i, g i (barx + (u : EuclideanSpace ℝ (Fin n))) < g i barx / 2)
      (nhds 0) := by
    rw [Filter.eventually_all]
    intro i
    have hcg : ContinuousAt (fun u : V => g i (barx + (u : EuclideanSpace ℝ (Fin n)))) 0 :=
      (cvxShift hXconv (hgconv i) V barx).continuousOn_interior.continuousAt hCint
    exact hcg.eventually (gt_mem_nhds (show g i (barx + ((0 : V) : EuclideanSpace ℝ (Fin n))) < g i barx / 2
      by simp; linarith [hbarx_g i]))
  have hT : Filter.Tendsto (fun v : EuclideanSpace ℝ (Fin n) => V.orthogonalProjectionOnto v)
      (nhds 0) (nhds 0) :=
    (V.orthogonalProjectionOnto).continuous.tendsto' 0 0 (map_zero _)
  have e0 : Filter.Eventually (fun u : V => u ∈ C) (nhds 0) := hC0
  filter_upwards [hT.eventually (e0.and (e1.and e2))] with v hv
  exact ⟨barx + (V.orthogonalProjectionOnto v : EuclideanSpace ℝ (Fin n)), hv.1, hv.2.1, hv.2.2,
    by rw [Submodule.starProjection_apply]⟩

lemma riEq {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (barx : EuclideanSpace ℝ (Fin n))
    (hbX : barx ∈ X) (w : EuclideanSpace ℝ (Fin n)) (b : ℝ)
    (hb0 : inner ℝ w barx + b = 0) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) :
    inner ℝ w x + b = inner ℝ ((affineSpan ℝ X).direction.starProjection w) x
      + -inner ℝ ((affineSpan ℝ X).direction.starProjection w) barx := by
  set V := (affineSpan ℝ X).direction
  have hmem : x - barx ∈ V := by
    have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hbX)
    rwa [vsub_eq_sub] at this
  have hS : V.starProjection (x - barx) = x - barx := Submodule.starProjection_eq_self_iff.2 hmem
  have e : inner ℝ (V.starProjection w) (x - barx) = inner ℝ w (x - barx) := by
    rw [Submodule.inner_starProjection_left_eq_right, hS]
  rw [inner_sub_right, inner_sub_right] at e
  linarith

lemma riProj {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) [V.HasOrthogonalProjection]
    (w v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (V.starProjection w) (V.starProjection v) = inner ℝ (V.starProjection w) v := by
  rw [← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 (V.starProjection_apply_mem w)]

lemma gradInner {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (gradient φ x) v = fderiv ℝ φ x v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open FirstOrderOpt.ConvexTheory Gradient in
theorem solution {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_ri : barx ∈ intrinsicInterior ℝ X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (hxstar_opt : ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x) :
    ∃ lamStar : Fin m → ℝ, ∃ yStar : Fin p → ℝ, (∀ i, 0 ≤ lamStar i) ∧
      -((∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j)) ∈
        normalCone X xstar ∧
      (∀ i, lamStar i * g i xstar = 0) := by
  have hbX : barx ∈ X := intrinsicInterior_subset hbarx_ri
  set V := (affineSpan ℝ X).direction with hV
  have heq : ∀ x ∈ X, ∀ j, h j x = inner ℝ (V.starProjection (w j)) x
      + -inner ℝ (V.starProjection (w j)) barx := fun x hx j => by
    rw [hh]
    exact riEq X barx hbX (w j) (b j) (by rw [← hh]; exact hbarx_h j) x hx
  obtain ⟨lam, y, hlam, H⟩ := cvxCore X f g (fun j => V.starProjection (w j))
    (fun j => -inner ℝ (V.starProjection (w j)) barx)
    (fun j x => inner ℝ (V.starProjection (w j)) x + -inner ℝ (V.starProjection (w j)) barx)
    (fun j x => rfl) hXconv hfconv hgconv (f xstar) barx hbX hbarx_g
    (fun j => by simp)
    (fun x hx hg hh0 => hxstar_opt x hx hg (fun j => by rw [heq x hx j]; exact hh0 j))
    (by
      filter_upwards [riLoc X hXconv f g hfconv hgconv barx hbarx_ri hbarx_g] with v hv
      obtain ⟨x, hx, h1, h2, rfl⟩ := hv
      refine ⟨_, hx, h1, h2, fun j => ?_⟩
      rw [inner_add_right, riProj]
      ring)
  have H' : ∀ x ∈ X, f xstar ≤ f x + ∑ i, lam i * g i x + ∑ j, y j * h j x := by
    intro x hx
    have e := H x hx
    have hs : ∑ j, y j * h j x = ∑ j, y j * (inner ℝ (V.starProjection (w j)) x
        + -inner ℝ (V.starProjection (w j)) barx) :=
      Finset.sum_congr rfl fun j _ => by rw [heq x hx j]
    rw [hs]
    exact e
  have hS0 : ∑ i, lam i * g i xstar ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hxstar_g i)
  have hS1 := H' xstar hxstar
  simp only [hxstar_h, mul_zero, Finset.sum_const_zero, add_zero] at hS1
  have hS : ∑ i, lam i * g i xstar = 0 := by linarith
  have hCS : ∀ i, lam i * g i xstar = 0 := by
    have hz := (Finset.sum_eq_zero_iff_of_nonpos
      (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hxstar_g i))).1 hS
    exact fun i => hz i (Finset.mem_univ i)
  refine ⟨lam, y, hlam, ?_, hCS⟩
  let L : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => f x + ∑ i, lam i * g i x + ∑ j, y j * h j x
  have hmin : IsMinOn L X xstar := by
    intro x hx
    show L xstar ≤ L x
    have e := H' x hx
    simp only [L, hxstar_h, mul_zero, Finset.sum_const_zero, add_zero, hS]
    exact e
  have hhd : ∀ j, HasFDerivAt (h j) (innerSL ℝ (w j)) xstar := by
    intro j
    have e : h j = fun x => innerSL ℝ (w j) x + b j := funext fun x => by
      rw [hh, innerSL_apply_apply]
    rw [e]
    exact ((innerSL ℝ (w j)).hasFDerivAt).add_const (b j)
  have hD : HasFDerivAt L (fderiv ℝ f xstar + ∑ i, lam i • fderiv ℝ (g i) xstar
      + ∑ j, y j • innerSL ℝ (w j)) xstar := by
    have h1 := hfdiff.hasFDerivAt
    have h2 := HasFDerivAt.sum (u := Finset.univ) (x := xstar)
      (fun i _ => ((hgdiff i).hasFDerivAt).const_mul (lam i))
    have h3 := HasFDerivAt.sum (u := Finset.univ) (x := xstar)
      (fun j _ => (hhd j).const_mul (y j))
    refine HasFDerivAt.congr_of_eventuallyEq ((h1.add h2).add h3)
      (Filter.Eventually.of_forall fun x => ?_)
    simp [L, Finset.sum_apply]
  simp only [normalCone, Set.mem_setOf_eq]
  intro x hx
  have hseg : segment ℝ xstar (xstar + (x - xstar)) ⊆ X := by
    rw [add_sub_cancel]
    exact hXconv.segment_subset hxstar hx
  have hnn := (hmin.localize).hasFDerivWithinAt_nonneg hD.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, innerSL_apply_apply] at hnn
  rw [inner_neg_left, inner_add_left, inner_add_left, sum_inner, sum_inner, gradInner]
  simp only [inner_smul_left, gradInner, RCLike.conj_to_real]
  linarith
