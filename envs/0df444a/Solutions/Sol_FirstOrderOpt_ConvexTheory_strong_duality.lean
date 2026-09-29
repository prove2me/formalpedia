-- Prove2me | solution 1 for FirstOrderOpt.ConvexTheory.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:13:41.923985+00:00
-- url     : https://prove2.me/submissions/e59c51d3-f083-4522-bffe-cdad79c97fe6

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_lagrangian

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

lemma cvxLoc {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_int : barx ∈ interior X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0) :
    ∀ᶠ v in nhds (0 : EuclideanSpace ℝ (Fin n)), ∃ x ∈ X, f x < f barx + 1 / 2 ∧
        (∀ i, g i x < g i barx / 2) ∧ ∀ j, h j x = inner ℝ (w j) v := by
  have hXn : ∀ᶠ x in nhds barx, x ∈ X := mem_interior_iff_mem_nhds.1 hbarx_int
  have hIn : interior X ∈ nhds barx := isOpen_interior.mem_nhds hbarx_int
  have hcf : ContinuousAt f barx := hfconv.continuousOn_interior.continuousAt hIn
  have e1 : ∀ᶠ x in nhds barx, f x < f barx + 1 / 2 :=
    hcf.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ x in nhds barx, ∀ i, g i x < g i barx / 2 := by
    rw [Filter.eventually_all]
    intro i
    have hcg : ContinuousAt (g i) barx := (hgconv i).continuousOn_interior.continuousAt hIn
    exact hcg.eventually (gt_mem_nhds (by linarith [hbarx_g i]))
  have hT : Filter.Tendsto (fun v : EuclideanSpace ℝ (Fin n) => barx + v)
      (nhds 0) (nhds barx) := by
    have hc : Continuous (fun v : EuclideanSpace ℝ (Fin n) => barx + v) :=
      continuous_const.add continuous_id
    exact hc.tendsto' 0 barx (add_zero barx)
  filter_upwards [hT.eventually (hXn.and (e1.and e2))] with v hv
  refine ⟨barx + v, hv.1, hv.2.1, hv.2.2, fun j => ?_⟩
  have e := hbarx_h j
  rw [hh] at e ⊢
  rw [inner_add_right]
  linarith

open FirstOrderOpt.ConvexTheory in
theorem solution {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (Feasible : Set (EuclideanSpace ℝ (Fin n)))
    (hFeasible : Feasible = {x ∈ X | (∀ i, g i x ≤ 0) ∧ (∀ j, h j x = 0)})
    (fStar : ℝ) (hfStar : IsGLB (f '' Feasible) fStar)
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_int : barx ∈ interior X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0) :
    ∃ lamStar : Fin m → ℝ, ∃ yStar : Fin p → ℝ, (∀ i, 0 ≤ lamStar i) ∧
      IsGLB ((fun x => lagrangian f g h x lamStar yStar) '' X) fStar := by
  have hbarxX : barx ∈ X := interior_subset hbarx_int
  obtain ⟨lam, y, hlam, H⟩ := cvxCore X f g w b h hh hXconv hfconv hgconv fStar barx hbarxX
    hbarx_g hbarx_h
    (fun x hx hg hh0 => hfStar.1 ⟨x, by rw [hFeasible]; exact ⟨hx, hg, hh0⟩, rfl⟩)
    (cvxLoc X f g w b h hh hfconv hgconv barx hbarx_int hbarx_g hbarx_h)
  refine ⟨lam, y, hlam, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact H x hx
  · intro B hB
    apply hfStar.2
    rintro _ ⟨x, hxF, rfl⟩
    rw [hFeasible] at hxF
    obtain ⟨hxX, hg, hh0⟩ := hxF
    have e := hB ⟨x, hxX, rfl⟩
    simp only [lagrangian, hh0, mul_zero, Finset.sum_const_zero, add_zero] at e
    have e2 : ∑ i, lam i * g i x ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hg i)
    linarith
