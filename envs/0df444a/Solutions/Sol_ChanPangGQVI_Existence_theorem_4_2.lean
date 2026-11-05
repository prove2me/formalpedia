-- Prove2me | solution 1 for ChanPangGQVI.Existence.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T23:22:04.558562+00:00
-- url     : https://prove2.me/submissions/326d50be-b4b6-4892-90b0-b462607390a1

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_GICP
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet
import Definitions.Def_ChanPangGQVI_Existence_Coercivity
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_graph
import Theorems.Thm_SocialEquilibrium_Existence_fixed_point_of_contractible_polyhedron
import Theorems.Thm_SocialEquilibrium_Existence_isPolyhedron_prod

set_option autoImplicit false

namespace P2M27a3

open SocialEquilibrium.Existence Filter Topology
open scoped RealInnerProductSpace unitInterval

/-- Contractibility transports along a homeomorphism of subtypes. -/
lemma isContractible_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (e : A ≃ₜ B) (hB : IsContractible B) : IsContractible A := by
  obtain ⟨b0, H, h0, h1⟩ := hB
  refine ⟨e.symm b0, ⟨fun p => e.symm (H (p.1, e p.2)), ?_⟩, ?_, ?_⟩
  · exact e.symm.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  · intro z
    show e.symm (H (0, e z)) = z
    rw [h0]; exact e.symm_apply_apply z
  · intro z
    show e.symm (H (1, e z)) = e.symm b0
    rw [h1]

/-- A convex set deforms into any of its points (straight-line homotopy). -/
lemma isDeformableInto_of_convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set V} (hS : Convex ℝ S) (z0 : S) : IsDeformableInto S z0 := by
  refine ⟨⟨fun p => ⟨(1 - (p.1 : ℝ)) • (p.2 : V) + (p.1 : ℝ) • (z0 : V),
    hS p.2.2 z0.2 (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)⟩, ?_⟩, ?_, ?_⟩
  · exact Continuous.subtype_mk (by fun_prop) _
  · intro z
    apply Subtype.ext
    show (1 - ((0 : I) : ℝ)) • (z : V) + ((0 : I) : ℝ) • (z0 : V) = z
    simp
  · intro z
    apply Subtype.ext
    show (1 - ((1 : I) : ℝ)) • (z : V) + ((1 : I) : ℝ) • (z0 : V) = z0
    simp

/-- Product of a convex set and a translate of a (Chan-Pang) contractible set is contractible. -/
lemma isContractible_convex_prod {n : ℕ} {S1 S2 : Set (EuclideanSpace ℝ (Fin n))}
    (q : EuclideanSpace ℝ (Fin n)) (hS1 : Convex ℝ S1) (h1 : S1.Nonempty)
    (h2 : ChanPangGQVI.Existence.IsContractibleSet S2) :
    IsContractible {w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      w.1 ∈ S1 ∧ w.2 - q ∈ S2} := by
  obtain ⟨a0, ha0⟩ := h1
  obtain ⟨x0, hx0, g, hgc, hgm, hg⟩ := h2
  have hmem : ∀ p : I × {w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      w.1 ∈ S1 ∧ w.2 - q ∈ S2},
      ((p.2 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).2 - q, (p.1 : ℝ)) ∈
        S2 ×ˢ Set.Icc (0 : ℝ) 1 := fun p => ⟨p.2.2.2, p.1.2⟩
  refine ⟨⟨(a0, x0 + q), ha0, by simpa using hx0⟩,
    ⟨fun p => ⟨((1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).1
        + (p.1 : ℝ) • a0,
      g ((p.2 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).2 - q, (p.1 : ℝ)) + q),
      hS1 p.2.2.1 ha0 (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring),
      by simpa using hgm (hmem p)⟩, ?_⟩, ?_, ?_⟩
  · refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _
    refine Continuous.add ?_ continuous_const
    refine hgc.comp_continuous (by fun_prop) hmem
  · intro z
    apply Subtype.ext
    show ((1 - ((0 : I) : ℝ)) • (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).1
        + ((0 : I) : ℝ) • a0,
      g ((z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).2 - q, ((0 : I) : ℝ)) + q) =
      (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    rw [Set.Icc.coe_zero, (hg _ z.2.2).1]
    simp
  · intro z
    apply Subtype.ext
    show ((1 - ((1 : I) : ℝ)) • (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).1
        + ((1 : I) : ℝ) • a0,
      g ((z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).2 - q, ((1 : I) : ℝ)) + q) =
      (a0, x0 + q)
    rw [Set.Icc.coe_one, (hg _ z.2.2).2]
    simp

/-- An upper hemicontinuous map with closed values has a closed graph. -/
lemma isClosed_graph_of_uhc {n : ℕ}
    (μ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hμ : UpperHemicontinuous μ) (hcl : ∀ x, IsClosed (μ x)) :
    IsClosed {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ μ p.1} := by
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hp
  have hat : UpperHemicontinuousAt μ p.1 :=
    upperHemicontinuousAt_iff_forall_isOpen.mpr
      ((upperHemicontinuous_iff_forall_isOpen.mp hμ) p.1)
  exact hat.mem_of_tendsto (hcl p.1) ((continuous_fst.tendsto p).comp hlim)
    (Frequently.of_forall fun k => hu k) ((continuous_snd.tendsto p).comp hlim)

/-- An upper hemicontinuous compact-valued map is bounded on a compact set. -/
lemma bounded_of_uhc {n : ℕ}
    (μ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hμ : UpperHemicontinuous μ) (hc : ∀ x, IsCompact (μ x))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    ∃ Y : ℝ, ∀ x ∈ K, ∀ y ∈ μ x, ‖y‖ ≤ Y := by
  refine hK.induction_on (p := fun s => ∃ Y : ℝ, ∀ x ∈ s, ∀ y ∈ μ x, ‖y‖ ≤ Y)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨Y, hY⟩
    exact ⟨Y, fun x hx => hY x (hst hx)⟩
  · rintro s t ⟨Y1, h1⟩ ⟨Y2, h2⟩
    refine ⟨max Y1 Y2, ?_⟩
    rintro x (hx | hx) y hy
    · exact (h1 x hx y hy).trans (le_max_left _ _)
    · exact (h2 x hx y hy).trans (le_max_right _ _)
  · intro x _
    obtain ⟨b, hb⟩ := (hc x).isBounded.subset_closedBall 0
    have hsub : μ x ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (b + 1) := fun y hy =>
      Metric.closedBall_subset_ball (by linarith) (hb hy)
    have hev := (upperHemicontinuous_iff_forall_isOpen.mp hμ) x _ Metric.isOpen_ball hsub
    refine ⟨{x' | μ x' ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (b + 1)},
      mem_nhdsWithin_of_mem_nhds hev, b + 1, fun x' hx' y hy => ?_⟩
    have := hx' hy
    rw [mem_ball_zero_iff] at this
    exact this.le

/-- Every closed ball lies in the convex hull of a finite set. -/
lemma exists_finset_closedBall_subset {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) (T : ℝ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
      Metric.closedBall c T ⊆ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1)) (k := ℝ)
    (V := EuclideanSpace ℝ (Fin n)) (P := EuclideanSpace ℝ (Fin n)) (by simp)
  have hint := b.centroid_mem_interior_convexHull
  set c' := Finset.univ.centroid ℝ b
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c' hint
  set T' := max T 1
  have hT' : 0 < T' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set t : ℝ := T' / (ε / 2)
  let h : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun z => c + t • (z - c')
      linear := t • LinearMap.id
      map_vadd' := by
        intro p v
        simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply]
        rw [show v + p - c' = v + (p - c') by abel, smul_add]
        abel }
  refine ⟨Finset.univ.image (fun i => h (b i)), ?_⟩
  intro z hz
  have hz' : c' + (t⁻¹) • (z - c) ∈ convexHull ℝ (Set.range b) := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (by positivity))]
    have hzc : ‖z - c‖ ≤ T' := (mem_closedBall_iff_norm.mp hz).trans (le_max_left _ _)
    calc t⁻¹ * ‖z - c‖ ≤ t⁻¹ * T' := by gcongr
      _ = ε / 2 := by simp only [t]; field_simp
      _ < ε := by linarith
  have himg : h (c' + (t⁻¹) • (z - c)) = z := by
    show c + t • (c' + t⁻¹ • (z - c) - c') = z
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    abel
  rw [← himg]
  have : h '' convexHull ℝ (Set.range b) = convexHull ℝ (h '' Set.range b) :=
    AffineMap.image_convexHull h _
  have hmem : h (c' + (t⁻¹) • (z - c)) ∈ h '' convexHull ℝ (Set.range b) := ⟨_, hz', rfl⟩
  rw [this] at hmem
  convert hmem using 2
  ext y
  simp [Set.mem_image, Set.range]

lemma cone_smul_mem {n : ℕ} (C : PointedCone ℝ (EuclideanSpace ℝ (Fin n))) {c : ℝ} (hc : 0 ≤ c)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ C) : c • v ∈ C :=
  C.smul_mem hc hv

lemma cone_convex {n : ℕ} (C : PointedCone ℝ (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (C : Set (EuclideanSpace ℝ (Fin n))) := by
  intro a ha b hb s t hs ht _
  exact C.add_mem (cone_smul_mem C hs ha) (cone_smul_mem C ht hb)

lemma isPolyhedron_convexHull {n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin n))) (hS : S.Nonempty) :
    IsPolyhedron (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) := by
  refine ⟨n, convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))),
    ⟨{convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))}, ?_, ?_⟩, ⟨Homeomorph.refl _⟩⟩
  · intro C hC
    rw [Finset.mem_singleton] at hC
    subst hC
    exact ⟨S, hS, rfl⟩
  · simp

lemma finset_nonempty_of_subset {n : ℕ} {S : Finset (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 ≤ r)
    (h : Metric.closedBall c r ⊆ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) :
    S.Nonempty := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · have := h (Metric.mem_closedBall_self hr)
    simp [hS] at this
  · exact hS

open ChanPangGQVI.Existence in
theorem main {n : ℕ} (Lt : PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (hLt_closed : IsClosed (Lt : Set (EuclideanSpace ℝ (Fin n))))
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hm : Continuous m)
    (μ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (ut : EuclideanSpace ℝ (Fin n))
    (hi : ∀ x : EuclideanSpace ℝ (Fin n), ut - m x ∈ Lt)
    (hii : IsStronglyCopositiveAt μ (coneTranslate m (fun _ => Lt)) ut)
    (hμ_contr : ∀ x, IsContractibleSet (μ x))
    (hμ_cpt : ∀ x, IsCompact (μ x)) (hμ_usc : UpperHemicontinuous μ)
    (q : EuclideanSpace ℝ (Fin n)) :
    ∃ x y : EuclideanSpace ℝ (Fin n), IsGICPSolution (fun _ => Lt) m (shiftMap μ q) x y := by
  obtain ⟨_, α, hα, y0, _, hcop⟩ := hii
  obtain ⟨ρ1, hρ1⟩ : ∃ ρ1 : ℝ, ρ1 = ‖q + y0‖ / α + 1 := ⟨_, rfl⟩
  have hρ1pos : 0 < ρ1 := by rw [hρ1]; positivity
  -- radial retraction onto the closed ball of radius ρ1 about ut
  obtain ⟨lam, hlam⟩ : ∃ lam : EuclideanSpace ℝ (Fin n) → ℝ,
      lam = fun x => ρ1 / max ρ1 ‖x - ut‖ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      r = fun x => ut + lam x • (x - ut) := ⟨_, rfl⟩
  have hmaxpos : ∀ x, 0 < max ρ1 ‖x - ut‖ := fun x => lt_of_lt_of_le hρ1pos (le_max_left _ _)
  have hlam0 : ∀ x, 0 ≤ lam x := fun x => by rw [hlam]; exact div_nonneg hρ1pos.le (hmaxpos x).le
  have hlam1 : ∀ x, lam x ≤ 1 := fun x => by
    rw [hlam]; exact (div_le_one (hmaxpos x)).mpr (le_max_left _ _)
  have hlamc : Continuous lam := by
    rw [hlam]
    exact continuous_const.div (continuous_const.max (continuous_id.sub continuous_const).norm)
      (fun x => (hmaxpos x).ne')
  have hrc : Continuous r := by rw [hr]; fun_prop
  have hr_sub : ∀ x, r x - ut = lam x • (x - ut) := fun x => by rw [hr]; simp
  have hr_norm : ∀ x, ‖r x - ut‖ = lam x * ‖x - ut‖ := fun x => by
    rw [hr_sub, norm_smul, Real.norm_of_nonneg (hlam0 x)]
  have hr_ball : ∀ x, r x ∈ Metric.closedBall ut ρ1 := by
    intro x
    rw [mem_closedBall_iff_norm, hr_norm]
    calc lam x * ‖x - ut‖ ≤ lam x * max ρ1 ‖x - ut‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (hlam0 x)
      _ = ρ1 := by rw [hlam]; exact div_mul_cancel₀ _ (hmaxpos x).ne'
  have hr_far : ∀ x, ρ1 < ‖x - ut‖ → ‖r x - ut‖ = ρ1 := by
    intro x hx
    rw [hr_norm, hlam]
    simp only [max_eq_right hx.le]
    exact div_mul_cancel₀ _ (ne_of_gt (hρ1pos.trans hx))
  have hr_near : ∀ x, ‖x - ut‖ ≤ ρ1 → r x = x := by
    intro x hx
    have h1 : lam x = 1 := by rw [hlam]; simp only [max_eq_left hx]; exact div_self hρ1pos.ne'
    have h2 := hr_sub x
    rw [h1, one_smul] at h2
    exact sub_left_injective h2
  -- bounds
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall ut ρ1).exists_bound_of_continuousOn
    (f := fun x => ut - m x) (by fun_prop)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M0 0 := ⟨_, rfl⟩
  have hM0' : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hM : ∀ x ∈ Metric.closedBall ut ρ1, ‖ut - m x‖ ≤ M := fun x hx => by
    rw [hMdef]; exact (hM0 x hx).trans (le_max_left _ _)
  obtain ⟨Y, hY⟩ := bounded_of_uhc μ hμ_usc hμ_cpt _ (isCompact_closedBall ut ρ1)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 * (ρ1 + M) + 1 := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR]; positivity
  obtain ⟨D, hD⟩ : ∃ D : Set (EuclideanSpace ℝ (Fin n)),
      D = (Lt : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.closedBall 0 R := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)),
      A = fun y => {l | l ∈ D ∧ ∀ l' ∈ D, ⟪y, l⟫ ≤ ⟪y, l'⟫} := ⟨_, rfl⟩
  have hDc : IsCompact D := by rw [hD]; exact (isCompact_closedBall 0 R).inter_left hLt_closed
  have h0D : (0 : EuclideanSpace ℝ (Fin n)) ∈ D := by
    rw [hD]; exact ⟨Lt.zero_mem, Metric.mem_closedBall_self hRpos.le⟩
  have hAne : ∀ y, (A y).Nonempty := by
    intro y
    obtain ⟨l, hl, hmin⟩ := hDc.exists_isMinOn ⟨0, h0D⟩
      (f := fun l => ⟪y, l⟫) (by fun_prop)
    rw [hA]
    exact ⟨l, hl, fun l' hl' => hmin hl'⟩
  have hDconv : Convex ℝ D := by rw [hD]; exact (cone_convex Lt).inter (convex_closedBall 0 R)
  have hAconv : ∀ y, Convex ℝ (A y) := by
    intro y l1 hl1 l2 hl2 a b ha hb hab
    rw [hA] at hl1 hl2 ⊢
    refine ⟨hDconv hl1.1 hl2.1 ha hb hab, fun l' hl' => ?_⟩
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have e1 := mul_le_mul_of_nonneg_left (hl1.2 l' hl') ha
    have e2 := mul_le_mul_of_nonneg_left (hl2.2 l' hl') hb
    have e3 : a * ⟪y, l'⟫ + b * ⟪y, l'⟫ = ⟪y, l'⟫ := by rw [← add_mul, hab, one_mul]
    linarith
  have hAgraph : IsClosed {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ A p.1} := by
    have e : {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ A p.1} =
        {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ D} ∩
          ⋂ l' ∈ D, {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            ⟪p.1, p.2⟫ ≤ ⟪p.1, l'⟫} := by
      ext p
      rw [hA]
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    exact (hDc.isClosed.preimage continuous_snd).inter
      (isClosed_biInter fun l' _ => isClosed_le (by fun_prop) (by fun_prop))
  -- the polyhedral domain
  obtain ⟨Sx, hSx⟩ := exists_finset_closedBall_subset ut (M + R)
  obtain ⟨Sy, hSy⟩ := exists_finset_closedBall_subset (0 : EuclideanSpace ℝ (Fin n)) (max Y 0 + ‖q‖)
  have hMR : 0 ≤ M + R := by linarith
  have hYq : 0 ≤ max Y 0 + ‖q‖ := by positivity
  obtain ⟨Z, hZdef⟩ : ∃ Z : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      Z = convexHull ℝ (Sx : Set (EuclideanSpace ℝ (Fin n))) ×ˢ
        convexHull ℝ (Sy : Set (EuclideanSpace ℝ (Fin n))) := ⟨_, rfl⟩
  have hZ : IsPolyhedron Z := by
    rw [hZdef]
    exact isPolyhedron_prod (isPolyhedron_convexHull Sx (finset_nonempty_of_subset hMR hSx))
      (isPolyhedron_convexHull Sy (finset_nonempty_of_subset hYq hSy))
  have hZc : IsContractible Z := by
    have hz0 : (ut, (0 : EuclideanSpace ℝ (Fin n))) ∈ Z := by
      rw [hZdef]
      exact ⟨hSx (Metric.mem_closedBall_self hMR), hSy (Metric.mem_closedBall_self hYq)⟩
    refine ⟨⟨_, hz0⟩, isDeformableInto_of_convex ?_ _⟩
    rw [hZdef]
    exact (convex_convexHull ℝ _).prod (convex_convexHull ℝ _)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      Φ = fun z => {w | w.1 ∈ {a | a - m (r z.1) ∈ A z.2} ∧ w.2 - q ∈ μ (r z.1)} := ⟨_, rfl⟩
  have hΦZ : ∀ z, Φ z ⊆ Z := by
    intro z w hw
    rw [hΦ] at hw
    obtain ⟨h1, h2⟩ := hw
    have h1' : w.1 - m (r z.1) ∈ A z.2 := h1
    rw [hA] at h1'
    have hD1 := h1'.1
    rw [hD] at hD1
    have hl := hD1.2
    rw [mem_closedBall_zero_iff] at hl
    have hmb := hM _ (hr_ball z.1)
    rw [hZdef]
    refine ⟨hSx ?_, hSy ?_⟩
    · rw [mem_closedBall_iff_norm]
      calc ‖w.1 - ut‖ = ‖(w.1 - m (r z.1)) - (ut - m (r z.1))‖ := by congr 1; abel
        _ ≤ ‖w.1 - m (r z.1)‖ + ‖ut - m (r z.1)‖ := norm_sub_le _ _
        _ ≤ M + R := by linarith
    · rw [mem_closedBall_zero_iff]
      have hy := hY _ (hr_ball z.1) _ h2
      calc ‖w.2‖ = ‖(w.2 - q) + q‖ := by rw [sub_add_cancel]
        _ ≤ ‖w.2 - q‖ + ‖q‖ := norm_add_le _ _
        _ ≤ max Y 0 + ‖q‖ := by linarith [le_max_left Y 0]
  have hG : IsClosed {p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) | p.2 ∈ Φ p.1} := by
    have h1 : IsClosed {p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
        (p.1.2, p.2.1 - m (r p.1.1)) ∈
          {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ A p.1}} :=
      hAgraph.preimage (by fun_prop)
    have h2 : IsClosed {p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
        (r p.1.1, p.2.2 - q) ∈
          {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ μ p.1}} :=
      (isClosed_graph_of_uhc μ hμ_usc (fun x => (hμ_cpt x).isClosed)).preimage (by fun_prop)
    rw [hΦ]
    exact h1.inter h2
  obtain ⟨φ, hφdef⟩ : ∃ φ : Z → Set Z, φ = fun z => Subtype.val ⁻¹' Φ z.1 := ⟨_, rfl⟩
  have hφ : IsSemicontinuous φ := by
    show IsClosed (graph φ)
    have e : graph φ = (fun p : Z × Z => ((p.1 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        (p.2 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))) ⁻¹'
        {p | p.2 ∈ Φ p.1} := by
      rw [hφdef]; rfl
    rw [e]
    exact hG.preimage (by fun_prop)
  have hφc : ∀ z : Z, IsContractible (φ z) := by
    intro z
    have hsub : Φ z.1 ⊆ Set.range (Subtype.val : Z → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := by
      rw [Subtype.range_coe]; exact hΦZ z.1
    rw [hφdef]
    refine isContractible_of_homeomorph
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsub) ?_
    obtain ⟨a, ha⟩ := hAne z.1.2
    have hconv : Convex ℝ {a | a - m (r z.1.1) ∈ A z.1.2} := by
      intro a1 h1 a2 h2 s t hs ht hst
      have e : s • (a1 - m (r z.1.1)) + t • (a2 - m (r z.1.1)) =
          s • a1 + t • a2 - (s + t) • m (r z.1.1) := by
        simp only [smul_sub, add_smul]; abel
      rw [hst, one_smul] at e
      show s • a1 + t • a2 - m (r z.1.1) ∈ A z.1.2
      rw [← e]
      exact hAconv z.1.2 h1 h2 hs ht hst
    have hne : ({a | a - m (r z.1.1) ∈ A z.1.2} : Set (EuclideanSpace ℝ (Fin n))).Nonempty :=
      ⟨a + m (r z.1.1), by simpa using ha⟩
    rw [hΦ]
    exact isContractible_convex_prod (S1 := {a | a - m (r z.1.1) ∈ A z.1.2}) q hconv hne
      (hμ_contr _)
  obtain ⟨⟨⟨x, y⟩, hz⟩, hfix⟩ := fixed_point_of_contractible_polyhedron Z hZ hZc φ hφ hφc
  rw [hφdef] at hfix
  have hfix' : (x, y) ∈ Φ (x, y) := hfix
  rw [hΦ] at hfix'
  obtain ⟨hsA', hyμ⟩ := hfix'
  have hsA : x - m (r x) ∈ A y := hsA'
  rw [hA] at hsA
  have hyμ' : y - q ∈ μ (r x) := hyμ
  -- a priori bound
  have hw : ut - m (r x) ∈ Lt := hi (r x)
  have hwM : ‖ut - m (r x)‖ ≤ M := hM _ (hr_ball x)
  have hwD : ut - m (r x) ∈ D := by
    rw [hD]; refine ⟨hw, ?_⟩
    rw [mem_closedBall_zero_iff]; rw [hR]; linarith
  have hsD := hsA.1
  have hsLt : x - m (r x) ∈ Lt := by rw [hD] at hsD; exact hsD.1
  have hys : ⟪y, x - m (r x)⟫ ≤ ⟪y, ut - m (r x)⟫ := hsA.2 _ hwD
  have hfeas : r x - m (r x) ∈ Lt := by
    have e : r x - m (r x) = lam x • (x - m (r x)) + (1 - lam x) • (ut - m (r x)) := by
      have h := hr_sub x
      rw [show r x = ut + lam x • (x - ut) by rw [← h]; abel]
      simp only [smul_sub, sub_smul, one_smul]
      abel
    rw [e]
    exact Lt.add_mem (cone_smul_mem Lt (hlam0 x) hsLt) (cone_smul_mem Lt (sub_nonneg.mpr (hlam1 x)) hw)
  have hcopx := hcop (r x) ⟨r x - m (r x), hfeas, by abel⟩ (y - q) hyμ'
  have hin1 : ⟪y, r x - ut⟫ ≤ 0 := by
    rw [hr_sub, real_inner_smul_right]
    have e : x - ut = (x - m (r x)) - (ut - m (r x)) := by abel
    rw [e, inner_sub_right]
    exact mul_nonpos_of_nonneg_of_nonpos (hlam0 x) (by linarith)
  have hin2 : -⟪q + y0, r x - ut⟫ ≤ ‖q + y0‖ * ‖r x - ut‖ := by
    have h := real_inner_le_norm (-(q + y0)) (r x - ut)
    rw [inner_neg_left, norm_neg] at h
    exact h
  have hsplit : ⟪y - q - y0, r x - ut⟫ = ⟪y, r x - ut⟫ - ⟪q + y0, r x - ut⟫ := by
    rw [show y - q - y0 = y - (q + y0) by abel, inner_sub_left]
  have hd : α * ‖r x - ut‖ ^ 2 ≤ ‖q + y0‖ * ‖r x - ut‖ := by linarith
  have hnear : ‖x - ut‖ ≤ ρ1 := by
    by_contra hfar
    rw [not_le] at hfar
    rw [hr_far x hfar] at hd
    have h3 : α * ρ1 * ρ1 ≤ ‖q + y0‖ * ρ1 := by nlinarith
    have h3' : α * ρ1 ≤ ‖q + y0‖ := le_of_mul_le_mul_right h3 hρ1pos
    have h4 : α * ρ1 = ‖q + y0‖ + α := by rw [hρ1]; field_simp
    linarith
  have hxeq : r x = x := hr_near x hnear
  rw [hxeq] at hsLt hsA hyμ' hwM
  have hsn : ‖x - m x‖ ≤ ρ1 + M := by
    calc ‖x - m x‖ = ‖(x - ut) + (ut - m x)‖ := by congr 1; abel
      _ ≤ ‖x - ut‖ + ‖ut - m x‖ := norm_add_le _ _
      _ ≤ ρ1 + M := by linarith
  have hle0 : ⟪y, x - m x⟫ ≤ 0 := by
    have := hsA.2 0 h0D
    simpa using this
  have hge0 : 0 ≤ ⟪y, x - m x⟫ := by
    have hD2 : (2 : ℝ) • (x - m x) ∈ D := by
      rw [hD]
      refine ⟨cone_smul_mem Lt (by norm_num) hsLt, ?_⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2), hR]
      linarith
    have := hsA.2 _ hD2
    rw [real_inner_smul_right] at this
    linarith
  have hdual : ∀ l ∈ Lt, 0 ≤ ⟪y, l⟫ := by
    intro l hl
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (‖l‖ + 1) := ⟨_, rfl⟩
    have hcpos : 0 < c := by rw [hc]; positivity
    have hcl : c * ‖l‖ ≤ 1 := by
      rw [hc, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    have hDl : x - m x + c • l ∈ D := by
      rw [hD]
      refine ⟨Lt.add_mem hsLt (cone_smul_mem Lt hcpos.le hl), ?_⟩
      rw [mem_closedBall_zero_iff]
      calc ‖x - m x + c • l‖ ≤ ‖x - m x‖ + ‖c • l‖ := norm_add_le _ _
        _ = ‖x - m x‖ + c * ‖l‖ := by rw [norm_smul, Real.norm_of_nonneg hcpos.le]
        _ ≤ R := by rw [hR]; linarith
    have := hsA.2 _ hDl
    rw [inner_add_right, real_inner_smul_right] at this
    have h5 : 0 ≤ c * ⟪y, l⟫ := by linarith
    exact (mul_nonneg_iff_of_pos_left hcpos).mp h5
  refine ⟨x, y, ⟨x - m x, hsLt, by abel⟩, ⟨y - q, hyμ', sub_add_cancel y q⟩,
    fun l hl => hdual l hl, le_antisymm hle0 hge0⟩

end P2M27a3

open ChanPangGQVI.Existence in
theorem solution {n : ℕ} (Lt : PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (hLt_closed : IsClosed (Lt : Set (EuclideanSpace ℝ (Fin n))))
    (hLt_solid : (interior (Lt : Set (EuclideanSpace ℝ (Fin n)))).Nonempty)
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hm : Continuous m)
    (μ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (ut : EuclideanSpace ℝ (Fin n))
    (hi : ∀ x : EuclideanSpace ℝ (Fin n), ut - m x ∈ Lt)
    (hii : IsStronglyCopositiveAt μ (coneTranslate m (fun _ => Lt)) ut)
    (hμ_ne : ∀ x, (μ x).Nonempty) (hμ_contr : ∀ x, IsContractibleSet (μ x))
    (hμ_cpt : ∀ x, IsCompact (μ x)) (hμ_usc : UpperHemicontinuous μ) :
    ∀ q : EuclideanSpace ℝ (Fin n),
      ∃ x y : EuclideanSpace ℝ (Fin n), IsGICPSolution (fun _ => Lt) m (shiftMap μ q) x y := by
  intro q
  exact P2M27a3.main Lt hLt_closed m hm μ ut hi hii hμ_contr hμ_cpt hμ_usc q
