-- Prove2me | solution 1 for FanGlicksberg.kakutani_fan_glicksberg
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:33:13.408212+00:00
-- url     : https://prove2.me/submissions/18a82be1-7d05-4229-be4a-d981b2f3c4ec

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
import Theorems.Thm_Kakutani1941_FixedPoint_kakutani_fixed_point

open Filter Topology Set Pointwise

namespace KFGAux

/-- Graph of an upper hemicontinuous correspondence with closed values, over a closed set,
is closed (regular target). -/
lemma isClosed_graph {E : Type*} [TopologicalSpace E] [RegularSpace E]
    (K : Set E) (hK : IsClosed K) (Φ : E → Set E) (hΦ : UpperHemicontinuousOn Φ K)
    (hΦclosed : ∀ x ∈ K, IsClosed (Φ x)) :
    IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ Φ p.1} := by
  rw [isClosed_iff_frequently]
  intro p hp
  have hpK : p.1 ∈ K := by
    have : ∃ᶠ q in 𝓝 p, q.1 ∈ K := hp.mono fun q hq => hq.1
    have h2 : ∃ᶠ x in 𝓝 p.1, x ∈ K :=
      (continuous_fst.tendsto p).frequently this
    exact isClosed_iff_frequently.mp hK _ h2
  refine ⟨hpK, ?_⟩
  by_contra hnot
  have hdisj : Disjoint (𝓝ˢ (Φ p.1)) (𝓝 p.2) := by
    rw [disjoint_nhdsSet_nhds, (hΦclosed _ hpK).closure_eq]
    exact hnot
  obtain ⟨W, hW, U, hU, hWU⟩ := Filter.disjoint_iff.mp hdisj
  have h1 : ∀ᶠ x in 𝓝[K] p.1, W ∈ 𝓝ˢ (Φ x) := hΦ p.1 hpK W hW
  rw [eventually_nhdsWithin_iff] at h1
  have h2 : ∀ᶠ q in 𝓝 p, (q.1 ∈ K → W ∈ 𝓝ˢ (Φ q.1)) ∧ q.2 ∈ U :=
    ((continuous_fst.tendsto p).eventually h1).and ((continuous_snd.tendsto p).eventually hU)
  obtain ⟨q, ⟨hq1, hq2⟩, hqK, hqΦ⟩ := (h2.and_frequently hp).exists
  have hsub : Φ q.1 ⊆ W := subset_of_mem_nhdsSet (hq1 hqK)
  exact Set.disjoint_left.mp hWU (hsub hqΦ) hq2

end KFGAux

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (K : Set E) (hKne : K.Nonempty) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (Φ : E → Set E) (hΦ : UpperHemicontinuousOn Φ K)
    (hΦK : ∀ x ∈ K, Φ x ⊆ K) (hΦne : ∀ x ∈ K, (Φ x).Nonempty)
    (hΦconv : ∀ x ∈ K, Convex ℝ (Φ x)) (hΦclosed : ∀ x ∈ K, IsClosed (Φ x)) :
    ∃ x ∈ K, x ∈ Φ x := by
  classical
  have hKcl : IsClosed K := hKc.isClosed
  set Gr : Set (E × E) := {p : E × E | p.1 ∈ K ∧ p.2 ∈ Φ p.1} with hGr_def
  have hGr_closed : IsClosed Gr := KFGAux.isClosed_graph K hKcl Φ hΦ hΦclosed
  have hGr_sub : Gr ⊆ K ×ˢ K := fun p hp => ⟨hp.1, hΦK _ hp.1 hp.2⟩
  have hGr_cpt : IsCompact Gr := (hKc.prod hKc).of_isClosed_subset hGr_closed hGr_sub
  -- the approximate fixed point sets
  set F : Set E → Set E := fun V => {x | ∃ y, (x, y) ∈ Gr ∧ x - y ∈ V} with hF_def
  have hFimg : ∀ V, F V = Prod.fst '' (Gr ∩ {p | p.1 - p.2 ∈ V}) := by
    intro V
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨(x, y), ⟨hy, hxy⟩, rfl⟩
    · rintro ⟨⟨a, y⟩, ⟨hy, hxy⟩, rfl⟩
      exact ⟨y, hy, hxy⟩
  have hFcpt : ∀ V, IsClosed V → IsCompact (F V) := by
    intro V hV
    rw [hFimg]
    exact (hGr_cpt.inter_right (hV.preimage (continuous_fst.sub continuous_snd))).image
      continuous_fst
  have hFne : ∀ V, V ∈ 𝓝 (0 : E) → IsClosed V → Convex ℝ V → (F V).Nonempty := by
    intro V hV hVc hVconv
    have hint : interior V ∈ 𝓝 (0 : E) := interior_mem_nhds.mpr hV
    have h0int : (0 : E) ∈ interior V := mem_of_mem_nhds hint
    obtain ⟨T, hT⟩ := hKc.elim_finite_subcover (fun t : K => {z : E | (t : E) - z ∈ interior V})
      (fun t => isOpen_interior.preimage (continuous_const.sub continuous_id))
      (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, by simpa using h0int⟩)
    set m := T.card with hm
    let e := T.equivFin
    let t : Fin m → E := fun i => ((e.symm i : T) : K)
    have htK : ∀ i, t i ∈ K := fun i => ((e.symm i : T) : K).2
    have hcov : ∀ z ∈ K, ∃ i, t i - z ∈ V := by
      intro z hz
      have := hT hz
      simp only [mem_iUnion] at this
      obtain ⟨s, hs, hzs⟩ := this
      refine ⟨e ⟨s, hs⟩, ?_⟩
      have : t (e ⟨s, hs⟩) = (s : E) := by simp [t]
      rw [this]
      exact interior_subset hzs
    -- the linear map from the simplex
    let L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] E :=
      ∑ i, (LinearMap.smulRight ((EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin m))) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ) (t i))
    have hL : ∀ p, L p = ∑ i, p i • t i := by
      intro p
      simp [L, LinearMap.sum_apply]
    have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
    set S : Set (EuclideanSpace ℝ (Fin m)) := {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} with hS_def
    have hLS : ∀ p ∈ S, L p ∈ K := by
      intro p hp
      rw [hL]
      exact hKconv.sum_mem (fun i _ => hp.1 i) hp.2 (fun i _ => htK i)
    have hsingle : ∀ i, EuclideanSpace.single i (1 : ℝ) ∈ S := by
      intro i
      refine ⟨fun j => ?_, ?_⟩
      · by_cases h : j = i <;> simp [PiLp.single_apply, h]
      · simp [PiLp.single_apply]
    have hLsingle : ∀ i, L (EuclideanSpace.single i (1 : ℝ)) = t i := by
      intro i
      rw [hL]
      simp [PiLp.single_apply]
    have hcoord : ∀ i : Fin m, Continuous fun p : EuclideanSpace ℝ (Fin m) => p i :=
      fun i => PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i
    have hSclosed : IsClosed S := by
      have h1 : IsClosed {p : EuclideanSpace ℝ (Fin m) | ∀ i, 0 ≤ p i} := by
        have : {p : EuclideanSpace ℝ (Fin m) | ∀ i, 0 ≤ p i} =
            ⋂ i, {p : EuclideanSpace ℝ (Fin m) | 0 ≤ p i} := by
          ext p; simp
        rw [this]
        exact isClosed_iInter fun i => isClosed_le continuous_const (hcoord i)
      exact h1.inter (isClosed_eq (continuous_finsetSum _ fun i _ => hcoord i)
        continuous_const)
    have hSconv : Convex ℝ S := by
      intro p hp q hq a b ha hb hab
      refine ⟨fun i => ?_, ?_⟩
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hp.2, hq.2, mul_one, hab]
    have hSbdd : Bornology.IsBounded S := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun p hp => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      rw [Real.sqrt_le_one]
      calc ∑ i, ‖p i‖ ^ 2 ≤ ∑ i, p i := by
            apply Finset.sum_le_sum
            intro i _
            have h0 := hp.1 i
            have h1 : p i ≤ 1 := by
              rw [← hp.2]
              exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
            rw [Real.norm_eq_abs, abs_of_nonneg h0]
            nlinarith
        _ = 1 := hp.2
    obtain ⟨z0, hz0⟩ := hKne
    obtain ⟨i0, -⟩ := hcov z0 hz0
    have hSne : S.Nonempty := ⟨_, hsingle i0⟩
    -- the correspondence on the simplex
    let Ψ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)) :=
      fun p => {q | q ∈ S ∧ ∃ y ∈ Φ (L p), L q - y ∈ V}
    have hsumset : ∀ A : Set E, {c : E | ∃ y ∈ A, c - y ∈ V} = A + V := by
      intro A
      ext c
      simp only [mem_setOf_eq, Set.mem_add]
      constructor
      · rintro ⟨y, hy, hcy⟩
        exact ⟨y, hy, c - y, hcy, by abel⟩
      · rintro ⟨y, hy, v, hv, rfl⟩
        exact ⟨y, hy, by simpa using hv⟩
    have hΨ : ∀ p ∈ S, Kakutani1941.FixedPoint.IsClosedConvexSubset S (Ψ p) := by
      intro p hp
      have hLpK := hLS p hp
      refine ⟨fun q hq => hq.1, ?_, ?_⟩
      · have hcpt : IsCompact (Φ (L p)) :=
          hKc.of_isClosed_subset (hΦclosed _ hLpK) (hΦK _ hLpK)
        have h1 : IsClosed (Φ (L p) + V) := hVc.add_left_of_isCompact hcpt
        have : Ψ p = S ∩ L ⁻¹' (Φ (L p) + V) := by
          ext q
          simp only [Ψ, mem_inter_iff, mem_preimage, ← hsumset]
          rfl
        rw [this]
        exact hSclosed.inter (h1.preimage hLc)
      · intro q1 hq1 q2 hq2 a b ha hb hab
        obtain ⟨hq1S, y1, hy1, hv1⟩ := hq1
        obtain ⟨hq2S, y2, hy2, hv2⟩ := hq2
        refine ⟨hSconv hq1S hq2S ha hb hab, a • y1 + b • y2,
          hΦconv _ hLpK hy1 hy2 ha hb hab, ?_⟩
        have : L (a • q1 + b • q2) - (a • y1 + b • y2) =
            a • (L q1 - y1) + b • (L q2 - y2) := by
          simp only [map_add, map_smul, smul_sub]
          abel
        rw [this]
        exact hVconv hv1 hv2 ha hb hab
    have hΨne : ∀ p ∈ S, (Ψ p).Nonempty := by
      intro p hp
      have hLpK := hLS p hp
      obtain ⟨z, hz⟩ := hΦne _ hLpK
      obtain ⟨i, hi⟩ := hcov z (hΦK _ hLpK hz)
      refine ⟨EuclideanSpace.single i 1, hsingle i, z, hz, ?_⟩
      rw [hLsingle]
      exact hi
    have hD : IsClosed (Gr + ({(0 : E)} ×ˢ V)) :=
      (isClosed_singleton.prod hVc).add_left_of_isCompact hGr_cpt
    have hΨusc : Kakutani1941.FixedPoint.IsUpperSemicontinuous S Ψ := by
      intro x y x₀ y₀ hxS hx₀ hx hy hy₀
      refine ⟨hSclosed.mem_of_tendsto hy₀ (Eventually.of_forall fun n => (hy n).1), ?_⟩
      have hmem : ∀ n, (L (x n), L (y n)) ∈ Gr + ({(0 : E)} ×ˢ V) := by
        intro n
        obtain ⟨-, w, hw, hwv⟩ := hy n
        refine Set.mem_add.mpr ⟨(L (x n), w), ⟨hLS _ (hxS n), hw⟩, (0, L (y n) - w),
          ⟨rfl, hwv⟩, ?_⟩
        simp
      have hlim : Tendsto (fun n => (L (x n), L (y n))) atTop (𝓝 (L x₀, L y₀)) :=
        ((hLc.tendsto _).comp hx).prodMk_nhds ((hLc.tendsto _).comp hy₀)
      obtain ⟨⟨a, w⟩, ⟨haK, hw⟩, ⟨o, v⟩, ⟨ho, hv⟩, heq⟩ :=
        Set.mem_add.mp (hD.mem_of_tendsto hlim (Eventually.of_forall hmem))
      simp only [mem_singleton_iff] at ho
      subst ho
      simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq] at heq
      obtain ⟨rfl, hv'⟩ := heq
      refine ⟨w, hw, ?_⟩
      rw [← hv']
      simpa using hv
    obtain ⟨p, hpS, hpp⟩ := Kakutani1941.FixedPoint.kakutani_fixed_point hSbdd hSclosed hSconv
      hSne Ψ hΨ hΨne hΨusc
    obtain ⟨-, y, hy, hpy⟩ := hpp
    exact ⟨L p, y, ⟨hLS p hpS, hy⟩, hpy⟩
  -- intersection over closed convex neighbourhoods of 0
  let ι := {V : Set E // V ∈ 𝓝 (0 : E) ∧ IsClosed V ∧ Convex ℝ V}
  have hιne : Nonempty ι := ⟨⟨univ, univ_mem, isClosed_univ, convex_univ⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun V : ι => F V.1)
    (by
      intro V W
      refine ⟨⟨V.1 ∩ W.1, inter_mem V.2.1 W.2.1, V.2.2.1.inter W.2.2.1,
        V.2.2.2.inter W.2.2.2⟩, ?_, ?_⟩
      · rintro z ⟨y, hy, hzy⟩
        exact ⟨y, hy, hzy.1⟩
      · rintro z ⟨y, hy, hzy⟩
        exact ⟨y, hy, hzy.2⟩)
    (fun V => hFne V.1 V.2.1 V.2.2.1 V.2.2.2)
    (fun V => hFcpt V.1 V.2.2.1)
    (fun V => (hFcpt V.1 V.2.2.1).isClosed)
  rw [mem_iInter] at hx
  have hxK : x ∈ K := by
    obtain ⟨y, hy, -⟩ := hx ⟨univ, univ_mem, isClosed_univ, convex_univ⟩
    exact hy.1
  refine ⟨x, hxK, ?_⟩
  by_contra hnot
  have hU : (Φ x)ᶜ ∈ 𝓝 x := (hΦclosed x hxK).isOpen_compl.mem_nhds hnot
  have hW0 : {v : E | x - v ∈ (Φ x)ᶜ} ∈ 𝓝 (0 : E) := by
    have hcont : Continuous fun v : E => x - v := continuous_const.sub continuous_id
    have : Tendsto (fun v : E => x - v) (𝓝 0) (𝓝 x) := by
      simpa using hcont.tendsto (0 : E)
    exact this hU
  obtain ⟨W1, hW1, hW1c, hW1sub⟩ := exists_mem_nhds_isClosed_subset hW0
  obtain ⟨W2, ⟨hW2, hW2conv⟩, hW2sub⟩ :=
    (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.mp hW1
  have hcl : closure W2 ⊆ W1 := closure_minimal hW2sub hW1c
  obtain ⟨y, hy, hxy⟩ := hx ⟨closure W2, mem_of_superset hW2 subset_closure, isClosed_closure,
    hW2conv.closure⟩
  have : x - (x - y) ∈ (Φ x)ᶜ := hW1sub (hcl hxy)
  simp only [sub_sub_cancel] at this
  exact this hy.2
