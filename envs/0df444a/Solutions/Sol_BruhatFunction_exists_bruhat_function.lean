-- Prove2me | solution 1 for BruhatFunction.exists_bruhat_function
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:56:25.761853+00:00
-- url     : https://prove2.me/submissions/0569ce35-d3ba-4c8a-9650-e19eb601eb36

import Mathlib

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace Sol_BruhatFunction_exists_bruhat_function

open Set Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Topological step: a continuous `f ≥ 0` on `G`, compactly supported modulo `H`, which is
positive somewhere on every coset `xH`. It is a locally finite sum of right translates of one
compactly supported bump, over a maximal "separated" family of points. -/
theorem exists_pos_fn [LocallyCompactSpace G] [T2Space G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ f : G → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport f ∩ (K * (H : Set G)))) ∧
      ∀ x : G, ∃ h ∈ H, 0 < f (x * h) := by
  obtain ⟨C0, hC0c, hC0n⟩ := exists_compact_mem_nhds (1 : G)
  have h1C0 : (1 : G) ∈ C0 := mem_of_mem_nhds hC0n
  set U : Set G := C0 * C0⁻¹ with hUdef
  have hUc : IsCompact U := hC0c.mul hC0c.inv
  have h1U : (1 : G) ∈ U := Set.mem_mul.2 ⟨1, h1C0, 1, by simpa using h1C0, by simp⟩
  have hUinv : ∀ u ∈ U, u⁻¹ ∈ U := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hu
    exact Set.mem_mul.2 ⟨b⁻¹, Set.mem_inv.1 hb, a⁻¹, by simpa using ha, by group⟩
  -- the "closeness" relation between points of `G`
  set R : G → G → Prop := fun x y => ∃ u ∈ U, ∃ h ∈ H, y = u * x * h with hRdef
  have hRsymm : ∀ x y, R x y → R y x := by
    rintro x y ⟨u, hu, h, hh, rfl⟩
    exact ⟨u⁻¹, hUinv u hu, h⁻¹, H.inv_mem hh, by group⟩
  -- a maximal separated family
  obtain ⟨X, hXmax⟩ := zorn_subset {X : Set G | X.Pairwise (fun x y => ¬ R x y)}
    (fun c hcS hc => ⟨⋃₀ c, (hc.pairwise_sUnion).2 hcS, fun s hs => Set.subset_sUnion_of_mem hs⟩)
  have hXS : X.Pairwise (fun x y => ¬ R x y) := hXmax.1
  have hcover : ∀ y : G, ∃ x ∈ X, R x y := by
    intro y
    by_contra hy
    push Not at hy
    have hins : (insert y X).Pairwise (fun x y => ¬ R x y) := by
      rw [Set.pairwise_insert]
      exact ⟨hXS, fun b hb _ => ⟨fun hR => hy b hb (hRsymm _ _ hR), hy b hb⟩⟩
    have hsub : insert y X ⊆ X := hXmax.2 hins (Set.subset_insert _ _)
    exact hy y (hsub (Set.mem_insert _ _)) ⟨1, h1U, 1, H.one_mem, by simp⟩
  -- a separated family meets every saturated compact set `C * H` in finitely many points
  have hfin : ∀ C : Set G, IsCompact C →
      {x : G | x ∈ X ∧ ∃ c ∈ C, ∃ h ∈ H, x = c * h}.Finite := by
    intro C hC
    have hN : ∀ c ∈ C, (fun g => g * c⁻¹) ⁻¹' C0 ∈ 𝓝 c := by
      intro c _
      apply (continuous_mul_const c⁻¹).continuousAt.preimage_mem_nhds
      simpa using hC0n
    obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover _ hN
    have hex : ∀ x ∈ {x : G | x ∈ X ∧ ∃ c ∈ C, ∃ h ∈ H, x = c * h},
        ∃ a ∈ t, ∃ c : G, c * a⁻¹ ∈ C0 ∧ ∃ h ∈ H, x = c * h := by
      rintro x ⟨-, c, hc, h, hh, rfl⟩
      obtain ⟨a, hat, hca⟩ := Set.mem_iUnion₂.1 (hcov hc)
      exact ⟨a, hat, c, hca, h, hh, rfl⟩
    choose! j hjt hj using hex
    refine Set.Finite.of_finite_image (f := j) ?_ ?_
    · exact t.finite_toSet.subset (Set.image_subset_iff.2 fun x hx => hjt x hx)
    · intro x hx x' hx' hjj
      by_contra hne
      obtain ⟨c, hc, h, hh, hxe⟩ := hj x hx
      obtain ⟨c', hc', h', hh', hxe'⟩ := hj x' hx'
      rw [hjj] at hc
      apply hXS hx'.1 hx.1 (Ne.symm hne)
      refine ⟨(c * (j x')⁻¹) * (c' * (j x')⁻¹)⁻¹,
        Set.mem_mul.2 ⟨_, hc, _, by simpa using hc', rfl⟩, h'⁻¹ * h, H.mul_mem (H.inv_mem hh') hh, ?_⟩
      rw [hxe, hxe']
      group
  -- the bump function
  obtain ⟨φ, hφU, -, hφc, hφ01⟩ :=
    exists_continuous_one_zero_of_isCompact hUc isClosed_empty (Set.disjoint_empty _)
  set S : Set G := tsupport φ with hSdef
  set P : X → Set G := fun i => (fun y => y * (i : G)⁻¹) ⁻¹' S with hPdef
  have hPclosed : ∀ i, IsClosed (P i) := fun i =>
    (isClosed_tsupport _).preimage (continuous_mul_const _)
  have hPfin : ∀ K : Set G, IsCompact K → {i : X | (P i ∩ (K * (H : Set G))).Nonempty}.Finite := by
    intro K hK
    have h1 := (hfin _ (hφc.inv.mul hK)).preimage (f := (Subtype.val : X → G))
      Subtype.val_injective.injOn
    refine h1.subset ?_
    rintro i ⟨z, hzP, hzK⟩
    obtain ⟨k, hk, h, hh, hkh⟩ := Set.mem_mul.1 hzK
    refine ⟨i.2, (z * (i : G)⁻¹)⁻¹ * k, Set.mem_mul.2 ⟨_, Set.inv_mem_inv.2 (show z * (i : G)⁻¹ ∈ S from hzP), k, hk, rfl⟩, h, hh, ?_⟩
    rw [mul_assoc, hkh]
    group
  have hPlf : LocallyFinite P := by
    intro y
    obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds y
    refine ⟨K, hKn, (hPfin K hKc).subset ?_⟩
    rintro i ⟨z, hzP, hzK⟩
    exact ⟨z, hzP, Set.mem_mul.2 ⟨z, hzK, 1, H.one_mem, mul_one z⟩⟩
  set g : X → G → ℝ := fun i y => φ (y * (i : G)⁻¹) with hgdef
  have hgsupp : ∀ i, Function.support (g i) ⊆ P i := by
    intro i y hy
    exact subset_tsupport _ hy
  have hglf : LocallyFinite fun i => Function.support (g i) := hPlf.subset hgsupp
  refine ⟨fun y => ∑ᶠ i, g i y, ?_, ?_, ?_, ?_⟩
  · exact continuous_finsum (fun i => φ.continuous.comp (continuous_mul_const _)) hglf
  · intro y
    exact finsum_nonneg fun i => (hφ01 _).1
  · intro K hK
    have hsupp : tsupport (fun y => ∑ᶠ i, g i y) ⊆ ⋃ i, P i := by
      refine closure_minimal ?_ (hPlf.isClosed_iUnion hPclosed)
      intro y hy
      by_contra hn
      apply hy
      refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
      by_contra hne
      exact hn (Set.mem_iUnion.2 ⟨i, hgsupp i hne⟩)
    refine IsCompact.of_isClosed_subset
      ((hPfin K hK).isCompact_biUnion fun i _ => hφc.image (continuous_mul_const (i : G)))
      ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK)) ?_
    rintro z ⟨hzs, hzK⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsupp hzs)
    refine Set.mem_iUnion₂.2 ⟨i, ⟨z, hi, hzK⟩, z * (i : G)⁻¹, hi, by group⟩
  · intro x
    obtain ⟨x0, hx0, u, hu, h, hh, hxe⟩ := hcover x
    refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
    have hval : g ⟨x0, hx0⟩ (x * h⁻¹) = 1 := by
      simp only [hgdef]
      rw [show x * h⁻¹ * x0⁻¹ = u by rw [hxe]; group]
      exact hφU hu
    have hle : g ⟨x0, hx0⟩ (x * h⁻¹) ≤ ∑ᶠ i, g i (x * h⁻¹) :=
      single_le_finsum (f := fun i => g i (x * h⁻¹)) (⟨x0, hx0⟩ : X)
        (hglf.point_finite (x * h⁻¹)) (fun j => (hφ01 _).1)
    linarith

/-- Normalization step: a continuous `f ≥ 0` which is compactly supported modulo `H` and does not
vanish identically on any coset `xH` can be divided by its `H`-average. -/
theorem of_pos_fn [LocallyCompactSpace G] [T2Space G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsHaarMeasure]
    (f : G → ℝ) (hfc : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfK : ∀ K : Set G, IsCompact K → IsCompact (tsupport f ∩ (K * (H : Set G))))
    (hpos : ∀ x : G, ∃ h ∈ H, 0 < f (x * h)) :
    ∃ u : G → ℝ, Continuous u ∧ (∀ x, 0 ≤ u x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport u ∩ (K * (H : Set G)))) ∧
      ∀ x : G, Integrable (fun h : H => u (x * (h : G))) μH ∧
        ∫ h : H, u (x * (h : G)) ∂μH = 1 := by
  have hemb : Topology.IsClosedEmbedding (Subtype.val : H → G) := hH.isClosedEmbedding_subtypeVal
  -- the compact set of `H` outside of which `h ↦ f (y * h)` vanishes, uniformly for `y ∈ K`
  have hL : ∀ K : Set G, IsCompact K →
      IsCompact ((Subtype.val : H → G) ⁻¹' (K⁻¹ * (tsupport f ∩ (K * (H : Set G))))) ∧
      ∀ y ∈ K, ∀ h : H,
        h ∉ (Subtype.val : H → G) ⁻¹' (K⁻¹ * (tsupport f ∩ (K * (H : Set G)))) →
          f (y * (h : G)) = 0 := by
    intro K hK
    refine ⟨hemb.isCompact_preimage (hK.inv.mul (hfK K hK)), ?_⟩
    intro y hy h hh
    by_contra hne
    apply hh
    refine Set.mem_mul.2 ⟨y⁻¹, by simpa using hy, y * (h : G), ⟨subset_tsupport _ hne,
      Set.mem_mul.2 ⟨y, hy, (h : G), h.2, rfl⟩⟩, by group⟩
  have hcont : ∀ x : G, Continuous (fun h : H => f (x * (h : G))) := fun x =>
    hfc.comp (continuous_const.mul continuous_subtype_val)
  have hcs : ∀ x : G, HasCompactSupport (fun h : H => f (x * (h : G))) := by
    intro x
    obtain ⟨hLc, hLz⟩ := hL {x} isCompact_singleton
    refine hLc.of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_minimal ?_ hLc.isClosed
    intro h hh
    by_contra hn
    exact hh (hLz x rfl h hn)
  have hint : ∀ x : G, Integrable (fun h : H => f (x * (h : G))) μH := fun x =>
    (hcont x).integrable_of_hasCompactSupport (hcs x)
  set F : G → ℝ := fun x => ∫ h : H, f (x * (h : G)) ∂μH with hFdef
  have hFinv : ∀ x : G, ∀ h0 ∈ H, F (x * h0) = F x := by
    intro x h0 hh0
    have := integral_mul_left_eq_self (μ := μH) (fun h : H => f (x * (h : G))) ⟨h0, hh0⟩
    simp only [hFdef]
    rw [← this]
    congr 1
    funext h
    simp [mul_assoc]
  have hFpos : ∀ x : G, 0 < F x := by
    intro x
    obtain ⟨h0, hh0, hp⟩ := hpos x
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (⟨h0, hh0⟩ : H))
      (hcont x) (hcs x) (fun h => hf0 _) hp.ne'
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro y0
    obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds y0
    obtain ⟨hLc, hLz⟩ := hL K hKc
    have hco : ContinuousOn F K := by
      refine continuousOn_integral_of_compact_support (f := fun (y : G) (h : H) => f (y * (h : G)))
        hLc ?_ ?_
      · exact (hfc.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).continuousOn
      · intro p x hp hx
        exact hLz p hp x hx
    exact hco.continuousAt hKn
  refine ⟨fun y => f y * (F y)⁻¹, ?_, ?_, ?_, ?_⟩
  · exact hfc.mul (hFc.inv₀ fun y => (hFpos y).ne')
  · intro y
    exact mul_nonneg (hf0 y) (inv_nonneg.2 (hFpos y).le)
  · intro K hK
    exact (hfK K hK).of_isClosed_subset
      ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK))
      (Set.inter_subset_inter_left _ tsupport_mul_subset_left)
  · intro x
    have heq : (fun h : H => f (x * (h : G)) * (F (x * (h : G)))⁻¹) =
        fun h : H => f (x * (h : G)) * (F x)⁻¹ := by
      funext h
      rw [hFinv x h h.2]
    refine ⟨?_, ?_⟩
    · simp only [heq]
      exact (hint x).mul_const _
    · simp only [heq]
      rw [integral_mul_const]
      exact mul_inv_cancel₀ (hFpos x).ne'

end Sol_BruhatFunction_exists_bruhat_function

open Sol_BruhatFunction_exists_bruhat_function in
theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsHaarMeasure] :
    ∃ u : G → ℝ, Continuous u ∧ (∀ x, 0 ≤ u x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport u ∩ (K * (H : Set G)))) ∧
      ∀ x : G, Integrable (fun h : H => u (x * (h : G))) μH ∧
        ∫ h : H, u (x * (h : G)) ∂μH = 1 := by
  obtain ⟨f, hfc, hf0, hfK, hpos⟩ := exists_pos_fn H hH
  exact of_pos_fn H hH μH f hfc hf0 hfK hpos
