-- Prove2me | solution 1 for CGWH.onePoint_rat_weaklyHausdorff_not_t2
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:02:48.834329+00:00
-- url     : https://prove2.me/submissions/8b5e7e3b-5b8c-4d1d-a262-65a1f857bc64

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

namespace Sol_CGWH_onePoint_rat_weaklyHausdorff_not_t2

open Filter OnePoint Set

/-- `OnePoint ℚ` is a sequential space: a sequentially closed subset `A` has a closed trace on `ℚ`,
and if `∞ ∉ A` this trace is sequentially compact, because a sequence of `A ∩ ℚ` without convergent
subsequence leaves every compact subset of `ℚ`, i.e. tends to `∞`. -/
theorem sequentialSpace : SequentialSpace (OnePoint ℚ) := by
  refine ⟨fun A hA => ?_⟩
  have hB : IsClosed ((↑) ⁻¹' A : Set ℚ) := by
    refine IsSeqClosed.isClosed fun x p hx hxp => ?_
    exact hA (x := fun n => (x n : OnePoint ℚ)) hx ((continuous_coe.tendsto p).comp hxp)
  by_cases h : ∞ ∈ A
  · exact (isClosed_iff_of_mem h).2 hB
  · refine (isClosed_iff_of_notMem h).2 ⟨hB, ?_⟩
    rw [isCompact_iff_isSeqCompact]
    intro x hx
    by_contra hcon
    have hx_inf : Tendsto (fun n => (x n : OnePoint ℚ)) atTop (𝓝 ∞) := by
      have hcc : Tendsto x atTop (coclosedCompact ℚ) := by
        rw [hasBasis_coclosedCompact.tendsto_right_iff]
        rintro K ⟨-, hKc⟩
        by_contra hfreq
        have hfreq' : ∃ᶠ n in atTop, x n ∈ K := by
          rw [not_eventually] at hfreq
          exact hfreq.mono fun n hn => not_not.1 hn
        obtain ⟨a, -, φ, hφ, hφa⟩ := hKc.isSeqCompact.subseq_of_frequently_in hfreq'
        have haB : a ∈ ((↑) ⁻¹' A : Set ℚ) :=
          hB.mem_of_tendsto hφa (Eventually.of_forall fun n => hx (φ n))
        exact hcon ⟨a, haB, φ, hφ, hφa⟩
      exact tendsto_coe_infty.comp hcc
    exact h (hA (x := fun n => (x n : OnePoint ℚ)) hx hx_inf)

/-- Every compact subset of `OnePoint ℚ` is closed. -/
theorem isClosed_of_isCompact {C : Set (OnePoint ℚ)} (hC : IsCompact C) : IsClosed C := by
  have hD : IsClosed ((↑) ⁻¹' C : Set ℚ) := by
    refine IsSeqClosed.isClosed fun d q hd hdq => ?_
    -- a cluster point `c ∈ C` of the sequence `↑(d n)`
    obtain ⟨c, hcC, hc⟩ := hC (f := map (fun n => (d n : OnePoint ℚ)) atTop)
      (le_principal_iff.2 (mem_map.2 (Eventually.of_forall hd)))
    induction c using OnePoint.rec with
    | infty =>
      exfalso
      -- the compact set `{q} ∪ {d n}` of `ℚ` gives a neighbourhood of `∞` avoiding the sequence
      have hK : IsCompact (insert q (range d)) := hdq.isCompact_insert_range
      have hopen : IsOpen ((↑) '' (insert q (range d)) : Set (OnePoint ℚ))ᶜ :=
        isOpen_compl_image_coe.2 ⟨hK.isClosed, hK⟩
      have h1 : ((↑) '' (insert q (range d)) : Set (OnePoint ℚ))ᶜ ∈ 𝓝 (∞ : OnePoint ℚ) :=
        hopen.mem_nhds infty_notMem_image_coe
      have h2 : ((↑) '' (insert q (range d)) : Set (OnePoint ℚ)) ∈
          map (fun n => (d n : OnePoint ℚ)) atTop :=
        mem_map.2 (Eventually.of_forall fun n =>
          mem_image_of_mem _ (mem_insert_of_mem _ (mem_range_self n)))
      have h3 : (∅ : Set (OnePoint ℚ)) ∈
          𝓝 (∞ : OnePoint ℚ) ⊓ map (fun n => (d n : OnePoint ℚ)) atTop := by
        have := inter_mem_inf h1 h2
        rwa [compl_inter_self] at this
      exact hc.ne (empty_mem_iff_bot.1 h3)
    | coe r =>
      have hrq : r = q := by
        by_contra hrq
        have hdisj : Disjoint (𝓝 r) (𝓝 q) := disjoint_nhds_nhds.2 hrq
        have htend : map (fun n => (d n : OnePoint ℚ)) atTop ≤ 𝓝 (q : OnePoint ℚ) :=
          (continuous_coe.tendsto q).comp hdq
        have hcl : ClusterPt (r : OnePoint ℚ) (𝓝 (q : OnePoint ℚ)) := hc.mono htend
        rw [ClusterPt, nhds_coe_eq, nhds_coe_eq, ← map_inf coe_injective, map_neBot_iff] at hcl
        exact hcl.ne hdisj.eq_bot
      rw [← hrq]
      exact hcC
  by_cases h : ∞ ∈ C
  · exact (isClosed_iff_of_mem h).2 hD
  · refine (isClosed_iff_of_notMem h).2 ⟨hD, ?_⟩
    refine (isOpenEmbedding_coe.isInducing.isCompact_preimage_iff ?_).2 hC
    intro c hc
    by_contra hcr
    exact h (notMem_range_coe_iff.1 hcr ▸ hc)

/-- `OnePoint ℚ` is not Hausdorff: a neighbourhood of `0` disjoint from a neighbourhood of `∞`
would be contained in a compact subset of `ℚ`, and such subsets have empty interior. -/
theorem not_t2Space : ¬ T2Space (OnePoint ℚ) := by
  intro _
  obtain ⟨U, V, hU, hV, hUinf, hV0, hUV⟩ := t2_separation (infty_ne_coe (0 : ℚ))
  have hcomp : IsCompact ((↑) ⁻¹' U : Set ℚ)ᶜ := ((isOpen_iff_of_mem hUinf).1 hU).2
  have hint := Rat.interior_compact_eq_empty hcomp
  have hVopen : IsOpen ((↑) ⁻¹' V : Set ℚ) := hV.preimage continuous_coe
  have h0 : (0 : ℚ) ∈ interior ((↑) ⁻¹' U : Set ℚ)ᶜ := by
    refine mem_interior.2 ⟨_, ?_, hVopen, hV0⟩
    intro x hxV hxU
    exact disjoint_left.1 hUV hxU hxV
  rw [hint] at h0
  exact h0

/-- Two continuous maps from a compact Hausdorff space to `OnePoint ℚ`, one with value `∞` and the
other with a finite value at `k`, differ on a neighbourhood of `k`. -/
theorem eventually_ne_of_eq_infty {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {g h : K → OnePoint ℚ} (hg : Continuous g) (hh : Continuous h) {k : K}
    (hgk : g k = ∞) (hhk : h k ≠ ∞) : ∀ᶠ k' in 𝓝 k, g k' ≠ h k' := by
  have hopen : IsOpen (h ⁻¹' (range ((↑) : ℚ → OnePoint ℚ))) := isOpen_range_coe.preimage hh
  have hk : k ∈ h ⁻¹' (range ((↑) : ℚ → OnePoint ℚ)) := by
    obtain ⟨b, hb⟩ := ne_infty_iff_exists.1 hhk
    exact ⟨b, hb⟩
  obtain ⟨N, hNc, hkN, hNsub⟩ := exists_compact_subset hopen hk
  have hM : IsCompact (h '' N) := hNc.image hh
  have hMsub : h '' N ⊆ range ((↑) : ℚ → OnePoint ℚ) := image_subset_iff.2 hNsub
  have hMc : IsCompact ((↑) ⁻¹' (h '' N) : Set ℚ) :=
    (isOpenEmbedding_coe.isInducing.isCompact_preimage_iff hMsub).2 hM
  have hopen2 : IsOpen ((↑) '' ((↑) ⁻¹' (h '' N) : Set ℚ) : Set (OnePoint ℚ))ᶜ :=
    isOpen_compl_image_coe.2 ⟨hMc.isClosed, hMc⟩
  rw [image_preimage_eq_of_subset hMsub] at hopen2
  have hgk' : g k ∉ h '' N := by
    rw [hgk]
    intro hmem
    exact infty_notMem_range_coe (hMsub hmem)
  have h1 : g ⁻¹' (h '' N)ᶜ ∈ 𝓝 k := (hopen2.preimage hg).mem_nhds hgk'
  have h2 : N ∈ 𝓝 k := mem_interior_iff_mem_nhds.1 hkN
  filter_upwards [h1, h2] with k' hk1 hk2 heq
  exact hk1 (heq ▸ mem_image_of_mem h hk2)

/-- The coincidence set of two continuous maps from a compact Hausdorff space to `OnePoint ℚ` is
closed. -/
theorem isClosed_setOf_eq {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {g h : K → OnePoint ℚ} (hg : Continuous g) (hh : Continuous h) :
    IsClosed {k | g k = h k} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro k hk
  have hne : g k ≠ h k := hk
  change ∀ᶠ k' in 𝓝 k, g k' ≠ h k'
  by_cases hginf : g k = ∞
  · exact eventually_ne_of_eq_infty hg hh hginf (fun e => hne (hginf.trans e.symm))
  · by_cases hhinf : h k = ∞
    · exact (eventually_ne_of_eq_infty hh hg hhinf hginf).mono fun k' hk' e => hk' e.symm
    · obtain ⟨a, ha⟩ := ne_infty_iff_exists.1 hginf
      obtain ⟨b, hb⟩ := ne_infty_iff_exists.1 hhinf
      have hab : a ≠ b := by
        rintro rfl
        exact hne (ha.symm.trans hb)
      obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hab
      have h1 : g ⁻¹' ((↑) '' U) ∈ 𝓝 k :=
        ((isOpen_image_coe.2 hU).preimage hg).mem_nhds ⟨a, haU, ha⟩
      have h2 : h ⁻¹' ((↑) '' V) ∈ 𝓝 k :=
        ((isOpen_image_coe.2 hV).preimage hh).mem_nhds ⟨b, hbV, hb⟩
      filter_upwards [h1, h2] with k' hk1 hk2 heq
      obtain ⟨u, hu, hu'⟩ := hk1
      obtain ⟨v, hv, hv'⟩ := hk2
      have huv : u = v := coe_injective (hu'.trans (heq.trans hv'.symm))
      exact disjoint_left.1 hUV hu (huv ▸ hv)

/-- The square of `OnePoint ℚ` is not compactly generated: its diagonal has closed preimage under
every continuous map from a compact Hausdorff space, but it is not closed. -/
theorem not_compactlyGeneratedSpace_prod :
    ¬ CompactlyGeneratedSpace (OnePoint ℚ × OnePoint ℚ) := by
  intro _
  apply not_t2Space
  rw [t2_iff_isClosed_diagonal]
  refine CompactlyGeneratedSpace.isClosed' fun K _ _ _ f hf => ?_
  exact isClosed_setOf_eq (continuous_fst.comp hf) (continuous_snd.comp hf)

end Sol_CGWH_onePoint_rat_weaklyHausdorff_not_t2

open CGWH Sol_CGWH_onePoint_rat_weaklyHausdorff_not_t2 in
theorem solution :
    CompactlyGeneratedSpace (OnePoint ℚ) ∧ WeaklyHausdorffSpace (OnePoint ℚ) ∧
      ¬ T2Space (OnePoint ℚ) ∧ ¬ CompactlyGeneratedSpace (OnePoint ℚ × OnePoint ℚ) := by
  refine ⟨?_, ⟨fun K _ _ _ f hf => isClosed_of_isCompact (isCompact_range hf)⟩, not_t2Space,
    not_compactlyGeneratedSpace_prod⟩
  have := sequentialSpace
  infer_instance
