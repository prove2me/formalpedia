-- Prove2me | solution 1 for ClosingLemma.crTopology_one_eq_c1Topology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:17:42.02854+00:00
-- url     : https://prove2.me/submissions/c796f7c1-047c-49d3-8289-e7d280208781

import Mathlib
import Definitions.Def_BCWCentralizer_Basic
import Definitions.Def_ClosingLemma_DiffeoCrTopology

open scoped Manifold ContDiff Topology
open Set Filter Bundle

set_option linter.unusedSectionVars false

namespace CLAux

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "TM" => TangentBundle (𝓡 n) M

omit [IsManifold (𝓡 n) ∞ M] in
lemma mem_atlas1 {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) :
    e ∈ IsManifold.maximalAtlas (𝓡 n) 1 M :=
  IsManifold.maximalAtlas_subset_of_le (by exact_mod_cast le_top) he

example (g : BCWCentralizer.Diff1 n M) : ContMDiff (𝓡 n) (𝓡 n) 1 g := g.contMDiff

/-- chain rule identity -/
lemma key (g : BCWCentralizer.Diff1 n M) {φ ψ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) (hψ : ψ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M)
    {y : E} (hy : y ∈ φ.target) (hgy : g (φ.symm y) ∈ ψ.source) (w : E) :
    (tangentMap (𝓡 n) (𝓡 n) ψ (tangentMap (𝓡 n) (𝓡 n) g
      (tangentMap (𝓡 n) (𝓡 n) φ.symm (⟨y, w⟩ : TangentBundle (𝓡 n) E)))).2 =
      fderiv ℝ (ψ ∘ g ∘ φ.symm) y w := by
  have h1 := mdifferentiableAt_symm_of_mem_maximalAtlas (mem_atlas1 hφ) hy
  have h2 : MDifferentiableAt (𝓡 n) (𝓡 n) g (φ.symm y) :=
    (g.contMDiff.mdifferentiable one_ne_zero) _
  have h3 := mdifferentiableAt_of_mem_maximalAtlas (mem_atlas1 hψ) hgy
  have hc : mfderiv (𝓡 n) (𝓡 n) (ψ ∘ g ∘ φ.symm) y = (mfderiv (𝓡 n) (𝓡 n) ψ (g (φ.symm y))).comp
      ((mfderiv (𝓡 n) (𝓡 n) g (φ.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) φ.symm y)) := by
    rw [mfderiv_comp y h3 (h2.comp y h1), mfderiv_comp y h2 h1]; rfl
  have := congrArg (fun L => L w) hc
  simp only [mfderiv_eq_fderiv] at this
  exact this.symm

lemma ifd0 (F G : E → E) (y : E) :
    ‖iteratedFDeriv ℝ 0 F y - iteratedFDeriv ℝ 0 G y‖ = ‖F y - G y‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  rw [← map_sub, LinearIsometryEquiv.norm_map]

lemma ifd1_eq (F : E → E) (y : E) :
    iteratedFDeriv ℝ 1 F y = (continuousMultilinearCurryFin1 ℝ E E).symm (fderiv ℝ F y) := by
  ext m; simp [iteratedFDeriv_one_apply]

lemma ifd1 (F G : E → E) (y : E) :
    ‖iteratedFDeriv ℝ 1 F y - iteratedFDeriv ℝ 1 G y‖ = ‖fderiv ℝ F y - fderiv ℝ G y‖ := by
  rw [ifd1_eq, ifd1_eq, ← map_sub, LinearIsometryEquiv.norm_map]

lemma tm_ext {p q : TM} (h1 : p.proj = q.proj) (h2 : (p.2 : E) = (q.2 : E)) : p = q := by
  cases p; cases q; simp only at h1; subst h1; simp only at h2; subst h2; rfl

lemma contOn_tm {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) :
    ContinuousOn (tangentMap (𝓡 n) (𝓡 n) e) (π E (TangentSpace (𝓡 n)) ⁻¹' e.source) := by
  have h := ((contMDiffOn_of_mem_maximalAtlas (mem_atlas1 he))).continuousOn_tangentMapWithin
    le_rfl e.open_source.uniqueMDiffOn
  refine h.congr fun p hp => ?_
  exact (tangentMapWithin_eq_tangentMap (e.open_source.uniqueMDiffOn _ hp)
    (mdifferentiableAt_of_mem_maximalAtlas (mem_atlas1 he) hp)).symm

lemma contOn_tm_symm {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) :
    ContinuousOn (tangentMap (𝓡 n) (𝓡 n) e.symm)
      (π E (TangentSpace (𝓡 n)) ⁻¹' e.target) := by
  have h := ((contMDiffOn_symm_of_mem_maximalAtlas (mem_atlas1 he))).continuousOn_tangentMapWithin
    le_rfl e.open_target.uniqueMDiffOn
  refine h.congr fun p hp => ?_
  exact (tangentMapWithin_eq_tangentMap (e.open_target.uniqueMDiffOn _ hp)
    (mdifferentiableAt_symm_of_mem_maximalAtlas (mem_atlas1 he) hp)).symm

lemma tm_symm_tm {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) {v : TM} (hv : v.proj ∈ e.source) :
    tangentMap (𝓡 n) (𝓡 n) e.symm (tangentMap (𝓡 n) (𝓡 n) e v) = v := by
  apply tm_ext
  · exact e.left_inv hv
  · have h1 := mdifferentiableAt_symm_of_mem_maximalAtlas (mem_atlas1 he) (e.map_source hv)
    have h2 := mdifferentiableAt_of_mem_maximalAtlas (mem_atlas1 he) hv
    have hc := mfderiv_comp v.proj h1 h2
    have hid : (e.symm ∘ e : M → M) =ᶠ[𝓝 v.proj] id := by
      filter_upwards [e.open_source.mem_nhds hv] with x hx using e.left_inv hx
    rw [hid.mfderiv_eq, mfderiv_id] at hc
    have := congrArg (fun L => L v.2) hc
    exact this.symm

/-- `C¹` local representative is `C¹` on the natural open set. -/
lemma contDiffOn_rep (g : BCWCentralizer.Diff1 n M) {φ ψ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) (hψ : ψ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) :
    ContDiffOn ℝ 1 (ψ ∘ g ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (g ⁻¹' ψ.source)) := by
  rw [← contMDiffOn_iff_contDiffOn]
  have h1 := (contMDiffOn_symm_of_mem_maximalAtlas (mem_atlas1 hφ)).mono
    (inter_subset_left (t := φ.symm ⁻¹' (g ⁻¹' ψ.source)))
  have h2 := g.contMDiff.comp_contMDiffOn h1
  exact (contMDiffOn_of_mem_maximalAtlas (mem_atlas1 hψ)).comp h2 (fun y hy => hy.2)

lemma isOpen_rep (g : BCWCentralizer.Diff1 n M) (φ ψ : OpenPartialHomeomorph M E) :
    IsOpen (φ.target ∩ φ.symm ⁻¹' (g ⁻¹' ψ.source)) :=
  φ.continuousOn_symm.isOpen_inter_preimage φ.open_target (ψ.open_source.preimage g.continuous)

lemma rep_eq (g : BCWCentralizer.Diff1 n M) {φ ψ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) (hψ : ψ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M)
    {v : TM} (h1 : v.proj ∈ φ.source) (h2 : g v.proj ∈ ψ.source) :
    tangentMap (𝓡 n) (𝓡 n) g v = tangentMap (𝓡 n) (𝓡 n) ψ.symm
      (⟨ψ (g (φ.symm (φ v.proj))), fderiv ℝ (ψ ∘ g ∘ φ.symm) (φ v.proj)
        (tangentMap (𝓡 n) (𝓡 n) φ v).2⟩ : TangentBundle (𝓡 n) E) := by
  have h2' : g (φ.symm (φ v.proj)) ∈ ψ.source := by rwa [φ.left_inv h1]
  have e2 : tangentMap (𝓡 n) (𝓡 n) ψ (tangentMap (𝓡 n) (𝓡 n) g
      (tangentMap (𝓡 n) (𝓡 n) φ.symm (tangentMap (𝓡 n) (𝓡 n) φ v))) =
      (⟨ψ (g (φ.symm (φ v.proj))), fderiv ℝ (ψ ∘ g ∘ φ.symm) (φ v.proj)
        (tangentMap (𝓡 n) (𝓡 n) φ v).2⟩ : TangentBundle (𝓡 n) E) := by
    apply tm_ext (M := E)
    · rfl
    · exact key g hφ hψ (φ.map_source h1) h2' _
  calc tangentMap (𝓡 n) (𝓡 n) g v
      = tangentMap (𝓡 n) (𝓡 n) ψ.symm (tangentMap (𝓡 n) (𝓡 n) ψ (tangentMap (𝓡 n) (𝓡 n) g v)) :=
        (tm_symm_tm hψ h2).symm
    _ = tangentMap (𝓡 n) (𝓡 n) ψ.symm (tangentMap (𝓡 n) (𝓡 n) ψ (tangentMap (𝓡 n) (𝓡 n) g
          (tangentMap (𝓡 n) (𝓡 n) φ.symm (tangentMap (𝓡 n) (𝓡 n) φ v)))) := by
        rw [tm_symm_tm hφ h1]
    _ = _ := by rw [e2]

lemma snd_cont : Continuous (fun q : TangentBundle (𝓡 n) E => (q.2 : E)) :=
  continuous_snd.comp (tangentBundleModelSpaceHomeomorph (𝓡 n)).continuous

lemma dirB : @Continuous (BCWCentralizer.Diff1 n M) _ (ClosingLemma.crTopology 1) _
    BCWCentralizer.tangentMapCM := by
  let _ : TopologicalSpace (BCWCentralizer.Diff1 n M) := ClosingLemma.crTopology 1
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  apply ContinuousMap.continuous_of_continuous_uncurry
  rw [continuous_iff_continuousAt]
  rintro ⟨g0, v0⟩
  set x0 := v0.proj with hx0
  set φ := chartAt E x0 with hφdef
  set ψ := chartAt E (g0 x0) with hψdef
  have hφ : φ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := IsManifold.chart_mem_maximalAtlas x0
  have hψ : ψ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hU : φ.source ∩ g0 ⁻¹' ψ.source ∈ 𝓝 x0 :=
    inter_mem (φ.open_source.mem_nhds (mem_chart_source E x0))
      (g0.continuous.continuousAt.preimage_mem_nhds
        (ψ.open_source.mem_nhds (mem_chart_source E _)))
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hN : ∀ ε > 0, ClosingLemma.crBasicNhd 1 g0 φ ψ K ε ∈ 𝓝 g0 := by
    intro ε hε
    apply IsOpen.mem_nhds
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      exact ⟨g0, φ, ψ, K, ε, hφ, hψ, hKc, fun x hx => (hKU hx).1,
        fun x hx => (hKU hx).2, hε, rfl⟩
    · exact ⟨fun x hx => (hKU hx).2, fun y _ k _ => by simpa using hε⟩
  set A : BCWCentralizer.Diff1 n M → E → E := fun g => ψ ∘ g ∘ φ.symm with hA
  have hev : ∀ ε > 0, ∀ᶠ p : BCWCentralizer.Diff1 n M × TM in 𝓝 (g0, v0),
      p.1 ∈ ClosingLemma.crBasicNhd 1 g0 φ ψ K ε ∧ p.2.proj ∈ K := by
    intro ε hε
    exact ((continuous_fst.tendsto (g0, v0)).eventually (hN ε hε)).and
      ((continuous_snd.tendsto (g0, v0)).eventually ((FiberBundle.continuous_proj E (TangentSpace (𝓡 n))).continuousAt
        hKn))
  have hUA : TendstoUniformlyOn (fun p : BCWCentralizer.Diff1 n M × TM => A p.1) (A g0)
      (𝓝 (g0, v0)) (φ '' K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hev ε hε] with p hp y hy
    have := hp.1.2 y hy 0 (Nat.zero_le _)
    rw [ifd0] at this
    rw [dist_comm, dist_eq_norm]; exact this
  have hUD : TendstoUniformlyOn (fun p : BCWCentralizer.Diff1 n M × TM => fderiv ℝ (A p.1))
      (fderiv ℝ (A g0)) (𝓝 (g0, v0)) (φ '' K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hev ε hε] with p hp y hy
    have := hp.1.2 y hy 1 le_rfl
    rw [ifd1] at this
    rw [dist_comm, dist_eq_norm]; exact this
  have hy0 : φ x0 ∈ φ.target ∩ φ.symm ⁻¹' (g0 ⁻¹' ψ.source) := by
    refine ⟨φ.map_source (mem_chart_source E x0), ?_⟩
    simp only [mem_preimage]; rw [φ.left_inv (mem_chart_source E x0)]
    exact mem_chart_source E _
  have hcd := contDiffOn_rep g0 hφ hψ
  have hopen := isOpen_rep g0 φ ψ
  have hcA : ContinuousWithinAt (A g0) (φ '' K) (φ x0) :=
    ((hcd.continuousOn).continuousAt (hopen.mem_nhds hy0)).continuousWithinAt
  have hcD : ContinuousWithinAt (fderiv ℝ (A g0)) (φ '' K) (φ x0) :=
    ((hcd.continuousOn_fderiv_of_isOpen hopen le_rfl).continuousAt
      (hopen.mem_nhds hy0)).continuousWithinAt
  have hy : Tendsto (fun p : BCWCentralizer.Diff1 n M × TM => φ p.2.proj) (𝓝 (g0, v0))
      (𝓝[φ '' K] (φ x0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((φ.continuousAt (mem_chart_source E x0)).comp
        (FiberBundle.continuous_proj E (TangentSpace (𝓡 n))).continuousAt).tendsto.comp
          (continuous_snd.tendsto (g0, v0))
    · filter_upwards [hev 1 one_pos] with p hp using mem_image_of_mem _ hp.2
  have hw : Tendsto (fun p : BCWCentralizer.Diff1 n M × TM =>
      ((tangentMap (𝓡 n) (𝓡 n) φ p.2).2 : E)) (𝓝 (g0, v0))
      (𝓝 ((tangentMap (𝓡 n) (𝓡 n) φ v0).2 : E)) := by
    have h := (contOn_tm hφ).continuousAt
      (((FiberBundle.continuous_proj E (TangentSpace (𝓡 n))).isOpen_preimage _
        φ.open_source).mem_nhds (mem_chart_source E x0))
    exact ((snd_cont.continuousAt).comp h).tendsto.comp (continuous_snd.tendsto (g0, v0))
  have ha := hUA.tendsto_comp hcA hy
  have hb : Tendsto (fun p : BCWCentralizer.Diff1 n M × TM =>
      fderiv ℝ (A p.1) (φ p.2.proj) ((tangentMap (𝓡 n) (𝓡 n) φ p.2).2 : E)) (𝓝 (g0, v0))
      (𝓝 (fderiv ℝ (A g0) (φ x0) ((tangentMap (𝓡 n) (𝓡 n) φ v0).2 : E))) :=
    (isBoundedBilinearMap_apply.continuous.tendsto _).comp ((hUD.tendsto_comp hcD hy).prodMk_nhds hw)
  set G : BCWCentralizer.Diff1 n M × TM → TangentBundle (𝓡 n) E := fun p =>
    ⟨A p.1 (φ p.2.proj), fderiv ℝ (A p.1) (φ p.2.proj) ((tangentMap (𝓡 n) (𝓡 n) φ p.2).2 : E)⟩
    with hG
  have hGt : Tendsto G (𝓝 (g0, v0)) (𝓝 (G (g0, v0))) := by
    have := ((tangentBundleModelSpaceHomeomorph (𝓡 n)).symm.continuous.tendsto _).comp
      (ha.prodMk_nhds hb)
    exact this
  have hG0 : (G (g0, v0)).proj ∈ ψ.target := by
    show ψ (g0 (φ.symm (φ x0))) ∈ ψ.target
    exact ψ.map_source hy0.2
  have hFt := ((contOn_tm_symm hψ).continuousAt
      (((FiberBundle.continuous_proj E (TangentSpace (𝓡 n))).isOpen_preimage _
        ψ.open_target).mem_nhds hG0)).tendsto.comp hGt
  have hEq : ∀ᶠ p : BCWCentralizer.Diff1 n M × TM in 𝓝 (g0, v0),
      tangentMap (𝓡 n) (𝓡 n) ψ.symm (G p) = Function.uncurry (fun g v => BCWCentralizer.tangentMapCM g v) p := by
    filter_upwards [hev 1 one_pos] with p hp
    exact (rep_eq p.1 hφ hψ (hKU hp.2).1 (hp.1.1 hp.2)).symm
  have h0 := hEq.self_of_nhds
  unfold ContinuousAt
  rw [← h0]
  exact hFt.congr' hEq

lemma dirA (S : Set (BCWCentralizer.Diff1 n M)) (hS : S ∈ ClosingLemma.crBasicNhds (M := M) 1) :
    IsOpen[BCWCentralizer.c1Topology] S := by
  obtain ⟨f, φ, ψ, K, ε, hφ, hψ, hKc, hKφ, hfK, hε, rfl⟩ := hS
  let _ : TopologicalSpace (BCWCentralizer.Diff1 n M) := BCWCentralizer.c1Topology
  have : LocallyCompactSpace (ModelProd E E) := inferInstanceAs (LocallyCompactSpace (E × E))
  have : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (ModelProd E E) TM
  have hJ : Continuous (fun p : BCWCentralizer.Diff1 n M × TM =>
      tangentMap (𝓡 n) (𝓡 n) p.1 p.2) :=
    continuous_eval.comp ((continuous_induced_dom (f := BCWCentralizer.tangentMapCM)).prodMap
      continuous_id)
  have hproj := FiberBundle.continuous_proj E (TangentSpace (𝓡 n) : M → Type _)
  have hprojE := FiberBundle.continuous_proj E (TangentSpace (𝓡 n) : E → Type _)
  refine (@isOpen_iff_mem_nhds (BCWCentralizer.Diff1 n M) BCWCentralizer.c1Topology _).2 ?_
  intro g0 hg0
  set A : BCWCentralizer.Diff1 n M → E → E := fun g => ψ ∘ g ∘ φ.symm with hA
  set L := φ '' K with hL
  have hLc : IsCompact L := hKc.image_of_continuousOn (φ.continuousOn.mono hKφ)
  have hLU : ∀ g : BCWCentralizer.Diff1 n M, MapsTo g K ψ.source →
      L ⊆ φ.target ∩ φ.symm ⁻¹' (g ⁻¹' ψ.source) := by
    rintro g hg _ ⟨x, hx, rfl⟩
    refine ⟨φ.map_source (hKφ hx), ?_⟩
    simp only [mem_preimage]; rw [φ.left_inv (hKφ hx)]; exact hg hx
  have hLg0 := hLU g0 hg0.1
  have hLf := hLU f hfK
  have hcD0 := (contDiffOn_rep g0 hφ hψ).continuousOn_fderiv_of_isOpen (isOpen_rep g0 φ ψ) le_rfl
  have hcDf := (contDiffOn_rep f hφ hψ).continuousOn_fderiv_of_isOpen (isOpen_rep f φ ψ) le_rfl
  have hcAf := (contDiffOn_rep f hφ hψ).continuousOn
  -- margin
  obtain ⟨M0, hM0, hM0L⟩ : ∃ M0 : ℝ, M0 < ε ∧
      ∀ y ∈ L, ‖fderiv ℝ (A g0) y - fderiv ℝ (A f) y‖ ≤ M0 := by
    rcases L.eq_empty_or_nonempty with hLe | hLne
    · exact ⟨0, hε, by simp [hLe]⟩
    · have hcont : ContinuousOn (fun y => ‖fderiv ℝ (A g0) y - fderiv ℝ (A f) y‖) L :=
        ((hcD0.mono hLg0).sub (hcDf.mono hLf)).norm
      obtain ⟨y1, hy1, hmax⟩ := hLc.exists_isMaxOn hLne hcont
      refine ⟨_, ?_, fun y hy => hmax hy⟩
      have := hg0.2 y1 hy1 1 le_rfl
      rw [ifd1] at this; exact this
  set m' := (M0 + ε) / 2 with hm'
  have hm'ε : m' < ε := by rw [hm']; linarith
  have hM0m' : M0 < m' := by rw [hm']; linarith
  set Q := L ×ˢ Metric.closedBall (0 : E) 1 with hQ
  have hQc : IsCompact Q := hLc.prod (isCompact_closedBall _ _)
  have tube : ∀ᶠ g in 𝓝 g0, ∀ q ∈ Q, g (φ.symm q.1) ∈ ψ.source ∧
      ‖A g q.1 - A f q.1‖ < ε ∧
      ‖fderiv ℝ (A g) q.1 q.2 - fderiv ℝ (A f) q.1 q.2‖ < m' := by
    apply hQc.eventually_forall_of_forall_eventually
    rintro ⟨y0, w0⟩ ⟨hy0, hw0⟩
    have hy0t : y0 ∈ φ.target := (hLg0 hy0).1
    -- the composite maps
    set c : E × E → TangentBundle (𝓡 n) E := fun q => (tangentBundleModelSpaceHomeomorph (𝓡 n)).symm q
      with hc
    have hcc : Continuous c := (tangentBundleModelSpaceHomeomorph (𝓡 n)).symm.continuous
    have hT1 : ContinuousAt (fun q : E × E => tangentMap (𝓡 n) (𝓡 n) φ.symm (c q)) (y0, w0) :=
      (contOn_tm_symm hφ).continuousAt ((hprojE.isOpen_preimage _ φ.open_target).mem_nhds
        hy0t) |>.comp hcc.continuousAt
    have hT2 : ContinuousAt (fun p : BCWCentralizer.Diff1 n M × (E × E) =>
        tangentMap (𝓡 n) (𝓡 n) p.1 (tangentMap (𝓡 n) (𝓡 n) φ.symm (c p.2))) (g0, (y0, w0)) :=
      hJ.continuousAt.comp (continuousAt_fst.prodMk (hT1.comp_of_eq continuousAt_snd rfl))
    have hin : (tangentMap (𝓡 n) (𝓡 n) g0 (tangentMap (𝓡 n) (𝓡 n) φ.symm (c (y0, w0)))).proj ∈
        ψ.source := (hLg0 hy0).2
    have hT3 : ContinuousAt (fun p : BCWCentralizer.Diff1 n M × (E × E) =>
        tangentMap (𝓡 n) (𝓡 n) ψ (tangentMap (𝓡 n) (𝓡 n) p.1
          (tangentMap (𝓡 n) (𝓡 n) φ.symm (c p.2)))) (g0, (y0, w0)) :=
      ((contOn_tm hψ).continuousAt ((hproj.isOpen_preimage _ ψ.open_source).mem_nhds hin)).comp_of_eq
        hT2 rfl
    have ev1 : ∀ᶠ p : BCWCentralizer.Diff1 n M × (E × E) in 𝓝 (g0, (y0, w0)),
        p.1 (φ.symm p.2.1) ∈ ψ.source :=
      (hproj.continuousAt.comp hT2).preimage_mem_nhds (ψ.open_source.mem_nhds hin)
    have ev2 : ∀ᶠ p : BCWCentralizer.Diff1 n M × (E × E) in 𝓝 (g0, (y0, w0)),
        p.2.1 ∈ φ.target :=
      (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
        (φ.open_target.mem_nhds hy0t)
    -- value part
    have hval : ContinuousAt (fun p : BCWCentralizer.Diff1 n M × (E × E) =>
        A p.1 p.2.1 - A f p.2.1) (g0, (y0, w0)) := by
      refine (hprojE.continuousAt.comp hT3).sub ?_
      exact ((hcAf.continuousAt ((isOpen_rep f φ ψ).mem_nhds (hLf hy0))).comp_of_eq
        (continuous_fst.comp continuous_snd).continuousAt rfl)
    have hval0 : ‖A g0 y0 - A f y0‖ < ε := by
      have := hg0.2 y0 hy0 0 (Nat.zero_le _); rw [ifd0] at this; exact this
    -- derivative part
    have hder : ContinuousAt (fun p : BCWCentralizer.Diff1 n M × (E × E) =>
        fderiv ℝ (A p.1) p.2.1 p.2.2 - fderiv ℝ (A f) p.2.1 p.2.2) (g0, (y0, w0)) := by
      refine ContinuousAt.sub ?_ ?_
      · refine ((snd_cont.continuousAt).comp hT3).congr ?_
        filter_upwards [ev1, ev2] with p h1 h2
        exact key p.1 hφ hψ h2 h1 p.2.2
      · exact ContinuousAt.clm_apply
          ((hcDf.continuousAt ((isOpen_rep f φ ψ).mem_nhds (hLf hy0))).comp_of_eq
            (continuous_fst.comp continuous_snd).continuousAt rfl)
          (continuous_snd.comp continuous_snd).continuousAt
    have hder0 : ‖fderiv ℝ (A g0) y0 w0 - fderiv ℝ (A f) y0 w0‖ < m' := by
      rw [← ContinuousLinearMap.sub_apply]
      refine lt_of_le_of_lt (ContinuousLinearMap.le_opNorm _ _) ?_
      have hw1 : ‖w0‖ ≤ 1 := by simpa using hw0
      calc _ ≤ ‖fderiv ℝ (A g0) y0 - fderiv ℝ (A f) y0‖ * 1 :=
            mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
        _ ≤ M0 := by rw [mul_one]; exact hM0L y0 hy0
        _ < m' := hM0m'
    filter_upwards [ev1, hval.norm.eventually (gt_mem_nhds hval0),
      hder.norm.eventually (gt_mem_nhds hder0)] with p h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [tube] with g hg
  refine ⟨fun x hx => ?_, fun y hy k hk => ?_⟩
  · have := (hg (φ x, 0) ⟨mem_image_of_mem _ hx, Metric.mem_closedBall_self zero_le_one⟩).1
    rwa [φ.left_inv (hKφ hx)] at this
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · rw [ifd0]
      exact (hg (y, 0) ⟨hy, Metric.mem_closedBall_self zero_le_one⟩).2.1
    · rw [ifd1]
      refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm ?_ fun w hw => ?_) hm'ε
      · have := hM0L
        exact le_trans (norm_nonneg _) (le_of_lt (hg (y, 0) ⟨hy,
          Metric.mem_closedBall_self zero_le_one⟩).2.2)
      · rw [ContinuousLinearMap.sub_apply]
        exact (hg (y, w) ⟨hy, by simp [hw]⟩).2.2.le

end CLAux

open ClosingLemma in
theorem solution {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :
    (crTopology 1 : TopologicalSpace (Diff n M 1)) =
      (BCWCentralizer.c1Topology : TopologicalSpace (BCWCentralizer.Diff1 n M)) := by
  apply le_antisymm
  · exact continuous_iff_le_induced.mp CLAux.dirB
  · exact TopologicalSpace.le_generateFrom_iff_subset_isOpen.2 fun S hS => CLAux.dirA S hS
