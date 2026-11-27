-- Prove2me | solution 1 for DirKKTBilevel.VP.Supplement.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:51.483734+00:00
-- url     : https://prove2.me/submissions/4f557164-45d5-4034-8ec1-2e12fc2c4dbe

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

open DirKKTBilevel
open DirKKTBilevel.VP
open DirKKTBilevel.VP.Supplement

/-- Proposition 4.4, p. 18: if the solution map `S` is inner semi-continuous at `(x̄, ȳ) ∈ gph S` in
direction `u` and `𝓕` is RCR-regular at `(x̄, ȳ)`, then `V` is directionally differentiable at
`x̄` in direction `u` and `V'(x̄; u) = min_{v ∈ L(x̄,ȳ;u)} ∇f(x̄, ȳ)(u, v)
= max_{λ ∈ Λ(x̄,ȳ)} ∇ₓL(x̄, ȳ; λ)u`, both extrema attained. -/
theorem solution {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : E n) (y : E m) (u : E n)
    (hISC : IsDirInnerSemicont f g x y u) (hRCR : IsRCR g x y) :
    ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
      IsLeast (linVals f g x u y) dV ∧ IsGreatest (lagVals f g x u y) dV := by
        have L1 : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (A : Set ι) (c₀ : ι → V) (n : V)
          (h : ∀ v, (∀ i ∈ A, inner ℝ (c₀ i) v ≤ 0) → inner ℝ n v ≤ 0),
            ∃ (T : Finset ι) (l : ι → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i, i ∉ T → l i = 0) ∧
            (∀ i ∈ T, i ∈ A) ∧ LinearIndepOn ℝ c₀ (T : Set ι) ∧ n = ∑ i, l i • c₀ i := by
          intro V _ _ _ ι _ A c₀ n h
          classical
          have : CompleteSpace V := FiniteDimensional.complete ℝ V
          set c : ι → V := fun i => if i ∈ A then c₀ i else 0 with hc
          -- Caratheodory
          have car : ∀ (x : V) (N : ℕ) (T : Finset ι) (l : ι → ℝ), T.card ≤ N → (∀ i, 0 ≤ l i) →
              (∀ i, i ∉ T → l i = 0) → x = ∑ i, l i • c i →
              ∃ (T : Finset ι) (l : ι → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i, i ∉ T → l i = 0) ∧
                LinearIndepOn ℝ c (T : Set ι) ∧ x = ∑ i, l i • c i := by
            intro x N
            induction N with
            | zero =>
              intro T l hT hl hlT hx
              have : T = ∅ := by simpa using hT
              subst this
              exact ⟨∅, l, hl, hlT, by simp, hx⟩
            | succ N ih =>
              intro T l hT hl hlT hx
              by_cases hli : LinearIndepOn ℝ c (T : Set ι)
              · exact ⟨T, l, hl, hlT, hli, hx⟩
              rw [linearIndepOn_finset_iff] at hli
              push Not at hli
              obtain ⟨f, hf0, i0, hi0, hfi0⟩ := hli
              -- sign normalise
              obtain ⟨μ, hμ0, j0, hj0, hμj0⟩ : ∃ μ : ι → ℝ, ∑ i ∈ T, μ i • c i = 0 ∧ ∃ j ∈ T, 0 < μ j := by
                rcases lt_or_gt_of_ne hfi0 with h1 | h1
                · refine ⟨fun i => - f i, ?_, i0, hi0, by simpa using h1⟩
                  simp [hf0]
                · exact ⟨f, hf0, i0, hi0, h1⟩
              have hne : (T.filter (fun i => 0 < μ i)).Nonempty := ⟨j0, by simp [hj0, hμj0]⟩
              obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image _ (fun i => l i / μ i) hne
              simp only [Finset.mem_filter] at hk hkmin
              set s := l k / μ k with hs
              have hs0 : 0 ≤ s := div_nonneg (hl k) hk.2.le
              have hsum : ∑ i, (if i ∈ T then μ i else 0) • c i = 0 := by
                rw [← hμ0]
                simp [ite_smul, Finset.sum_ite_mem]
              refine ih (T.erase k) (fun i => l i - s * (if i ∈ T then μ i else 0)) ?_ ?_ ?_ ?_
              · rw [Finset.card_erase_of_mem hk.1]; omega
              · intro i
                split_ifs with hi
                · by_cases hp : 0 < μ i
                  · have := hkmin i ⟨hi, hp⟩
                    rw [le_div_iff₀ hp] at this
                    linarith
                  · have : s * μ i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (not_lt.mp hp)
                    linarith [hl i]
                · simpa using hl i
              · intro i hi
                by_cases hik : i = k
                · subst hik
                  have := hk.2.ne'
                  simp [hk.1, hs, div_mul_cancel₀ _ this]
                · have : i ∉ T := fun hT => hi (Finset.mem_erase.mpr ⟨hik, hT⟩)
                  simp [this, hlT i this]
              · rw [hx]
                simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hsum]
                simp
          -- the cone
          let C : PointedCone ℝ V :=
            { carrier := {x | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ x = ∑ i, l i • c i}
              add_mem' := by
                rintro a b ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
                exact ⟨fun i => l i + l' i, fun i => add_nonneg (hl i) (hl' i), by
                  simp [add_smul, Finset.sum_add_distrib]⟩
              zero_mem' := ⟨0, by simp, by simp⟩
              smul_mem' := by
                rintro a b ⟨l, hl, rfl⟩
                exact ⟨fun i => a * l i, fun i => mul_nonneg a.2 (hl i), by
                  simp only [Finset.smul_sum, mul_smul]; rfl⟩ }
          have hclosed : IsClosed (C : Set V) := by
            have hU : (C : Set V) = ⋃ T ∈ {T : Finset ι | LinearIndepOn ℝ c (T : Set ι)},
                {x | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ i, i ∉ T → l i = 0) ∧ x = ∑ i, l i • c i} := by
              ext x
              simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
              constructor
              · rintro ⟨l, hl, hx⟩
                obtain ⟨T, l', h1, h2, h3, h4⟩ := car x _ Finset.univ l le_rfl hl (by simp) hx
                exact ⟨T, h3, l', h1, h2, h4⟩
              · rintro ⟨T, _, l, hl, _, hx⟩
                exact ⟨l, hl, hx⟩
            rw [hU]
            refine Set.Finite.isClosed_biUnion (Set.toFinite _) ?_
            intro T hT
            have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : T => c i)) = ⊥ := by
              refine LinearMap.ker_eq_bot'.mpr fun f hf => funext fun i => ?_
              rw [Fintype.linearCombination_apply] at hf
              exact Fintype.linearIndependent_iff.mp hT f hf i
            have hemb := LinearMap.isClosedEmbedding_of_injective hinj
            have hcl : IsClosed ((Fintype.linearCombination ℝ (fun i : T => c i)) '' {f | ∀ i, 0 ≤ f i}) := by
              apply hemb.isClosedMap
              simp only [Set.setOf_forall]
              exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
            convert hcl using 1
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_image]
            constructor
            · rintro ⟨l, hl, hlT, rfl⟩
              refine ⟨fun i => l i, fun i => hl i, ?_⟩
              rw [Fintype.linearCombination_apply]
              rw [Finset.sum_coe_sort T (fun i => l i • c i)]
              exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simp [hlT i hi])
            · rintro ⟨f, hf, rfl⟩
              refine ⟨fun i => if hi : i ∈ T then f ⟨i, hi⟩ else 0, ?_, ?_, ?_⟩
              · intro i; dsimp only; split_ifs with hi
                · exact hf _
                · exact le_rfl
              · intro i hi; simp [hi]
              · rw [Fintype.linearCombination_apply, ← Finset.sum_subset (Finset.subset_univ T)]
                · rw [← Finset.sum_coe_sort T]
                  simp
                · intro i _ hi; simp [hi]
          let PC : ProperCone ℝ V := ⟨C, hclosed⟩
          have hmem : n ∈ C := by
            by_contra hn
            obtain ⟨y, hy1, hy2⟩ := ProperCone.hyperplane_separation' (x₀ := n) PC hn
            have := h (-y) ?_
            · rw [inner_neg_right] at this; linarith
            · intro i hi
              have h1 : 0 ≤ inner ℝ (c₀ i) y := by
                apply hy1
                show ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ c₀ i = ∑ i, l i • c i
                refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
                · intro j; dsimp only; split_ifs <;> norm_num
                · have : c i = c₀ i := by simp [hc, hi]
                  simp [ite_smul, this]
              rw [inner_neg_right]; linarith
          obtain ⟨l0, hl0, hn0⟩ := hmem
          obtain ⟨T, l, h1, h2, h3, h4⟩ := car n _ Finset.univ l0 le_rfl hl0 (by simp) hn0
          have hTA : ∀ i ∈ T, i ∈ A := by
            intro i hi
            by_contra hA
            have := LinearIndepOn.ne_zero (R := ℝ) h3 (i := i) hi
            simp [hc, hA] at this
          refine ⟨T, l, h1, h2, hTA, ?_, ?_⟩
          · refine (linearIndepOn_congr ?_).mp h3
            intro i hi
            simp [hc, hTA i hi]
          · rw [h4]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hi : i ∈ T
            · simp [hc, hTA i hi]
            · simp [h2 i hi]
        have L2 : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (H : ι → V → ℝ) (b : ι → V → V) (z v : V)
          (hH : ∀ i y, HasFDerivAt (H i) (innerSL ℝ (b i y)) y) (hb : ∀ i, Continuous (b i))
          (K : Set ι) (hK0 : ∀ i ∈ K, H i z = 0) (hKv : ∀ i ∈ K, inner ℝ (b i z) v = 0)
          (hr : ∀ K' : Set ι, ∀ᶠ y in 𝓝 z,
            Module.finrank ℝ (Submodule.span ℝ ((fun i => b i y) '' K')) =
            Module.finrank ℝ (Submodule.span ℝ ((fun i => b i z) '' K'))),
            ∃ γ : ℝ → V, γ 0 = z ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 (0:ℝ), ∀ i ∈ K, H i (γ t) = 0 := by
          intro V _ _ _ ι _ H b z v hH hb K hK0 hKv hr
          classical
          have : CompleteSpace V := FiniteDimensional.complete ℝ V
          obtain ⟨J, hJK, -, hJspan, hJli⟩ := exists_linearIndepOn_extension (K := ℝ) (v := fun i => b i z)
            (s := ∅) (t := K) (by simp) (Set.empty_subset _)
          -- dual vectors
          have hd : ∀ j : ι, ∃ d : V, j ∈ J → ∀ i ∈ J, inner ℝ (b i z) d = if i = j then 1 else 0 := by
            intro j
            by_cases hj : j ∈ J
            · have hli : LinearIndependent ℝ (fun i : J => b i z) := hJli
              obtain ⟨φ, hφ⟩ := LinearMap.exists_extend
                ((Finsupp.lapply (⟨j, hj⟩ : J)).comp hli.repr : _ →ₗ[ℝ] ℝ)
              refine ⟨(InnerProductSpace.toDual ℝ V).symm (LinearMap.toContinuousLinearMap φ), ?_⟩
              intro _ i hi
              rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
              have hmem : b i z ∈ Submodule.span ℝ (Set.range (fun i : J => b i z)) :=
                Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
              have h1 := LinearMap.congr_fun hφ ⟨b i z, hmem⟩
              simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
              have h2 : hli.repr ⟨b i z, hmem⟩ = Finsupp.single (⟨i, hi⟩ : J) 1 :=
                hli.repr_eq_single _ _ rfl
              simp only [LinearMap.coe_toContinuousLinearMap']
              rw [h1]
              simp only [LinearEquiv.coe_coe, h2, Finsupp.lapply_apply, Finsupp.single_apply, Subtype.mk.injEq]
            · exact ⟨0, fun h => absurd h hj⟩
          choose d hd using hd
          have hHc : ∀ i, ContDiff ℝ 1 (H i) := by
            intro i
            rw [contDiff_one_iff_hasFDerivAt]
            exact ⟨fun y => innerSL ℝ (b i y), (innerSL ℝ).continuous.comp (hb i), hH i⟩
          set Ψ : V → V := fun y => (y - z) +
            ∑ j ∈ J.toFinset, (H j y - innerSL ℝ (b j z) (y - z)) • d j with hΨ
          have hΨc : ContDiff ℝ 1 Ψ := by
            refine (contDiff_id.sub contDiff_const).add (ContDiff.sum fun j _ => ?_)
            refine ContDiff.smul ((hHc j).sub ?_) contDiff_const
            exact (innerSL ℝ (b j z)).contDiff.comp (contDiff_id.sub contDiff_const)
          have hΨz : Ψ z = 0 := by
            simp only [hΨ, sub_self, map_zero, zero_add, sub_zero]
            refine Finset.sum_eq_zero fun j hj => ?_
            rw [hK0 j (hJK (by simpa using hj)), zero_smul]
          have hΨ' : HasFDerivAt Ψ ((ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V)) z := by
            have h0 : HasFDerivAt (fun y : V => y - z) (ContinuousLinearMap.id ℝ V) z :=
              (hasFDerivAt_id z).sub_const z
            have h1 : HasFDerivAt Ψ (ContinuousLinearMap.id ℝ V + ∑ j ∈ J.toFinset,
                ((innerSL ℝ (b j z) - (innerSL ℝ (b j z)).comp (ContinuousLinearMap.id ℝ V)).smulRight
                  (d j))) z := by
              refine h0.add (HasFDerivAt.fun_sum fun j _ => ?_)
              refine HasFDerivAt.smul_const ?_ (d j)
              exact (hH j z).sub (((innerSL ℝ (b j z)).hasFDerivAt).comp z h0)
            convert h1 using 1
            ext w
            simp
          have hs : HasStrictFDerivAt Ψ ((ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V)) z :=
            hΨc.contDiffAt.hasStrictFDerivAt' hΨ' one_ne_zero
          set inv := hs.localInverse with hinv
          have hinvc : ContDiffAt ℝ 1 inv (Ψ z) := hΨc.contDiffAt.to_localInverse hΨ' one_ne_zero
          have hinvs := hs.to_localInverse
          have hright := hs.eventually_right_inverse
          have hinv0 : inv (Ψ z) = z := hs.localInverse_apply_image
          rw [hΨz] at hinvc hinvs hright hinv0
          have hlin : Continuous (fun t : ℝ => t • v) := by fun_prop
          have hlin0 : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
            have h := hlin.tendsto 0
            rwa [zero_smul] at h
          set γ : ℝ → V := fun t => inv (t • v) with hγ
          have hγ0 : γ 0 = z := by simp [hγ, hinv0]
          have hγd : HasDerivAt γ v 0 := by
            have h1 : HasFDerivAt inv ((ContinuousLinearEquiv.refl ℝ V).symm : V →L[ℝ] V) ((0:ℝ) • v) := by
              rw [zero_smul]; exact hinvs.hasFDerivAt
            have h2 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
              simpa using (hasDerivAt_id (0:ℝ)).smul_const v
            exact h1.comp_hasDerivAt (0:ℝ) h2
          have hdiff : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ γ t := by
            have h1 := hlin0.eventually (hinvc.eventually (by simp))
            filter_upwards [h1] with t ht
            exact (ht.differentiableAt one_ne_zero).comp t (by fun_prop)
          have hγt : Tendsto γ (𝓝 0) (𝓝 z) := by
            have := hγd.continuousAt.tendsto
            rwa [hγ0] at this
          have hrank := hγt.eventually ((hr J).and (hr K))
          have hrt := hlin0.eventually hright
          have hall := (hdiff.and (hrank.and hrt))
          rw [Metric.eventually_nhds_iff_ball] at hall
          obtain ⟨ε, hε, hall⟩ := hall
          have hJ0 : ∀ t ∈ Metric.ball (0:ℝ) ε, ∀ j ∈ J, H j (γ t) = 0 := by
            intro t ht j hj
            have h1 : Ψ (γ t) = t • v := (hall t ht).2.2
            have h2 : inner ℝ (b j z) (Ψ (γ t)) = 0 := by
              rw [h1, inner_smul_right, hKv j (hJK hj), mul_zero]
            simp only [hΨ, inner_add_right, inner_sum, inner_smul_right, innerSL_apply_apply] at h2
            have h3 : ∑ x ∈ J.toFinset, (H x (γ t) - inner ℝ (b x z) (γ t - z)) * inner ℝ (b j z) (d x)
                = H j (γ t) - inner ℝ (b j z) (γ t - z) := by
              rw [Finset.sum_eq_single j]
              · rw [hd j hj j hj]; simp
              · intro k hk hkj
                rw [hd k (by simpa using hk) j hj, if_neg (Ne.symm hkj), mul_zero]
              · intro h; exact absurd (by simpa using hj) h
            rw [h3] at h2
            linarith
          have hzspan : Submodule.span ℝ ((fun i => b i z) '' J) =
              Submodule.span ℝ ((fun i => b i z) '' K) := by
            apply le_antisymm
            · exact Submodule.span_mono (Set.image_mono hJK)
            · exact Submodule.span_le.mpr hJspan
          refine ⟨γ, hγ0, hγd, ?_⟩
          filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with t ht i hi
          have hcomp : ∀ k, ∀ s ∈ Metric.ball (0:ℝ) ε,
              HasDerivAt (fun s => H k (γ s)) (inner ℝ (b k (γ s)) (deriv γ s)) s := by
            intro k s hs
            exact (hH k (γ s)).comp_hasDerivAt s (hall s hs).1.hasDerivAt
          have hzero : ∀ s ∈ Metric.ball (0:ℝ) ε, inner ℝ (b i (γ s)) (deriv γ s) = 0 := by
            intro s hs
            have hJs : ∀ j ∈ J, inner ℝ (b j (γ s)) (deriv γ s) = 0 := by
              intro j hj
              have h1 := hcomp j s hs
              have h2 : HasDerivAt (fun s => H j (γ s)) 0 s := by
                refine (hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq ?_
                filter_upwards [Metric.isOpen_ball.mem_nhds hs] with r hr
                exact hJ0 r hr j hj
              exact h1.unique h2
            have hspan : Submodule.span ℝ ((fun i => b i (γ s)) '' J) =
                Submodule.span ℝ ((fun i => b i (γ s)) '' K) := by
              apply Submodule.eq_of_le_of_finrank_eq
              · exact Submodule.span_mono (Set.image_mono hJK)
              · rw [(hall s hs).2.1.1, (hall s hs).2.1.2]
                rw [hzspan]
            have hmem : b i (γ s) ∈ Submodule.span ℝ ((fun i => b i (γ s)) '' J) := by
              rw [hspan]; exact Submodule.subset_span ⟨i, hi, rfl⟩
            refine Submodule.span_induction (p := fun x _ => inner ℝ x (deriv γ s) = (0:ℝ)) ?_ ?_ ?_ ?_ hmem
            · rintro x ⟨j, hj, rfl⟩; exact hJs j hj
            · simp
            · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
            · intro a x _ hx; rw [real_inner_smul_left, hx, mul_zero]
          have hconst := IsOpen.is_const_of_deriv_eq_zero (f := fun s => H i (γ s)) Metric.isOpen_ball
            (convex_ball (0:ℝ) ε).isPreconnected
            (fun s hs => (hcomp i s hs).differentiableAt.differentiableWithinAt)
            (fun s hs => by simpa [hzero s hs] using (hcomp i s hs).deriv)
            ht (Metric.mem_ball_self hε)
          simp only [hγ0] at hconst
          rw [hconst, hK0 i hi]
        have L4 : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (X : Type) [TopologicalSpace X] (b : X → ι → V) (a : X)
          (hb : ∀ i, ContinuousAt (fun q => b q i) a)
          (hr : ∀ K : Set ι, ∀ᶠ q in 𝓝 a, Module.finrank ℝ (Submodule.span ℝ (b q '' K)) =
            Module.finrank ℝ (Submodule.span ℝ (b a '' K))),
            ∃ C : ℝ, 0 < C ∧ ∀ᶠ q in 𝓝 a, ∀ T : Finset ι, LinearIndepOn ℝ (b q) (T : Set ι) →
            ∀ l : ι → ℝ, (∀ i, i ∉ T → l i = 0) → ∑ i, |l i| ≤ C * ‖∑ i, l i • b q i‖ := by
          intro V _ _ _ ι _ X _ b a hb hr
          classical
          have key : ∀ T : Finset ι, ∃ C : ℝ, 0 < C ∧ ∀ᶠ q in 𝓝 a, LinearIndepOn ℝ (b q) (T : Set ι) →
              ∀ l : ι → ℝ, (∀ i, i ∉ T → l i = 0) → ∑ i, |l i| ≤ C * ‖∑ i, l i • b q i‖ := by
            intro T
            have hcard : ∀ q, LinearIndepOn ℝ (b q) (T : Set ι) ↔
                Fintype.card T = Module.finrank ℝ (Submodule.span ℝ (b q '' (T : Set ι))) := by
              intro q
              have h1 := linearIndependent_iff_card_eq_finrank_span (R := ℝ) (b := fun i : T => b q i)
              have h2 : Set.range (fun i : T => b q i) = b q '' (T : Set ι) :=
                (Set.image_eq_range (b q) (T : Set ι)).symm
              rw [h2] at h1
              exact h1
            by_cases hT : LinearIndepOn ℝ (b a) (T : Set ι)
            · have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : T => b a i)) = ⊥ :=
                LinearMap.ker_eq_bot'.mpr fun f hf => funext fun i => by
                  rw [Fintype.linearCombination_apply] at hf
                  exact Fintype.linearIndependent_iff.mp hT f hf i
              obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith _ hinj
              set M : ℝ := (Fintype.card ι + 1) * K with hM
              have hKr : (0:ℝ) < K := by exact_mod_cast hK
              have hM0 : 0 < M := mul_pos (Nat.cast_add_one_pos _) hKr
              obtain ⟨η, hη0, hMη⟩ : ∃ η : ℝ, 0 < η ∧ M * η = 1 / 2 :=
                ⟨(1 / 2) / M, div_pos (by norm_num) hM0, mul_div_cancel₀ _ hM0.ne'⟩
              have hev : ∀ᶠ q in 𝓝 a, ∀ i, ‖b q i - b a i‖ < η := by
                rw [eventually_all]
                intro i
                have h1 : Tendsto (fun q => ‖b q i - b a i‖) (𝓝 a) (𝓝 0) := by
                  have := ((hb i).sub (continuousAt_const (y := b a i))).norm
                  simpa [ContinuousAt] using this
                exact h1.eventually (gt_mem_nhds hη0)
              refine ⟨2 * M, mul_pos two_pos hM0, ?_⟩
              filter_upwards [hev] with q hq _ l hl
              have h1 : ∀ i, |l i| ≤ K * ‖∑ i, l i • b a i‖ := by
                intro i
                by_cases hi : i ∈ T
                · have h2 := hanti.le_mul_dist (fun i : T => l i) 0
                  rw [dist_zero_right, map_zero, dist_zero_right, Fintype.linearCombination_apply,
                    Finset.sum_coe_sort T (fun i => l i • b a i),
                    Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by simp [hl i hi])] at h2
                  have h3 := norm_le_pi_norm (fun i : T => l i) ⟨i, hi⟩
                  exact le_trans h3 h2
                · rw [hl i hi, abs_zero]; exact mul_nonneg hKr.le (norm_nonneg _)
              have h2 : ∑ i, |l i| ≤ M * ‖∑ i, l i • b a i‖ := by
                calc ∑ i, |l i| ≤ ∑ i : ι, K * ‖∑ i, l i • b a i‖ := Finset.sum_le_sum fun i _ => h1 i
                  _ = Fintype.card ι * (K * ‖∑ i, l i • b a i‖) := by simp
                  _ ≤ M * ‖∑ i, l i • b a i‖ := by
                      rw [hM]
                      have : 0 ≤ (K:ℝ) * ‖∑ i, l i • b a i‖ := mul_nonneg hKr.le (norm_nonneg _)
                      rw [add_mul, add_mul, one_mul, mul_assoc]
                      linarith
              have h3 : ‖∑ i, l i • b a i‖ ≤ ‖∑ i, l i • b q i‖ + η * ∑ i, |l i| := by
                have h4 : ∑ i, l i • b a i = ∑ i, l i • b q i - ∑ i, l i • (b q i - b a i) := by
                  simp [smul_sub, Finset.sum_sub_distrib]
                rw [h4]
                refine (norm_sub_le _ _).trans ?_
                refine add_le_add_right ?_ _
                refine (norm_sum_le _ _).trans ?_
                rw [Finset.mul_sum]
                refine Finset.sum_le_sum fun i _ => ?_
                rw [norm_smul, Real.norm_eq_abs, mul_comm]
                exact mul_le_mul_of_nonneg_right (hq i).le (abs_nonneg _)
              have h5 : M * ‖∑ i, l i • b a i‖ ≤ M * ‖∑ i, l i • b q i‖ + 1 / 2 * ∑ i, |l i| := by
                calc M * ‖∑ i, l i • b a i‖ ≤ M * (‖∑ i, l i • b q i‖ + η * ∑ i, |l i|) :=
                    mul_le_mul_of_nonneg_left h3 hM0.le
                  _ = M * ‖∑ i, l i • b q i‖ + (M * η) * ∑ i, |l i| := by ring
                  _ = _ := by rw [hMη]
              linarith
            · refine ⟨1, one_pos, ?_⟩
              filter_upwards [hr (T : Set ι)] with q hq hli
              exact absurd ((hcard a).mpr (((hcard q).mp hli).trans hq)) hT
          choose C hC hCev using key
          refine ⟨∑ T, C T, Finset.sum_pos (fun T _ => hC T) ⟨∅, Finset.mem_univ _⟩, ?_⟩
          filter_upwards [eventually_all.mpr hCev] with q hq T hT l hl
          refine (hq T hT l hl).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact Finset.single_le_sum (f := C) (fun T _ => (hC T).le) (Finset.mem_univ T)
        have L3 : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (H : ι → V → ℝ) (b : ι → V → V) (w y : V)
          (hH : ∀ i z, HasFDerivAt (H i) (innerSL ℝ (b i z)) z) (hb : ∀ i, Continuous (b i))
          (hr : ∀ K' : Set ι, ∀ᶠ z in 𝓝 w,
            Module.finrank ℝ (Submodule.span ℝ ((fun i => b i z) '' K')) =
            Module.finrank ℝ (Submodule.span ℝ ((fun i => b i w) '' K')))
          (hw : ∀ i, H i w ≤ 0) (hmin : ∀ z, (∀ i, H i z ≤ 0) → ‖w - y‖ ≤ ‖z - y‖),
            ∀ v, (∀ i ∈ {i | H i w = 0}, inner ℝ (b i w) v ≤ 0) → inner ℝ (y - w) v ≤ 0 := by
          intro V _ _ _ ι _ H b w y hH hb hr hw hmin
          intro v hv
          by_contra hcon
          push Not at hcon
          have N : ∀ (f : ℝ → ℝ) (d : ℝ), d < 0 → HasDerivAt f d 0 → ∀ᶠ t in 𝓝[>] (0:ℝ), f t < f 0 := by
            intro f d hd hf
            rw [hasDerivAt_iff_tendsto_slope_zero] at hf
            have h1 := (hf.mono_left (nhdsWithin_mono 0 (fun x (hx : 0 < x) => hx.ne'))).eventually
              (gt_mem_nhds hd)
            filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
            have ht0' : (0:ℝ) < t := ht0
            rw [zero_add, smul_eq_mul] at ht
            have := (mul_neg_iff.mp ht)
            rcases this with ⟨_, h⟩ | ⟨h, _⟩
            · linarith
            · exact absurd h (not_lt.mpr (inv_pos.mpr ht0').le)
          obtain ⟨γ, hγ0, hγd, hγK⟩ := L2 V ι H b w v hH hb
            {i | H i w = 0 ∧ inner ℝ (b i w) v = 0} (fun i hi => hi.1) (fun i hi => hi.2) hr
          have hHγ : ∀ i, HasDerivAt (fun t => H i (γ t)) (inner ℝ (b i w) v) 0 := by
            intro i
            have h1 : HasFDerivAt (H i) (innerSL ℝ (b i w)) (γ 0) := by rw [hγ0]; exact hH i w
            exact h1.comp_hasDerivAt (0:ℝ) hγd
          have hfeas : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, H i (γ t) ≤ 0 := by
            rw [eventually_all]
            intro i
            rcases (hw i).lt_or_eq with h0 | h0
            · have h1 : Tendsto (fun t => H i (γ t)) (𝓝[>] 0) (𝓝 (H i w)) := by
                have := (hHγ i).continuousAt.tendsto
                rw [hγ0] at this
                exact this.mono_left nhdsWithin_le_nhds
              filter_upwards [h1.eventually (gt_mem_nhds h0)] with t ht using ht.le
            · rcases (hv i h0).lt_or_eq with h1 | h1
              · filter_upwards [N _ _ h1 (hHγ i)] with t ht
                simp only [hγ0, h0] at ht
                exact ht.le
              · filter_upwards [nhdsWithin_le_nhds hγK] with t ht
                exact (ht i ⟨h0, h1⟩).le
          have hdist : HasDerivAt (fun t => ‖γ t - y‖ ^ 2) (2 * inner ℝ (γ 0 - y) v) 0 :=
            (hγd.sub_const y).norm_sq
          have hneg : 2 * inner ℝ (γ 0 - y) v < 0 := by
            rw [hγ0, ← neg_sub, inner_neg_left]; linarith
          obtain ⟨t, ht1, ht2⟩ := (hfeas.and (N _ _ hneg hdist)).exists
          have h1 := hmin _ ht1
          simp only [hγ0] at ht2
          exact absurd ht2 (not_lt.mpr (pow_le_pow_left₀ (norm_nonneg _) h1 2))
        have L5 : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (X : Type) [MetricSpace X] (b : X → V → ι → V)
          (xb : X) (yb : V) (hb : ∀ i, Continuous (fun q : X × V => b q.1 q.2 i))
          (hr : ∀ K : Set ι, ∀ᶠ q in 𝓝 (xb, yb),
            Module.finrank ℝ (Submodule.span ℝ (b q.1 q.2 '' K)) =
            Module.finrank ℝ (Submodule.span ℝ (b xb yb '' K))),
            ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧ ∀ x, dist x xb < δ → ∀ H : ι → V → ℝ,
            (∀ i y, HasFDerivAt (H i) (innerSL ℝ (b x y i)) y) → ∀ y y0, dist y yb < δ → dist y0 yb < δ →
            (∀ i, H i y0 ≤ 0) → ∀ S : ℝ, 0 ≤ S → (∀ i, H i y ≤ S) → ∃ w, (∀ i, H i w ≤ 0) ∧ ‖w - y‖ ≤ ‖y0 - y‖ ∧
              ‖w - y‖ ≤ κ * S := by
          intro V _ _ _ ι _ X _ b xb yb hb hr
          classical
          have : ProperSpace V := FiniteDimensional.proper ℝ V
          obtain ⟨C, hC, hCev⟩ := L4 V ι (X × V) (fun q => b q.1 q.2) (xb, yb)
            (fun i => (hb i).continuousAt) hr
          obtain ⟨η, hη0, hCη⟩ : ∃ η : ℝ, 0 < η ∧ C * η = 1 / 4 :=
            ⟨(1 / 4) / C, div_pos (by norm_num) hC, mul_div_cancel₀ _ hC.ne'⟩
          have hev : ∀ᶠ q in 𝓝 (xb, yb), ∀ i, ‖b q.1 q.2 i - b xb yb i‖ < η / 2 := by
            rw [eventually_all]
            intro i
            have h1 : Tendsto (fun q : X × V => ‖b q.1 q.2 i - b xb yb i‖) (𝓝 (xb, yb)) (𝓝 0) := by
              have := (((hb i).continuousAt (x := (xb, yb))).sub
                (continuousAt_const (y := b xb yb i))).norm
              simpa [ContinuousAt] using this
            exact h1.eventually (gt_mem_nhds (half_pos hη0))
          have hall := hCev.and (hev.and (eventually_all.mpr hr))
          rw [Metric.eventually_nhds_iff] at hall
          obtain ⟨r, hr0, hall⟩ := hall
          refine ⟨2 * C, r / 4, mul_pos two_pos hC, div_pos hr0 four_pos, ?_⟩
          intro x hx H hH y y0 hy hy0 hfeas S hS0 hSi
          have hbx : ∀ i, Continuous (fun z => b x z i) := fun i =>
            (hb i).comp (Continuous.prodMk_right x)
          have hin : ∀ z, dist z yb < r → dist (x, z) (xb, yb) < r := by
            intro z hz
            rw [Prod.dist_eq]
            exact max_lt (by show dist x xb < r; linarith) hz
          have hHc : ∀ i, Continuous (H i) := fun i =>
            continuous_iff_continuousAt.mpr fun z => (hH i z).continuousAt
          -- minimiser
          have hcomp : IsCompact ({z | ∀ i, H i z ≤ 0} ∩ Metric.closedBall y ‖y0 - y‖) := by
            refine IsCompact.inter_left (isCompact_closedBall _ _) ?_
            have : {z | ∀ i, H i z ≤ 0} = ⋂ i, {z | H i z ≤ 0} := by ext; simp
            rw [this]
            exact isClosed_iInter fun i => isClosed_le (hHc i) continuous_const
          obtain ⟨w, ⟨hwf, hwb⟩, hwmin⟩ := hcomp.exists_isMinOn (f := fun z => ‖z - y‖)
            ⟨y0, hfeas, by simp [dist_eq_norm]⟩ (by fun_prop)
          have hwb' : ‖w - y‖ ≤ ‖y0 - y‖ := by simpa [dist_eq_norm] using hwb
          have hgmin : ∀ z, (∀ i, H i z ≤ 0) → ‖w - y‖ ≤ ‖z - y‖ := by
            intro z hz
            by_cases hzb : ‖z - y‖ ≤ ‖y0 - y‖
            · exact hwmin ⟨hz, by simpa [dist_eq_norm] using hzb⟩
            · exact hwb'.trans (not_le.mp hzb).le
          have hyr : dist y yb < r := by linarith
          have hwr : dist w yb < r := by
            have h1 : dist w yb ≤ dist w y + dist y yb := dist_triangle _ _ _
            have h2 : dist y0 y ≤ dist y0 yb + dist yb y := dist_triangle _ _ _
            rw [dist_comm yb y] at h2
            have h3 : dist w y ≤ dist y0 y := by rw [dist_eq_norm, dist_eq_norm]; exact hwb'
            linarith
          refine ⟨w, hwf, hwb', ?_⟩
          have hrankw : ∀ K' : Set ι, ∀ᶠ z in 𝓝 w,
              Module.finrank ℝ (Submodule.span ℝ ((fun i => b x z i) '' K')) =
              Module.finrank ℝ (Submodule.span ℝ ((fun i => b x w i) '' K')) := by
            intro K'
            have h1 : Metric.ball yb r ∈ 𝓝 w := Metric.isOpen_ball.mem_nhds hwr
            filter_upwards [h1] with z hz
            have e1 := (hall (hin z hz)).2.2 K'
            have e2 := (hall (hin w hwr)).2.2 K'
            exact e1.trans e2.symm
          obtain ⟨T, l, hl0, hlT, hTA, hTli, hn⟩ := L1 V ι {i | H i w = 0} (fun i => b x w i) (y - w)
            (L3 V ι H (fun i z => b x z i) w y hH hbx hrankw hwf hgmin)
          have hCl := (hall (hin w hwr)).1 T hTli l hlT
          simp only at hCl
          rw [← hn] at hCl
          have habs : ∑ i, |l i| = ∑ i, l i := Finset.sum_congr rfl fun i _ => abs_of_nonneg (hl0 i)
          rw [habs] at hCl
          set D := ‖y - w‖ with hD
          have hD0 : 0 ≤ D := norm_nonneg _
          have hmv : ∀ i, ‖H i y - H i w - innerSL ℝ (b x w i) (y - w)‖ ≤ η * ‖y - w‖ := by
            intro i
            refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (s := Metric.ball yb r)
              (f' := fun z => innerSL ℝ (b x z i)) (fun z _ => (hH i z).hasFDerivWithinAt) ?_
              (convex_ball _ _) hwr hyr
            intro z hz
            rw [← map_sub, innerSL_apply_norm]
            have h1 := (hall (hin z hz)).2.1 i
            have h2 := (hall (hin w hwr)).2.1 i
            simp only at h1 h2
            have h3 : b x z i - b x w i = (b x z i - b xb yb i) - (b x w i - b xb yb i) := by abel
            rw [h3]
            refine (norm_sub_le _ _).trans ?_
            linarith
          have hterm : ∀ i, l i * inner ℝ (b x w i) (y - w) ≤ l i * (S + η * D) := by
            intro i
            by_cases hi : i ∈ T
            · refine mul_le_mul_of_nonneg_left ?_ (hl0 i)
              have h1 := hmv i
              have h2 : H i w = 0 := hTA i hi
              rw [h2, innerSL_apply_apply, Real.norm_eq_abs] at h1
              have h3 := (abs_le.mp h1).1
              have h4 := hSi i
              linarith
            · simp [hlT i hi]
          have hsq : D * D ≤ (∑ i, l i) * (S + η * D) := by
            calc D * D = inner ℝ (y - w) (y - w) := (real_inner_self_eq_norm_mul_norm _).symm
              _ = inner ℝ (∑ i, l i • b x w i) (y - w) := by rw [← hn]
              _ = ∑ i, l i * inner ℝ (b x w i) (y - w) := by
                  rw [sum_inner]; simp only [real_inner_smul_left]
              _ ≤ ∑ i, l i * (S + η * D) := Finset.sum_le_sum fun i _ => hterm i
              _ = _ := by rw [Finset.sum_mul]
          have hfin : D * D ≤ (C * D) * (S + η * D) :=
            hsq.trans (mul_le_mul_of_nonneg_right hCl (add_nonneg hS0 (mul_nonneg hη0.le hD0)))
          have hfin2 : (C * D) * (S + η * D) = C * D * S + (C * η) * (D * D) := by ring
          rw [hfin2, hCη] at hfin
          rw [norm_sub_rev, ← hD]
          by_contra hcon
          rw [not_le] at hcon
          have hDpos : 0 < D := lt_of_le_of_lt (mul_nonneg (mul_nonneg two_pos.le hC.le) hS0) hcon
          have e1 := mul_lt_mul_of_pos_left hcon hDpos
          have e2 : D * (2 * C * S) = 2 * (C * D * S) := by ring
          have e3 := mul_pos hDpos hDpos
          linarith
        have D1 : ∀ (n m : ℕ) (h : Z n m → ℝ) (z : Z n m) (hz : DifferentiableAt ℝ h z) (u : E n) (v : E m),
            fderiv ℝ h z (WithLp.toLp 2 (u, v)) =
            fderiv ℝ h z (WithLp.toLp 2 (u, 0)) + inner ℝ (gradY h z) v := by
          intro n m h z hz u v
          have h1 : (WithLp.toLp 2 (u, v) : Z n m) = WithLp.toLp 2 (u, 0) + WithLp.toLp 2 (0, v) := by
            rw [← WithLp.toLp_add]; simp
          rw [h1, map_add]
          congr 1
          have h2 : fderiv ℝ h z (WithLp.toLp 2 (0, v)) = inner ℝ (gradient h z) (WithLp.toLp 2 (0, v) : Z n m) := by
            rw [gradient, InnerProductSpace.toDual_symm_apply]
          rw [h2, WithLp.prod_inner_apply]
          simp [gradY]
        have D2 : ∀ (n m : ℕ) (h : Z n m → ℝ) (hh : ContDiff ℝ 1 h) (x : E n) (y : E m),
            HasFDerivAt (fun y => h (WithLp.toLp 2 (x, y))) (innerSL ℝ (gradY h (WithLp.toLp 2 (x, y)))) y := by
          intro n m h hh x y
          let A : E m →L[ℝ] Z n m :=
            ((WithLp.prodContinuousLinearEquiv 2 ℝ (E n) (E m)).symm : (E n × E m) →L[ℝ] Z n m).comp
              (ContinuousLinearMap.inr ℝ (E n) (E m))
          have hA : HasFDerivAt (fun y : E m => (WithLp.toLp 2 (x, y) : Z n m)) A y := by
            have h1 : HasFDerivAt (fun y : E m => (WithLp.toLp 2 (x, 0) : Z n m) + A y) A y :=
              (A.hasFDerivAt).const_add _
            have he : (fun y : E m => (WithLp.toLp 2 (x, y) : Z n m)) =
                fun y : E m => (WithLp.toLp 2 (x, 0) : Z n m) + A y := by
              funext y
              show _ = (WithLp.toLp 2 (x, 0) : Z n m) + WithLp.toLp 2 (0, y)
              rw [← WithLp.toLp_add]; simp
            rw [he]
            exact h1
          have hd : DifferentiableAt ℝ h (WithLp.toLp 2 (x, y)) := hh.differentiable one_ne_zero _
          have h2 := hd.hasFDerivAt.comp y hA
          suffices he : innerSL ℝ (gradY h (WithLp.toLp 2 (x, y))) =
              (fderiv ℝ h (WithLp.toLp 2 (x, y))).comp A by
            rw [he]; exact h2
          refine ContinuousLinearMap.ext fun v => ?_
          have h3 := D1 n m h _ hd 0 v
          have h4 : (WithLp.toLp 2 ((0 : E n), (0 : E m)) : Z n m) = 0 := by
            exact WithLp.toLp_zero 2
          rw [h4, map_zero, zero_add] at h3
          exact h3.symm
        have D3 : ∀ (n m : ℕ) (h : Z n m → ℝ) (hh : ContDiff ℝ 1 h),
            Continuous (fun z => gradY h z) := by
          intro n m h hh
          have h1 : Continuous (fun z => fderiv ℝ h z) := hh.continuous_fderiv one_ne_zero
          have h2 : Continuous (fun z => gradient h z) := by
            have hc := (InnerProductSpace.toDual ℝ (Z n m)).symm.continuous
            exact hc.comp h1
          exact (continuous_snd.comp (WithLp.prod_continuous_ofLp 2 (E n) (E m))).comp h2
        have G : ∀ (n m : ℕ) (h : Z n m → ℝ) (hh : ContDiff ℝ 1 h) (z w : Z n m) (a b : ℕ → Z n m) (t : ℕ → ℝ)
          (ht : ∀ k, 0 < t k) (ha : Tendsto a atTop (𝓝 z)) (hb : Tendsto b atTop (𝓝 z))
          (hab : Tendsto (fun k => (t k)⁻¹ • (a k - b k)) atTop (𝓝 w)),
            Tendsto (fun k => (t k)⁻¹ * (h (a k) - h (b k))) atTop (𝓝 (fderiv ℝ h z w)) := by
          intro n m h hh z w a b t ht ha hb hab
          have hs : HasStrictFDerivAt h (fderiv ℝ h z) z := hh.contDiffAt.hasStrictFDerivAt one_ne_zero
          have h1 := hs.isLittleO.comp_tendsto (ha.prodMk_nhds hb)
          have h2 : (fun k => a k - b k) =O[atTop] t := by
            have h3 := hab.isBigO_one ℝ
            have h4 := (Asymptotics.isBigO_refl t atTop).smul h3
            refine (h4.congr ?_ ?_)
            · intro k; rw [smul_smul, mul_inv_cancel₀ (ht k).ne', one_smul]
            · intro k; exact mul_one _
          have h5 : (fun k => h (a k) - h (b k) - fderiv ℝ h z (a k - b k)) =o[atTop] t :=
            Asymptotics.IsLittleO.trans_isBigO h1 h2
          have h6 := h5.tendsto_inv_smul_nhds_zero
          have h7 := ((fderiv ℝ h z).continuous.tendsto w).comp hab
          have h8 := h6.add h7
          rw [zero_add] at h8
          refine h8.congr ?_
          intro k
          simp only [Function.comp, map_smul, smul_eq_mul]
          ring
        have L6 : ∀ (n m p : ℕ) (g : Z n m → E p) (hg : ContDiff ℝ 1 g) (xb : E n) (yb : E m)
          (hRCR : IsRCR g xb yb),
            ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧ ∀ x, dist x xb < δ → ∀ (lo : Fin p → ℝ) (y y0 : E m) (ε : ℝ), 0 ≤ ε →
            dist y yb < δ → dist y0 yb < δ →
            (∀ i, g (WithLp.toLp 2 (xb, yb)) i = 0 → lo i ≤ g (WithLp.toLp 2 (x, y0)) i ∧
              g (WithLp.toLp 2 (x, y0)) i ≤ 0) →
            (∀ i, g (WithLp.toLp 2 (xb, yb)) i = 0 → g (WithLp.toLp 2 (x, y)) i ≤ ε ∧
              lo i - g (WithLp.toLp 2 (x, y)) i ≤ ε) →
            ∃ w, (∀ i, g (WithLp.toLp 2 (xb, yb)) i = 0 → lo i ≤ g (WithLp.toLp 2 (x, w)) i ∧
              g (WithLp.toLp 2 (x, w)) i ≤ 0) ∧ ‖w - y‖ ≤ ‖y0 - y‖ ∧ ‖w - y‖ ≤ κ * ε := by
          intro n m p g hg xb yb hRCR
          classical
          obtain ⟨-, r, hr0, hrank⟩ := hRCR
          have hgi : ∀ i, ContDiff ℝ 1 (fun z => g z i) := fun i =>
            (EuclideanSpace.proj (𝕜 := ℝ) i : E p →L[ℝ] ℝ).contDiff.comp hg
          let ι := {i : Fin p // g (WithLp.toLp 2 (xb, yb)) i = 0} × Bool
          let σ : Bool → ℝ := fun c => if c then 1 else -1
          have hσ : ∀ c, σ c * σ c = 1 := by intro c; cases c <;> simp [σ]
          let b : E n → E m → ι → E m := fun x y k =>
            σ k.2 • gradY (fun z => g z (k.1 : Fin p)) (WithLp.toLp 2 (x, y))
          have htoLp : Continuous (fun q : E n × E m => (WithLp.toLp 2 (q.1, q.2) : Z n m)) :=
            WithLp.prod_continuous_toLp 2 (E n) (E m)
          have hb : ∀ k, Continuous (fun q : E n × E m => b q.1 q.2 k) := by
            intro k
            exact ((D3 n m _ (hgi k.1)).comp htoLp).const_smul (σ k.2)
          have hspan : ∀ (K : Set ι) x y, Submodule.span ℝ (b x y '' K) =
              Submodule.span ℝ ((fun j => gradY (fun w => g w j) (WithLp.toLp 2 (x, y))) ''
                ((fun k : ι => (k.1 : Fin p)) '' K)) := by
            intro K x y
            apply le_antisymm
            · rw [Submodule.span_le]
              rintro _ ⟨k, hk, rfl⟩
              exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.1, ⟨k, hk, rfl⟩, rfl⟩)
            · rw [Submodule.span_le]
              rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
              have h1 : b x y k ∈ Submodule.span ℝ (b x y '' K) := Submodule.subset_span ⟨k, hk, rfl⟩
              have h2 := Submodule.smul_mem _ (σ k.2) h1
              simp only [b, smul_smul, hσ, one_smul] at h2
              exact h2
          have hr : ∀ K : Set ι, ∀ᶠ q in 𝓝 (xb, yb),
              Module.finrank ℝ (Submodule.span ℝ (b q.1 q.2 '' K)) =
              Module.finrank ℝ (Submodule.span ℝ (b xb yb '' K)) := by
            intro K
            have h1 : Metric.ball (WithLp.toLp 2 (xb, yb) : Z n m) r ∈ 𝓝 (WithLp.toLp 2 (xb, yb) : Z n m) :=
              Metric.ball_mem_nhds _ hr0
            filter_upwards [(htoLp.tendsto (xb, yb)).eventually h1] with q hq
            rw [hspan, hspan]
            refine hrank _ ?_ _ hq
            rintro _ ⟨k, hk, rfl⟩
            exact k.1.2
          obtain ⟨κ, δ, hκ, hδ, hmain⟩ := L5 (E m) ι (E n) b xb yb hb hr
          refine ⟨κ, δ, hκ, hδ, ?_⟩
          intro x hx lo y y0 ε hε hy hy0 hbox hbd
          let H : ι → E m → ℝ := fun k y =>
            σ k.2 * g (WithLp.toLp 2 (x, y)) k.1 + (if k.2 then 0 else lo k.1)
          have hH : ∀ k y, HasFDerivAt (H k) (innerSL ℝ (b x y k)) y := by
            intro k y
            have h1 := ((D2 n m _ (hgi k.1) x y).const_mul (σ k.2)).add_const (if k.2 then 0 else lo k.1)
            have he : innerSL ℝ (b x y k) =
                σ k.2 • innerSL ℝ (gradY (fun z => g z (k.1 : Fin p)) (WithLp.toLp 2 (x, y))) :=
              (innerSL ℝ).map_smul _ _
            rw [he]
            exact h1
          have hle : ∀ z, (∀ i, g (WithLp.toLp 2 (xb, yb)) i = 0 → lo i ≤ g (WithLp.toLp 2 (x, z)) i ∧
                g (WithLp.toLp 2 (x, z)) i ≤ 0) ↔ ∀ k, H k z ≤ 0 := by
            intro z
            constructor
            · rintro h ⟨⟨i, hi⟩, c⟩
              obtain ⟨h1, h2⟩ := h i hi
              cases c
              · show (if false = true then (1:ℝ) else -1) * _ + (if false = true then (0:ℝ) else lo i) ≤ 0
                rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]; linarith
              · show (if true = true then (1:ℝ) else -1) * _ + (if true = true then (0:ℝ) else lo i) ≤ 0
                rw [if_pos rfl, if_pos rfl]; linarith
            · intro h i hi
              have h1 : (if true = true then (1:ℝ) else -1) * g (WithLp.toLp 2 (x, z)) i +
                (if true = true then (0:ℝ) else lo i) ≤ 0 := h (⟨i, hi⟩, true)
              have h2 : (if false = true then (1:ℝ) else -1) * g (WithLp.toLp 2 (x, z)) i +
                (if false = true then (0:ℝ) else lo i) ≤ 0 := h (⟨i, hi⟩, false)
              rw [if_pos rfl, if_pos rfl] at h1
              rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true] at h2
              constructor <;> linarith
          obtain ⟨w, hw1, hw2, hw3⟩ := hmain x hx H hH y y0 hy hy0 ((hle y0).mp hbox) ε hε (by
            rintro ⟨⟨i, hi⟩, c⟩
            obtain ⟨h1, h2⟩ := hbd i hi
            cases c
            · show (if false = true then (1:ℝ) else -1) * _ + (if false = true then (0:ℝ) else lo i) ≤ ε
              rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]; linarith
            · show (if true = true then (1:ℝ) else -1) * _ + (if true = true then (0:ℝ) else lo i) ≤ ε
              rw [if_pos rfl, if_pos rfl]; linarith)
          exact ⟨w, (hle w).mpr hw1, hw2, hw3⟩
        have M : ∀ (n m p : ℕ) (f : Z n m → ℝ) (g : Z n m → E p)
          (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : E n) (y : E m) (u : E n)
          (hISC : IsDirInnerSemicont f g x y u) (hRCR : IsRCR g x y)
          (hV : ∀ x y, y ∈ solMap f g x → valueFn f g x = ((f (WithLp.toLp 2 (x, y)) : ℝ) : EReal))
          (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0)),
            ∃ w ∈ linLL g x y u, (∀ v ∈ linLL g x y u,
              fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) ≤
              fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v))) ∧
            ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => (t (φ k))⁻¹ •
              ((valueFn f g (x + t (φ k) • u)).toReal - (valueFn f g x).toReal)) atTop
              (𝓝 (fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)))) := by
          intro n m p f g hf hg x y u hISC hRCR hV t ht ht0
          classical
          obtain ⟨hyS, hyL⟩ := hISC
          obtain ⟨ys, hys, hysS⟩ := hyL t (fun _ => u) ht ht0 tendsto_const_nhds
          obtain ⟨κ, δ, hκ, hδ, hcore⟩ := L6 n m p g hg x y hRCR
          have hgi : ∀ i, ContDiff ℝ 1 (fun z => g z i) := fun i =>
            (EuclideanSpace.proj (𝕜 := ℝ) i : E p →L[ℝ] ℝ).contDiff.comp hg
          have htoLp : Continuous (fun q : E n × E m => (WithLp.toLp 2 (q.1, q.2) : Z n m)) :=
            WithLp.prod_continuous_toLp 2 (E n) (E m)
          have htu : Tendsto (fun k => x + t k • u) atTop (𝓝 x) := by
            have := (ht0.smul_const u).const_add x
            simpa using this
          have hpair : ∀ (a : ℕ → E n) (b : ℕ → E m), Tendsto a atTop (𝓝 x) → Tendsto b atTop (𝓝 y) →
              Tendsto (fun k => (WithLp.toLp 2 (a k, b k) : Z n m)) atTop (𝓝 (WithLp.toLp 2 (x, y))) :=
            fun a b ha hb => (htoLp.tendsto (x, y)).comp (ha.prodMk_nhds hb)
          have hquot : ∀ (a : ℕ → E n) (b : ℕ → E m) (a' : ℕ → E n) (b' : ℕ → E m) (s : ℕ → ℝ) (u : E n) (v : E m),
              Tendsto (fun k => (s k)⁻¹ • (a k - a' k)) atTop (𝓝 u) →
              Tendsto (fun k => (s k)⁻¹ • (b k - b' k)) atTop (𝓝 v) →
              Tendsto (fun k => (s k)⁻¹ • ((WithLp.toLp 2 (a k, b k) : Z n m) - WithLp.toLp 2 (a' k, b' k)))
                atTop (𝓝 (WithLp.toLp 2 (u, v))) := by
            intro a b a' b' s u v h1 h2
            refine ((htoLp.tendsto (u, v)).comp (h1.prodMk_nhds h2)).congr fun k => ?_
            rw [← WithLp.toLp_sub, ← WithLp.toLp_smul]
            rfl
          have hinact : ∀ (a : ℕ → E n) (b : ℕ → E m), Tendsto a atTop (𝓝 x) → Tendsto b atTop (𝓝 y) →
              ∀ᶠ k in atTop, ∀ i, g (WithLp.toLp 2 (x, y)) i ≠ 0 → g (WithLp.toLp 2 (a k, b k)) i ≤ 0 := by
            intro a b ha hb
            rw [eventually_all]
            intro i
            by_cases hi : g (WithLp.toLp 2 (x, y)) i = 0
            · exact Eventually.of_forall fun k h => absurd hi h
            · have h1 : g (WithLp.toLp 2 (x, y)) i < 0 := lt_of_le_of_ne (hyS.1 i) hi
              have h2 : Tendsto (fun k => g (WithLp.toLp 2 (a k, b k)) i) atTop
                  (𝓝 (g (WithLp.toLp 2 (x, y)) i)) :=
                ((hgi i).continuous.tendsto _).comp (hpair a b ha hb)
              filter_upwards [h2.eventually (gt_mem_nhds h1)] with k hk _ using hk.le
          have hdu : Tendsto (fun k => (t k)⁻¹ • ((x + t k • u) - x)) atTop (𝓝 u) := by
            refine tendsto_const_nhds.congr fun k => ?_
            rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ht k).ne', one_smul]
          have hxd : ∀ᶠ k in atTop, dist (x + t k • u) x < δ := htu.eventually (Metric.ball_mem_nhds x hδ)
          have hysd : ∀ᶠ k in atTop, dist (ys k) y < δ := hys.eventually (Metric.ball_mem_nhds y hδ)
          set q : ℕ → ℝ := fun k => (t k)⁻¹ •
                ((valueFn f g (x + t k • u)).toReal - (valueFn f g x).toReal) with hq
          have hVx : (valueFn f g x).toReal = f (WithLp.toLp 2 (x, y)) := by rw [hV x y hyS]; rfl
          -- upper bound
          have hupper : ∀ v ∈ linLL g x y u, ∃ r : ℕ → ℝ, (∀ᶠ k in atTop, q k ≤ r k) ∧
              Tendsto r atTop (𝓝 (fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)))) := by
            intro v hv
            set yv : ℕ → E m := fun k => y + t k • v with hyv
            have hyvt : Tendsto yv atTop (𝓝 y) := by
              have := (ht0.smul_const v).const_add y
              simpa using this
            have hdv : Tendsto (fun k => (t k)⁻¹ • (yv k - y)) atTop (𝓝 v) := by
              refine tendsto_const_nhds.congr fun k => ?_
              rw [hyv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ht k).ne', one_smul]
            set S : ℕ → ℝ := fun k => ∑ i, if g (WithLp.toLp 2 (x, y)) i = 0 then
              max (g (WithLp.toLp 2 (x + t k • u, yv k)) i) 0 else 0 with hS
            have hS0 : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg fun i _ => by
              split_ifs
              · exact le_max_right _ _
              · exact le_rfl
            have hSi : ∀ k i, g (WithLp.toLp 2 (x, y)) i = 0 →
                g (WithLp.toLp 2 (x + t k • u, yv k)) i ≤ S k := by
              intro k i hi
              have h1 := Finset.single_le_sum (f := fun i => if g (WithLp.toLp 2 (x, y)) i = 0 then
                max (g (WithLp.toLp 2 (x + t k • u, yv k)) i) 0 else 0) (fun i _ => by
                  dsimp only; split_ifs
                  · exact le_max_right _ _
                  · exact le_rfl) (Finset.mem_univ i)
              simp only [hi, if_true] at h1
              exact (le_max_left _ _).trans h1
            have hSt : Tendsto (fun k => (t k)⁻¹ * S k) atTop (𝓝 0) := by
              simp only [hS, Finset.mul_sum]
              suffices hsum : Tendsto (fun k => ∑ i, (t k)⁻¹ * (if g (WithLp.toLp 2 (x, y)) i = 0 then
                  max (g (WithLp.toLp 2 (x + t k • u, yv k)) i) 0 else 0)) atTop
                  (𝓝 (∑ i : Fin p, (0:ℝ))) by
                rwa [Finset.sum_const_zero] at hsum
              refine tendsto_finset_sum _ fun i _ => ?_
              by_cases hi : g (WithLp.toLp 2 (x, y)) i = 0
              · simp only [hi, if_true]
                have h1 := G n m (fun z => g z i) (hgi i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v))
                  (fun k => WithLp.toLp 2 (x + t k • u, yv k)) (fun k => WithLp.toLp 2 (x, y)) t ht
                  (hpair _ _ htu hyvt) tendsto_const_nhds (hquot _ _ _ _ _ _ _ hdu hdv)
                have h2 := h1.max (tendsto_const_nhds (x := (0:ℝ)))
                rw [max_eq_right (hv i hi)] at h2
                refine h2.congr fun k => ?_
                simp only [hi, sub_zero]
                rw [mul_max_of_nonneg _ _ (inv_pos.mpr (ht k)).le, mul_zero]
              · simp [hi]
            have hex : ∀ k, ∃ w : E m, (dist (x + t k • u) x < δ ∧ dist (ys k) y < δ ∧ dist (yv k) y < δ ∧
                ys k ∈ solMap f g (x + t k • u)) → (∀ i, g (WithLp.toLp 2 (x, y)) i = 0 →
                  g (WithLp.toLp 2 (x + t k • u, w)) i ≤ 0) ∧ ‖w - yv k‖ ≤ κ * S k := by
              intro k
              by_cases hk : dist (x + t k • u) x < δ ∧ dist (ys k) y < δ ∧ dist (yv k) y < δ ∧
                ys k ∈ solMap f g (x + t k • u)
              · obtain ⟨h1, h2, h3, h4⟩ := hk
                obtain ⟨w, hw1, -, hw2⟩ := hcore (x + t k • u) h1
                  (fun i => min (g (WithLp.toLp 2 (x + t k • u, ys k)) i)
                    (g (WithLp.toLp 2 (x + t k • u, yv k)) i)) (yv k) (ys k) (S k) (hS0 k) h3 h2
                  (fun i _ => ⟨min_le_left _ _, h4.1 i⟩)
                  (fun i hi => ⟨hSi k i hi, by
                    have := min_le_right (g (WithLp.toLp 2 (x + t k • u, ys k)) i)
                      (g (WithLp.toLp 2 (x + t k • u, yv k)) i)
                    linarith [hS0 k]⟩)
                exact ⟨w, fun _ => ⟨fun i hi => (hw1 i hi).2, hw2⟩⟩
              · exact ⟨0, fun h => absurd h hk⟩
            choose w hw using hex
            have hev : ∀ᶠ k in atTop, (∀ i, g (WithLp.toLp 2 (x, y)) i = 0 →
                  g (WithLp.toLp 2 (x + t k • u, w k)) i ≤ 0) ∧ ‖w k - yv k‖ ≤ κ * S k := by
              filter_upwards [hxd, hysd, hyvt.eventually (Metric.ball_mem_nhds y hδ), hysS] with k h1 h2 h3 h4
              exact hw k ⟨h1, h2, h3, h4⟩
            have hwq : Tendsto (fun k => (t k)⁻¹ • (w k - yv k)) atTop (𝓝 0) := by
              refine squeeze_zero_norm' (a := fun k => κ * ((t k)⁻¹ * S k)) ?_ ?_
              · filter_upwards [hev] with k hk
                rw [norm_smul_of_nonneg (inv_pos.mpr (ht k)).le]
                have := mul_le_mul_of_nonneg_left hk.2 (inv_pos.mpr (ht k)).le
                linarith
              · simpa using hSt.const_mul κ
            have hwv : Tendsto (fun k => (t k)⁻¹ • (w k - y)) atTop (𝓝 v) := by
              have h1 := hwq.add hdv
              rw [zero_add] at h1
              refine h1.congr fun k => ?_
              rw [← smul_add]; congr 1; abel
            have hwt : Tendsto w atTop (𝓝 y) := by
              have h1 := (ht0.smul hwv).add_const y
              rw [zero_smul, zero_add] at h1
              refine h1.congr fun k => ?_
              rw [smul_smul, mul_inv_cancel₀ (ht k).ne', one_smul, sub_add_cancel]
            refine ⟨fun k => (t k)⁻¹ * (f (WithLp.toLp 2 (x + t k • u, w k)) - f (WithLp.toLp 2 (x, y))), ?_, ?_⟩
            · filter_upwards [hev, hinact _ _ htu hwt, hysS] with k h1 h2 h3
              have hfe : w k ∈ feasLL g (x + t k • u) := by
                intro i
                by_cases hi : g (WithLp.toLp 2 (x, y)) i = 0
                · exact h1.1 i hi
                · exact h2 i hi
              have h4 := h3.2 (w k) hfe
              simp only [hq, smul_eq_mul]
              rw [hVx, hV _ _ h3, EReal.toReal_coe]
              exact mul_le_mul_of_nonneg_left (sub_le_sub_right h4 _) (inv_pos.mpr (ht k)).le
            · exact G n m f hf (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v))
                (fun k => WithLp.toLp 2 (x + t k • u, w k)) (fun k => WithLp.toLp 2 (x, y)) t ht
                  (hpair _ _ htu hwt) tendsto_const_nhds (hquot _ _ _ _ _ _ _ hdu hwv)
          -- lower bound
          have hlower : ∃ w ∈ linLL g x y u, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ r : ℕ → ℝ,
              (∀ᶠ k in atTop, r k ≤ q (φ k)) ∧
              Tendsto r atTop (𝓝 (fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)))) := by
            set S : ℕ → ℝ := fun k => ∑ i, |g (WithLp.toLp 2 (x + t k • u, ys k)) i -
              g (WithLp.toLp 2 (x, ys k)) i| with hS
            have hS0 : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg fun i _ => abs_nonneg _
            have hSi : ∀ k i, |g (WithLp.toLp 2 (x + t k • u, ys k)) i -
                g (WithLp.toLp 2 (x, ys k)) i| ≤ S k := fun k i =>
              Finset.single_le_sum (f := fun i => |g (WithLp.toLp 2 (x + t k • u, ys k)) i -
                g (WithLp.toLp 2 (x, ys k)) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
            have hSt : ∃ c, Tendsto (fun k => (t k)⁻¹ * S k) atTop (𝓝 c) := by
              refine ⟨∑ i, |fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0))|, ?_⟩
              simp only [hS, Finset.mul_sum]
              refine tendsto_finset_sum _ fun i _ => ?_
              have h1 := G n m (fun z => g z i) (hgi i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0))
                  (fun k => WithLp.toLp 2 (x + t k • u, ys k)) (fun k => WithLp.toLp 2 (x, ys k)) t ht
                  (hpair _ _ htu hys) (hpair _ _ tendsto_const_nhds hys)
                  (hquot _ _ _ _ _ _ _ hdu (by simp))
              refine h1.abs.congr fun k => ?_
              rw [abs_mul, abs_of_pos (inv_pos.mpr (ht k))]
            obtain ⟨c, hc⟩ := hSt
            have hex : ∀ k, ∃ w : E m, (dist (x + t k • u) x < δ ∧ dist (ys k) y < δ ∧
                ys k ∈ solMap f g (x + t k • u)) → (∀ i, g (WithLp.toLp 2 (x, y)) i = 0 →
                  g (WithLp.toLp 2 (x + t k • u, ys k)) i ≤ g (WithLp.toLp 2 (x, w)) i ∧
                  g (WithLp.toLp 2 (x, w)) i ≤ 0) ∧ ‖w - ys k‖ ≤ κ * S k := by
              intro k
              by_cases hk : dist (x + t k • u) x < δ ∧ dist (ys k) y < δ ∧ ys k ∈ solMap f g (x + t k • u)
              · obtain ⟨h1, h2, h4⟩ := hk
                obtain ⟨w, hw1, -, hw2⟩ := hcore x (by rw [dist_self]; exact hδ)
                  (fun i => g (WithLp.toLp 2 (x + t k • u, ys k)) i) (ys k) y (S k) (hS0 k) h2
                  (by rw [dist_self]; exact hδ)
                  (fun i hi => ⟨by rw [hi]; exact h4.1 i, hi.le⟩)
                  (fun i hi => by
                    have h5 := abs_le.mp (hSi k i)
                    have h6 := h4.1 i
                    constructor <;> linarith [h5.1, h5.2])
                exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
              · exact ⟨0, fun h => absurd h hk⟩
            choose w hw using hex
            have hev : ∀ᶠ k in atTop, (∀ i, g (WithLp.toLp 2 (x, y)) i = 0 →
                  g (WithLp.toLp 2 (x + t k • u, ys k)) i ≤ g (WithLp.toLp 2 (x, w k)) i ∧
                  g (WithLp.toLp 2 (x, w k)) i ≤ 0) ∧ ‖w k - ys k‖ ≤ κ * S k := by
              filter_upwards [hxd, hysd, hysS] with k h1 h2 h4
              exact hw k ⟨h1, h2, h4⟩
            set d : ℕ → E m := fun k => (t k)⁻¹ • (ys k - w k) with hd
            have hdb : ∀ᶠ k in atTop, d k ∈ Metric.closedBall (0 : E m) (κ * (c + 1)) := by
              filter_upwards [hev, hc.eventually (gt_mem_nhds (lt_add_one c))] with k h1 h2
              rw [mem_closedBall_zero_iff, hd]
              simp only
              rw [norm_smul_of_nonneg (inv_pos.mpr (ht k)).le, norm_sub_rev]
              calc (t k)⁻¹ * ‖w k - ys k‖ ≤ (t k)⁻¹ * (κ * S k) :=
                    mul_le_mul_of_nonneg_left h1.2 (inv_pos.mpr (ht k)).le
                _ = κ * ((t k)⁻¹ * S k) := by ring
                _ ≤ κ * (c + 1) := by gcongr
            obtain ⟨v, -, φ, hφ, hφv⟩ := (isCompact_closedBall (0 : E m) (κ * (c + 1))).tendsto_subseq'
              hdb.frequently
            have hφt := hφ.tendsto_atTop
            have hwt : Tendsto (fun k => w (φ k)) atTop (𝓝 y) := by
              have h1 := (hys.comp hφt).sub ((ht0.comp hφt).smul hφv)
              rw [zero_smul, sub_zero] at h1
              refine h1.congr fun k => ?_
              simp only [Function.comp, hd]
              rw [smul_smul, mul_inv_cancel₀ (ht _).ne', one_smul]; abel
            have hGen : ∀ h : Z n m → ℝ, ContDiff ℝ 1 h → Tendsto (fun k => (t (φ k))⁻¹ *
                (h (WithLp.toLp 2 (x + t (φ k) • u, ys (φ k))) - h (WithLp.toLp 2 (x, w (φ k))))) atTop
                (𝓝 (fderiv ℝ h (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)))) := by
              intro h hh
              exact G n m h hh (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v))
                (fun k => WithLp.toLp 2 (x + t (φ k) • u, ys (φ k))) (fun k => WithLp.toLp 2 (x, w (φ k)))
                (fun k => t (φ k)) (fun k => ht _)
                (hpair _ _ (htu.comp hφt) (hys.comp hφt)) (hpair _ _ tendsto_const_nhds hwt)
                (hquot _ _ _ _ _ _ _ (hdu.comp hφt) hφv)
            refine ⟨v, ?_, φ, hφ, _, ?_, hGen f hf⟩
            · intro i hi
              refine le_of_tendsto (hGen _ (hgi i)) ?_
              filter_upwards [hφt.eventually hev] with k hk
              exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr (ht _)).le (sub_nonpos.mpr (hk.1 i hi).1)
            · filter_upwards [hφt.eventually hev, hφt.eventually hysS,
                hinact _ _ (tendsto_const_nhds (x := x)) hwt] with k h1 h3 h2
              have hfe : w (φ k) ∈ feasLL g x := by
                intro i
                by_cases hi : g (WithLp.toLp 2 (x, y)) i = 0
                · exact (h1.1 i hi).2
                · exact h2 i hi
              have h4 := hyS.2 _ hfe
              simp only [hq, smul_eq_mul]
              rw [hVx, hV _ _ h3, EReal.toReal_coe]
              exact mul_le_mul_of_nonneg_left (sub_le_sub_left h4 _) (inv_pos.mpr (ht _)).le
          obtain ⟨w, hwL, φ, hφ, r, hr1, hr2⟩ := hlower
          refine ⟨w, hwL, ?_, φ, hφ, ?_⟩
          · intro v hv
            obtain ⟨r', hr1', hr2'⟩ := hupper v hv
            refine le_of_tendsto_of_tendsto hr2 (hr2'.comp hφ.tendsto_atTop) ?_
            filter_upwards [hr1, hφ.tendsto_atTop.eventually hr1'] with k h1 h2 using h1.trans h2
          · obtain ⟨r', hr1', hr2'⟩ := hupper w hwL
            exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hr2 (hr2'.comp hφ.tendsto_atTop) hr1
              (hφ.tendsto_atTop.eventually hr1')
        classical
        have hgi : ∀ i, ContDiff ℝ 1 (fun z => g z i) := fun i =>
          (EuclideanSpace.proj (𝕜 := ℝ) i : E p →L[ℝ] ℝ).contDiff.comp hg
        have hV : ∀ x y, y ∈ solMap f g x → valueFn f g x = ((f (WithLp.toLp 2 (x, y)) : ℝ) : EReal) := by
          intro x y hy
          apply le_antisymm
          · exact iInf₂_le y hy.1
          · refine le_iInf₂ fun y' hy' => ?_
            exact EReal.coe_le_coe_iff.mpr (hy.2 y' hy')
        have hyS := hISC.1
        have hyL := hISC.2
        have hMain := M n m p f g hf hg x y u hISC hRCR hV
        obtain ⟨w, hwL, hwmin, -⟩ := hMain (fun k => 1 / ((k:ℝ) + 1)) (fun k => Nat.one_div_pos_of_nat)
          tendsto_one_div_add_atTop_nhds_zero_nat
        refine ⟨fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)), ⟨?_, ?_, ?_, ?_⟩, ⟨⟨w, hwL, rfl⟩, ?_⟩,
          ?_, ?_⟩
        · rw [hV x y hyS]; exact EReal.coe_ne_top _
        · rw [hV x y hyS]; exact EReal.coe_ne_bot _
        · have hne : ∀ᶠ t in 𝓝[>] (0:ℝ), (solMap f g (x + t • u)).Nonempty := by
            by_contra hcon
            rw [not_eventually] at hcon
            obtain ⟨t, ht, htn⟩ := exists_seq_forall_of_frequently
              (hcon.and_eventually (self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0)))
            obtain ⟨ys, -, hys⟩ := hyL t (fun _ => u) (fun k => (htn k).2)
              (tendsto_nhdsWithin_iff.mp ht).1 tendsto_const_nhds
            obtain ⟨k, hk⟩ := hys.exists
            exact (htn k).1 ⟨_, hk⟩
          filter_upwards [hne] with t ht
          obtain ⟨y', hy'⟩ := ht
          rw [hV _ y' hy']
          exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
        · refine tendsto_of_subseq_tendsto fun ns hns => ?_
          rw [tendsto_nhdsWithin_iff] at hns
          obtain ⟨hns0, hnspos⟩ := hns
          obtain ⟨N, hN⟩ := eventually_atTop.mp hnspos
          obtain ⟨w', hw'L, hw'min, φ, hφ, hφt⟩ := hMain (fun k => ns (k + N))
            (fun k => hN _ (by omega)) ((tendsto_add_atTop_iff_nat N).mpr hns0)
          have heq : fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w')) =
              fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) :=
            le_antisymm (hw'min w hwL) (hwmin w' hw'L)
          rw [heq] at hφt
          exact ⟨fun k => φ k + N, hφt⟩
        · rintro r ⟨v, hv, rfl⟩
          exact hwmin v hv
        · -- multiplier
          have hfd : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y)) := hf.differentiable one_ne_zero _
          have hgd : ∀ i, DifferentiableAt ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) := fun i =>
            (hgi i).differentiable one_ne_zero _
          obtain ⟨T, l, hl0, hlT, hTA, -, hn⟩ := L1 (E m) (Fin p)
            {i | g (WithLp.toLp 2 (x, y)) i = 0 ∧
              fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) = 0}
            (fun i => gradY (fun z => g z i) (WithLp.toLp 2 (x, y)))
            (-gradY f (WithLp.toLp 2 (x, y))) (by
              intro v hv
              have hadd : ∀ (h : Z n m → ℝ), DifferentiableAt ℝ h (WithLp.toLp 2 (x, y)) → ∀ s : ℝ,
                  fderiv ℝ h (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w + s • v)) =
                  fderiv ℝ h (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) +
                    s * inner ℝ (gradY h (WithLp.toLp 2 (x, y))) v := by
                intro h hh s
                rw [D1 n m h _ hh u (w + s • v), D1 n m h _ hh u w, inner_add_right, inner_smul_right]
                ring
              have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), w + s • v ∈ linLL g x y u := by
                have : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ i, g (WithLp.toLp 2 (x, y)) i = 0 →
                    fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w + s • v)) ≤ 0 := by
                  rw [eventually_all]
                  intro i
                  by_cases hi : g (WithLp.toLp 2 (x, y)) i = 0
                  · rcases (hwL i hi).lt_or_eq with h1 | h1
                    · have hc : Tendsto (fun s : ℝ =>
                          fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) +
                          s * inner ℝ (gradY (fun z => g z i) (WithLp.toLp 2 (x, y))) v) (𝓝[>] 0)
                          (𝓝 (fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)))) := by
                        have hc' : Continuous (fun s : ℝ =>
                          fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) +
                          s * inner ℝ (gradY (fun z => g z i) (WithLp.toLp 2 (x, y))) v) := by fun_prop
                        have := (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
                        simpa using this
                      filter_upwards [hc.eventually (gt_mem_nhds h1)] with s hs _
                      rw [hadd _ (hgd i)]
                      exact hs.le
                    · filter_upwards [self_mem_nhdsWithin] with s hs _
                      have hs' : (0:ℝ) < s := hs
                      rw [hadd _ (hgd i), h1, zero_add]
                      exact mul_nonpos_of_nonneg_of_nonpos hs'.le (hv i ⟨hi, h1⟩)
                  · exact Eventually.of_forall fun s h => absurd h hi
                exact this
              obtain ⟨s, hs1, hs2⟩ := (hev.and self_mem_nhdsWithin).exists
              have hs' : (0:ℝ) < s := hs2
              have h1 := hwmin _ hs1
              rw [hadd f hfd] at h1
              rw [inner_neg_left]
              by_contra hcon
              push Not at hcon
              have : s * inner ℝ (gradY f (WithLp.toLp 2 (x, y))) v < 0 :=
                mul_neg_of_pos_of_neg hs' (by linarith)
              linarith)
          refine ⟨WithLp.toLp 2 l, ⟨hl0, ?_, ?_⟩, ?_⟩
          · refine Finset.sum_eq_zero fun i _ => ?_
            by_cases hi : i ∈ T
            · rw [(hTA i hi).1, mul_zero]
            · show l i * _ = 0
              rw [hlT i hi, zero_mul]
          · show gradY f (WithLp.toLp 2 (x, y)) +
              ∑ i, l i • gradY (fun z => g z i) (WithLp.toLp 2 (x, y)) = 0
            rw [← hn]; simp
          · show _ = fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0)) +
              ∑ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0))
            have h1 : ∀ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0)) =
                - (l i * inner ℝ (gradY (fun z => g z i) (WithLp.toLp 2 (x, y))) w) := by
              intro i
              by_cases hi : i ∈ T
              · have h2 := (hTA i hi).2
                rw [D1 n m _ _ (hgd i) u w] at h2
                have h3 : fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0)) =
                  - inner ℝ (gradY (fun z => g z i) (WithLp.toLp 2 (x, y))) w := by linarith
                rw [h3]; ring
              · rw [hlT i hi]; ring
            rw [D1 n m f _ hfd u w]
            congr 1
            rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_neg_distrib]
            have h4 : inner ℝ (-gradY f (WithLp.toLp 2 (x, y))) w =
                ∑ i, l i * inner ℝ (gradY (fun z => g z i) (WithLp.toLp 2 (x, y))) w := by
              rw [hn, sum_inner]; simp only [real_inner_smul_left]
            rw [← h4, inner_neg_left, neg_neg]
        · rintro r ⟨l, ⟨hl0, hl1, hl2⟩, rfl⟩
          have hfd : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y)) := hf.differentiable one_ne_zero _
          have hgd : ∀ i, DifferentiableAt ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) := fun i =>
            (hgi i).differentiable one_ne_zero _
          have hcomp : ∀ i, l i * g (WithLp.toLp 2 (x, y)) i = 0 := by
            have h1 := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ =>
              mul_nonpos_of_nonneg_of_nonpos (hl0 i) (hyS.1 i))).mp hl1
            exact fun i => h1 i (Finset.mem_univ i)
          have hterm : ∀ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) ≤ 0 := by
            intro i
            rcases mul_eq_zero.mp (hcomp i) with h1 | h1
            · rw [h1, zero_mul]
            · exact mul_nonpos_of_nonneg_of_nonpos (hl0 i) (hwL i h1)
          have hsum : ∑ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) ≤ 0 :=
            Finset.sum_nonpos fun i _ => hterm i
          have h4 : inner ℝ (gradY f (WithLp.toLp 2 (x, y)) +
              ∑ i, l i • gradY (fun z => g z i) (WithLp.toLp 2 (x, y))) w = 0 := by
            rw [hl2, inner_zero_left]
          rw [inner_add_left, sum_inner] at h4
          simp only [real_inner_smul_left] at h4
          have h5 : ∑ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, w)) =
              ∑ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0)) +
              ∑ i, l i * inner ℝ (gradY (fun z => g z i) (WithLp.toLp 2 (x, y))) w := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [D1 n m _ _ (hgd i) u w]; ring
          rw [lagDerivX, D1 n m f _ hfd u w]
          linarith
