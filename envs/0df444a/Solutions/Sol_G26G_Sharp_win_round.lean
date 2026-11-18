-- Prove2me | solution 1 for G26G.Sharp.win_round
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:45:57.0212+00:00
-- url     : https://prove2.me/submissions/70ac18e1-1e4e-474d-9179-e6f4768a4b05

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_G26_FI_absMax_env
import Theorems.Thm_G26G_Sharp_cross_window
import Theorems.Thm_G26G_Sharp_ref_block
import Theorems.Thm_G26G_Sharp_runN_SI
import Theorems.Thm_G26G_Sharp_win_inv
import Theorems.Thm_G26G_Sharp_win_ok
import Theorems.Thm_G26R_runK_FI
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_J_4

-- ===== Solutions.G2.Haus =====

/-! ### The `k`-dimensional Hausdorff measure of a compact convex set of affine dimension `k` -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace G11

variable {d : ℕ}

theorem hausdorff_pos_fin {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) :
    0 < μH[(Module.finrank ℝ (vectorSpan ℝ K) : ℝ)] K ∧
      μH[(Module.finrank ℝ (vectorSpan ℝ K) : ℝ)] K < ∞ := by
  set V := vectorSpan ℝ K with hV
  set k := Module.finrank ℝ V with hk
  obtain ⟨b₀, hb₀⟩ := hne
  let bV := Module.finBasisOfFinrankEq ℝ V hk.symm
  let φ : (Fin k → ℝ) →ₗ[ℝ] (Fin d → ℝ) := V.subtype ∘ₗ bV.equivFun.symm.toLinearMap
  have hφinj : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro y z h
    exact bV.equivFun.symm.injective (Subtype.val_injective h)
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective hφinj
  have hψφ : ∀ y, ψ (φ y) = y := fun y => by
    simpa using LinearMap.congr_fun hψ y
  have hφsurj : ∀ v ∈ V, ∃ y, φ y = v := fun v hv =>
    ⟨bV.equivFun ⟨v, hv⟩, by simp [φ]⟩
  let L : (Fin k → ℝ) → (Fin d → ℝ) := fun y => b₀ + φ y
  let G : (Fin d → ℝ) → (Fin k → ℝ) := fun x => ψ (x - b₀)
  have hLG : ∀ x ∈ K, L (G x) = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hφsurj (x - b₀) (vsub_mem_vectorSpan ℝ hx hb₀)
    simp only [L, G, ← hy, hψφ]
    rw [hy]; abel
  have hKimg : L '' (G '' K) = K := by
    rw [Set.image_image]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; show L (G y) ∈ K; rw [hLG y hy]; exact hy
    · intro hx; exact ⟨x, hx, hLG x hx⟩
  -- Lipschitz constants
  obtain ⟨Kφ, hLφ⟩ : ∃ C, LipschitzWith C φ :=
    ⟨_, by simpa using (LinearMap.toContinuousLinearMap φ).lipschitz⟩
  obtain ⟨Kψ, hLψ⟩ : ∃ C, LipschitzWith C ψ :=
    ⟨_, by simpa using (LinearMap.toContinuousLinearMap ψ).lipschitz⟩
  have hL : LipschitzWith Kφ L := LipschitzWith.of_dist_le_mul fun y z => by
    simp only [L]; rw [dist_add_left]; exact hLφ.dist_le_mul _ _
  have hG : LipschitzWith Kψ G := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [G]; rw [← dist_sub_right x y b₀]; exact hLψ.dist_le_mul _ _
  have hvol : (μH[(k : ℝ)] : Measure (Fin k → ℝ)) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin k))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  -- the image `G '' K` is compact, convex and full-dimensional
  have hGK : IsCompact (G '' K) := hK.image hG.continuous
  have hGconv : Convex ℝ (G '' K) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • y, hconv hx hy ha hb hab, ?_⟩
    simp only [G]
    have : a • x + b • y - b₀ = a • (x - b₀) + b • (y - b₀) := by
      rw [smul_sub, smul_sub]
      nth_rewrite 1 [show b₀ = (a + b) • b₀ by rw [hab, one_smul]]
      rw [add_smul]; abel
    rw [this, map_add, map_smul, map_smul]
  have hspan : vectorSpan ℝ (G '' K) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hmem : ∀ w ∈ V, ψ w ∈ vectorSpan ℝ (G '' K) := by
      intro w hw
      rw [hV, vectorSpan_def] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.1 hw
        have : ψ (x -ᵥ y) = G x -ᵥ G y := by
          simp only [G, vsub_eq_sub]
          rw [← map_sub]; congr 1; abel
        rw [this]
        exact vsub_mem_vectorSpan ℝ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
    have := hmem (φ z) (by
      simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply]; exact Submodule.coe_mem _)
    rwa [hψφ] at this
  have hGne : (G '' K).Nonempty := ⟨G b₀, b₀, hb₀, rfl⟩
  have haff : affineSpan ℝ (G '' K) = ⊤ :=
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hGne).2 hspan
  obtain ⟨z, hz⟩ := (hGconv.interior_nonempty_iff_affineSpan_eq_top).2 haff
  have hvolpos : 0 < volume (G '' K) :=
    lt_of_lt_of_le (isOpen_interior.measure_pos volume ⟨z, hz⟩) (measure_mono interior_subset)
  constructor
  · -- positivity
    have h1 := hG.hausdorffMeasure_image_le hk0 K
    rw [hvol] at h1
    by_contra h0
    push Not at h0
    have h0' : μH[(k : ℝ)] K = 0 := nonpos_iff_eq_zero.1 h0
    rw [h0', mul_zero] at h1
    exact absurd (nonpos_iff_eq_zero.1 h1) hvolpos.ne'
  · -- finiteness
    have h1 := hL.hausdorffMeasure_image_le hk0 (G '' K)
    rw [hKimg, hvol] at h1
    refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top ?_ hGK.measure_lt_top)
    exact ENNReal.rpow_lt_top_of_nonneg hk0 ENNReal.coe_ne_top

end G11


-- ===== Solutions.T31.Geo =====

/-! ### General tools for the Theorem 3.1 leaves -/

open MeasureTheory Matrix Set

namespace T31

/-! #### Quadratic forms of positive definite matrices -/

/-! #### Convex hulls of compact sets in finite dimension -/

section Hull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- combinations of `n` points of `K` -/
def combSet (K : Set E) (n : ℕ) : Set E :=
  (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => K))

lemma combSet_succ {K : Set E} {z₀ : E} (hz₀ : z₀ ∈ K) (n : ℕ) :
    combSet K n ⊆ combSet K (n + 1) := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  refine ⟨⟨Fin.snoc w 0, Fin.snoc z z₀⟩, ⟨⟨fun i => ?_, ?_⟩, fun i _ => ?_⟩, ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hw.1 j
  · simp [Fin.sum_univ_castSucc, hw.2]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hz₀
    · simpa using hz j (mem_univ _)
  · simp [Fin.sum_univ_castSucc]

lemma combSet_mono {K : Set E} (hK : K.Nonempty) {k N : ℕ} (h : k ≤ N) :
    combSet K k ⊆ combSet K N := by
  obtain ⟨z₀, hz₀⟩ := hK
  induction N, h using Nat.le_induction with
  | base => exact le_rfl
  | succ N _ ih => exact ih.trans (combSet_succ hz₀ N)

lemma combSet_sub_hull (K : Set E) (n : ℕ) : combSet K n ⊆ convexHull ℝ K := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ K (hz i (mem_univ _)))

variable [FiniteDimensional ℝ E]

lemma hull_sub_combSet (K : Set E) :
    convexHull ℝ K ⊆ combSet K (Module.finrank ℝ E + 1) := by
  intro x hx
  obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hai.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
  have hne : K.Nonempty := convexHull_nonempty_iff.1 ⟨x, hx⟩
  refine combSet_mono hne hcard ?_
  let σ := Fintype.equivFin ι
  refine ⟨⟨w ∘ σ.symm, z ∘ σ.symm⟩, ⟨⟨fun i => (hw0 _).le, ?_⟩, fun i _ => hzK ⟨_, rfl⟩⟩, ?_⟩
  · simpa [Function.comp] using (Equiv.sum_comp σ.symm w).trans hw1
  · simp only [Function.comp]
    rw [← hsum]
    exact Equiv.sum_comp σ.symm (fun i => w i • z i)

lemma isCompact_convexHull_of {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  have : convexHull ℝ K = combSet K (Module.finrank ℝ E + 1) :=
    (hull_sub_combSet K).antisymm (combSet_sub_hull K _)
  rw [this]
  refine IsCompact.image ((isCompact_stdSimplex ℝ (Fin _)).prod (isCompact_univ_pi fun _ => hK)) ?_
  fun_prop

end Hull

/-! #### Integrals against measures supported on a compact set -/

variable {d : ℕ}

/-! #### Discrete measures -/

section Disc

variable {ι : Type*} [Fintype ι]

/-- the discrete measure `∑ r_i δ_{x_i}` -/
noncomputable def disc (r : ι → ℝ) (x : ι → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ∑ i, ENNReal.ofReal (r i) • Measure.dirac (x i)

instance disc_finite (r : ι → ℝ) (x : ι → Fin d → ℝ) : IsFiniteMeasure (disc r x) := by
  refine ⟨?_⟩
  simp only [disc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

end Disc

/-! #### The gauge of `𝒮 = Conv(𝒜 ∪ -𝒜)` dominates the sup norm -/

lemma Sset_sub_ball {𝒜 : Set (Fin d → ℝ)} (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) :
    IAFTRL.Sset 𝒜 ⊆ Metric.closedBall 0 1 := by
  refine convexHull_min ?_ (convex_closedBall 0 1)
  have h1 : ∀ a ∈ 𝒜, ‖a‖ ≤ 1 := by
    intro a ha
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have : a i * a i ≤ a ⬝ᵥ a :=
      Finset.single_le_sum (f := fun j => a j * a j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    have := hball a ha
    nlinarith [abs_mul_abs_self (a i), abs_nonneg (a i)]
  rintro x (hx | hx)
  · simpa using h1 x hx
  · have := h1 (-x) (by simpa using hx)
    simpa [norm_neg] using this

lemma Sset_nhds {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    IAFTRL.Sset 𝒜 ∈ nhds (0 : Fin d → ℝ) := by
  set S := IAFTRL.Sset 𝒜 with hSdef
  have hconv : Convex ℝ S := convex_convexHull ℝ _
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have h' : -(𝒜 ∪ -𝒜) = 𝒜 ∪ -𝒜 := by
      ext y; simp only [Set.mem_neg, Set.mem_union, neg_neg]; tauto
    have : -x ∈ -convexHull ℝ (𝒜 ∪ -𝒜) := by rw [Set.neg_mem_neg]; exact hx
    rw [← convexHull_neg, h'] at this
    exact this
  have haff : affineSpan ℝ S = ⊤ := by
    obtain ⟨a₀, ha₀⟩ := hne
    have hSne : S.Nonempty := ⟨a₀, subset_convexHull ℝ _ (Or.inl ha₀)⟩
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hSne, eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun a ha => ?_
    have hpa : a ∈ S := subset_convexHull ℝ _ (Or.inl ha)
    have hna : -a ∈ S := subset_convexHull ℝ _ (Or.inr (by simpa using ha))
    have h2 := vsub_mem_vectorSpan ℝ hpa hna
    rw [vsub_eq_sub, sub_neg_eq_add] at h2
    have := Submodule.smul_mem _ (1 / 2 : ℝ) h2
    have e : (1 / 2 : ℝ) • (a + a) = a := by
      rw [← two_smul ℝ a, smul_smul]; norm_num
    rwa [e] at this
  obtain ⟨x, hx⟩ := (hconv.interior_nonempty_iff_affineSpan_eq_top).2 haff
  have hxn : S ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  have hx' : -x ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have : (fun y : Fin d → ℝ => -y) ⁻¹' S ∈ nhds (-x) :=
      continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hxn)
    exact Filter.mem_of_superset this fun y hy => by simpa using hsymm _ hy
  have h0 : (0 : Fin d → ℝ) ∈ interior S := by
    have := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this
  exact mem_interior_iff_mem_nhds.1 h0

lemma norm_le_sNorm {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (x : Fin d → ℝ) : ‖x‖ ≤ IAFTRL.sNorm 𝒜 x := by
  have := le_gauge_of_subset_closedBall (absorbent_nhds_zero (Sset_nhds hne hspan)) zero_le_one
    (Sset_sub_ball hball) (x := x)
  simpa [IAFTRL.sNorm] using this

end T31


-- ===== Solutions.G1.Geo2 =====

/-! ### Generator geometry helpers -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G1L

variable {d : ℕ}

lemma Sset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Sset 𝒜 = Sset ℬ := by
  unfold Sset
  apply le_antisymm
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro x (hx | hx)
    · exact convexHull_mono subset_union_left (hgen.2 hx)
    · have h1 : -x ∈ convexHull ℝ ℬ := hgen.2 hx
      have h2 : x ∈ convexHull ℝ (-ℬ) := by
        rw [convexHull_neg, Set.mem_neg]; exact h1
      exact convexHull_mono subset_union_right h2
  · exact convexHull_mono (union_subset_union hgen.1 (Set.neg_subset_neg.2 hgen.1))

lemma sNorm_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) (x : Fin d → ℝ) :
    sNorm 𝒜 x = sNorm ℬ x := by
  unfold sNorm; rw [Sset_gen hgen]

lemma Kset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Kset 𝒜 = Kset ℬ :=
  ((convexHull_mono hgen.1).antisymm (convexHull_min hgen.2 (convex_convexHull ℝ ℬ))).symm

lemma exists_ne {ℬ : Set (Fin d → ℝ)} (hk : 1 ≤ kdim ℬ) (a : Fin d → ℝ) : ∃ b ∈ ℬ, b ≠ a := by
  by_contra h
  push Not at h
  have h1 : ℬ ⊆ {a} := fun b hb => h b hb
  have h2 : Kset ℬ ⊆ {a} := by
    unfold Kset; exact (convexHull_mono h1).trans (by rw [convexHull_singleton])
  have hsub : (Kset ℬ).Subsingleton := Set.subsingleton_singleton.anti h2
  have := (vectorSpan_eq_bot_iff_subsingleton ℝ).2 hsub
  unfold kdim at hk
  rw [this, finrank_bot] at hk
  omega

end G1L


-- ===== Solutions.G2.Meas =====

/-! ### Measurability of the reconstruction and of the exponential weights -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace G2M

variable {d : ℕ}

open Classical in
/-- Markov-ification of a measure -/
noncomputable def mk (ν : Measure (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  if ν univ = 1 then ν else Measure.dirac 0

lemma measurable_mk : Measurable (mk (d := d)) := by
  classical
  have hs : MeasurableSet {ν : Measure (Fin d → ℝ) | ν univ = 1} :=
    (Measure.measurable_coe MeasurableSet.univ) (measurableSet_singleton 1)
  exact Measurable.piecewise hs measurable_id measurable_const

instance mk_prob (ν : Measure (Fin d → ℝ)) : IsProbabilityMeasure (mk ν) := by
  unfold mk
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance

lemma mk_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] : mk ν = ν := by
  unfold mk; rw [if_pos measure_univ]

/-- the Markov kernel `ν ↦ mk ν` -/
noncomputable def kmk : Kernel (Measure (Fin d → ℝ)) (Fin d → ℝ) :=
  ⟨mk, measurable_mk⟩

instance : IsMarkovKernel (kmk (d := d)) := ⟨fun ν => mk_prob ν⟩

/-- measurability of `ν ↦ ∫ f d(mk ν)` -/
lemma measurable_integral_mk {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    Measurable fun ν : Measure (Fin d → ℝ) => ∫ x, f x ∂(mk ν) := by
  have := (hf.stronglyMeasurable.comp_measurable
    (measurable_snd (α := Measure (Fin d → ℝ)) (β := Fin d → ℝ))).integral_kernel_prod_right'
    (κ := kmk (d := d))
  exact this.measurable

/-- the design matrix entries of `mk ν` -/
noncomputable def cM (ν : Measure (Fin d → ℝ)) : Fin d → Fin d → ℝ :=
  fun i j => ∫ x, x i * x j ∂(mk ν)

lemma measurable_cM : Measurable (cM (d := d)) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact measurable_integral_mk (by fun_prop)

/-- entries of the inverse of a matrix given by its entries -/
noncomputable def invE (A : Fin d → Fin d → ℝ) : Fin d → Fin d → ℝ :=
  fun i j => (Matrix.of A)⁻¹ i j

lemma measurable_invE : Measurable (invE (d := d)) := by
  have hdet : Continuous fun A : Fin d → Fin d → ℝ => (Matrix.of A).det :=
    (continuous_id (X := Matrix (Fin d) (Fin d) ℝ)).matrix_det
  have hadj : Continuous fun A : Fin d → Fin d → ℝ => (Matrix.of A).adjugate :=
    (continuous_id (X := Matrix (Fin d) (Fin d) ℝ)).matrix_adjugate
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have : (fun A : Fin d → Fin d → ℝ => invE A i j) =
      fun A => ((Matrix.of A).det)⁻¹ * (Matrix.of A).adjugate i j := by
    funext A
    simp only [invE, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [this]
  have h1 : Measurable fun A : Fin d → Fin d → ℝ => (Matrix.of A).adjugate i j :=
    ((continuous_apply j).comp ((continuous_apply i).comp hadj)).measurable
  exact (hdet.measurable.inv).mul h1

/-- the reconstruction vector `v_x(ν) = M(ν)⁻¹ x` computed from `mk ν` -/
noncomputable def V (ν : Measure (Fin d → ℝ)) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ j, invE (cM ν) i j * x j

lemma measurable_V : Measurable fun z : Measure (Fin d → ℝ) × (Fin d → ℝ) => V z.1 z.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable fun z : Measure (Fin d → ℝ) × (Fin d → ℝ) => invE (cM z.1) i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_invE.comp (measurable_cM.comp measurable_fst)))
  exact h1.mul ((measurable_pi_apply j).comp measurable_snd)

lemma measurable_V_comp {α : Type*} {mα : MeasurableSpace α} {f : α → Measure (Fin d → ℝ)}
    {g : α → Fin d → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => V (f a) (g a) := by
  have h2 := (measurable_V (d := d)).comp (hf.prodMk hg)
  convert h2 using 1
  funext a
  simp only [Function.comp_apply]

lemma cM_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] :
    Matrix.of (cM ν) = IAFTRL.designMat ν := by
  ext i j; simp [cM, IAFTRL.designMat, mk_eq]

lemma V_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] (x : Fin d → ℝ) :
    V ν x = IAFTRL.gv ν x := by
  funext i
  simp only [V, IAFTRL.gv, IAFTRL.gM, invE, ← cM_eq ν, Matrix.mulVec, dotProduct]

end G2M


-- ===== Solutions.G2.Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

lemma Kset_compact {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

lemma meas_dot' {α : Type*} {mα : MeasurableSpace α} {f g : α → Fin d → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⬝ᵥ g a := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

/-! #### Runs -/

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma hist_mono {s t : ℕ} (h : s ≤ t) : R.hist s ≤ R.hist t := by
  unfold GRun.hist
  exact iSup₂_mono' fun i hi => ⟨i, lt_of_lt_of_le hi h, le_rfl⟩

lemma meas_hist_triple {s t : ℕ} (h : s < t) :
    Measurable[R.hist t] (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) := by
  refine Measurable.of_comap_le ?_
  exact le_iSup₂ (f := fun s (_ : s < t) =>
    MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance) s h

lemma meas_hist_Y {s t : ℕ} (hs : s < t) : Measurable[R.hist t] (R.Y s) := by
  refine Measurable.of_comap_le ?_
  have h1 : MeasurableSpace.comap (R.Y s) inferInstance ≤
      MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance := by
    have h2 : Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => z.2.2 := measurable_snd.snd
    rw [show R.Y s = (fun z : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => z.2.2) ∘
      (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono h2.comap_le
  exact h1.trans (le_iSup₂ (f := fun s (_ : s < t) =>
    MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance) s hs)

lemma feas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsFeasible3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) :=
  ((hR t ht).2.1.2 ω).1

lemma p_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsProbabilityMeasure (R.p t ω) :=
  (feas hR ht ω).1

lemma p_supp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    R.p t ω (Kset ℬ)ᶜ = 0 :=
  (feas hR ht ω).2.1

lemma thetaHat_eq (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {s : ℕ} (hs : s < T) (ω : Ω) :
    R.thetaHat s ω = R.Y s ω • G2M.V (R.p s ω) (R.X s ω) := by
  haveI := p_prob hR hs ω
  rw [GRun.thetaHat, G2M.V_eq]

lemma meas_thetaHat (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {s t : ℕ} (hs : s < t) (ht : t ≤ T) :
    Measurable[R.hist t] (R.thetaHat s) := by
  have hp0 : Measurable[R.hist s] (R.p s) := (hR s (by omega)).2.1.1
  have hp : Measurable[R.hist t] (R.p s) := hp0.mono (hist_mono hs.le) le_rfl
  have htr := meas_hist_triple (R := R) hs
  have hX : Measurable[R.hist t] (R.X s) := measurable_fst.comp htr
  have hY : Measurable[R.hist t] (R.Y s) := meas_hist_Y hs
  have hV : Measurable[R.hist t] fun ω => G2M.V (R.p s ω) (R.X s ω) :=
    G2M.measurable_V_comp hp hX
  have hm : Measurable[R.hist t] fun ω => R.Y s ω • G2M.V (R.p s ω) (R.X s ω) := hY.smul hV
  have : R.thetaHat s = fun ω => R.Y s ω • G2M.V (R.p s ω) (R.X s ω) :=
    funext (thetaHat_eq hR (by omega))
  rw [this]
  exact hm

lemma meas_cumEst (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t ≤ T) :
    Measurable[R.hist t] (R.cumEst t) := by
  unfold GRun.cumEst
  exact Finset.measurable_sum _ fun s hs => meas_thetaHat hR (Finset.mem_range.1 hs) ht

lemma G_le (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) : R.G t ≤ mΩ :=
  (hR t ht).1.2.2.2.2.1

lemma hist_le_G (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) : R.hist t ≤ R.G t :=
  (hR t ht).1.2.2.2.2.2.1

end Run

/-! #### Deterministic range bounds -/

lemma gbeta_pos (hd : 1 ≤ d) (t : ℕ) : 0 < gbeta d t := by
  unfold gbeta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

lemma gB_pos : 0 < gB d := by unfold gB; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

end Bounds

end G2R


-- ===== Solutions.G26.J11 =====

/-! ### Lemma J.11: uniform estimates for affine functions on a convex body -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace J11

variable {d : ℕ}

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

lemma haus_pos_fin : 0 < μH[(rdim D : ℝ)] D ∧ μH[(rdim D : ℝ)] D < ∞ :=
  G11.hausdorff_pos_fin hD hconv hne

lemma nvol_prob : IsProbabilityMeasure (nvol D) := by
  obtain ⟨h1, h2⟩ := haus_pos_fin hD hconv hne
  exact cond_isProbabilityMeasure_of_finite h1.ne' h2.ne

omit hconv hne in
lemma nvol_supp : nvol D Dᶜ = 0 := by
  unfold nvol
  rw [cond_apply hD.isClosed.measurableSet, Set.inter_compl_self, measure_empty, mul_zero]

/-- a homothetic copy of `D` with ratio `λ ∈ (0, 1]` has normalized volume `λ^r` -/
lemma nvol_hom {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    AffineMap.homothety x0 r '' D ⊆ D ∧
    nvol D (AffineMap.homothety x0 r '' D) = ENNReal.ofReal (r ^ rdim D) := by
  obtain ⟨hHpos, hHfin⟩ := haus_pos_fin hD hconv hne
  have hhom : ∀ x, AffineMap.homothety x0 r x = r • (x - x0) + x0 := fun x => by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  have hsub : AffineMap.homothety x0 r '' D ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hhom]
    have := hconv hx0 hx (by linarith : (0 : ℝ) ≤ 1 - r) hr0.le (by ring)
    convert this using 1
    rw [smul_sub, sub_smul, one_smul]; abel
  refine ⟨hsub, ?_⟩
  set c : ℝ≥0∞ := ((‖r‖₊ ^ (rdim D : ℝ) : ℝ≥0) : ℝ≥0∞) with hc
  have hlam : nvol D (AffineMap.homothety x0 r '' D) = c := by
    unfold nvol
    rw [cond_apply hD.isClosed.measurableSet, Set.inter_eq_right.2 hsub,
      hausdorffMeasure_homothety_image (Nat.cast_nonneg _) x0 hr0.ne', ENNReal.smul_def,
      smul_eq_mul, ← mul_assoc, mul_comm _ (c : ℝ≥0∞), mul_assoc,
      ENNReal.inv_mul_cancel hHpos.ne' hHfin.ne, mul_one]
  rw [hlam, hc, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_rpow, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hr0, Real.rpow_natCast]

/-- **The contraction lower bound**: if `g ≥ c ≥ 0` on the `λ`-contraction of `D` toward
`x0`, then `∫ g dσ ≥ λ^r c` -/
lemma contr_lb {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g (nvol D)) (hg0 : ∀ x ∈ D, 0 ≤ g x) {c : ℝ}
    (hc : 0 ≤ c) (hgc : ∀ x ∈ D, c ≤ g (AffineMap.homothety x0 r x)) :
    r ^ rdim D * c ≤ ∫ x, g x ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  obtain ⟨hsub, hvol⟩ := nvol_hom hD hconv hne hx0 hr0 hr1
  set H := AffineMap.homothety x0 r '' D with hH
  have hHm : MeasurableSet H :=
    (hD.image (AffineMap.homothety x0 r).continuous_of_finiteDimensional).isClosed.measurableSet
  have hsupp := nvol_supp hD
  have h1 : ∫ x, H.indicator (fun _ => c) x ∂(nvol D) ≤ ∫ x, g x ∂(nvol D) := by
    refine integral_mono_ae ((integrable_const c).indicator hHm) hg ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    by_cases hxH : x ∈ H
    · rw [indicator_of_mem hxH]
      obtain ⟨y, hy, rfl⟩ := hxH
      exact hgc y hy
    · rw [indicator_of_notMem hxH]; exact hg0 x hx
  rw [integral_indicator hHm, setIntegral_const, smul_eq_mul, measureReal_def, hvol,
    ENNReal.toReal_ofReal (pow_nonneg hr0.le _)] at h1
  exact h1

end

/-- affine functions along a homothety -/
lemma aff_hom' (v : Fin d → ℝ) (c : ℝ) (x0 x : Fin d → ℝ) (r : ℝ) :
    AffineMap.homothety x0 r x ⬝ᵥ v + c = (1 - r) * (x0 ⬝ᵥ v + c) + r * (x ⬝ᵥ v + c) := by
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  simp only [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]; ring

section Ineq

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

lemma cont_aff (v : Fin d → ℝ) (c : ℝ) : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v + c := by
  simp only [dotProduct]; fun_prop

/-- **Inverse contraction**: for `f > 0` on `D` with `f(x0) = m` and `f ≤ R`, every
`λ ∈ (0, 1]` gives `λ^r ((1−λ)m + λR)^{−p} ≤ ∫ f^{−p} dσ` -/
theorem inv_contr (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D)
    (hpos : ∀ x ∈ D, 0 < x ⬝ᵥ v + c) {R : ℝ} (hR : ∀ x ∈ D, x ⬝ᵥ v + c ≤ R)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (p : ℕ) :
    l ^ rdim D * (((1 - l) * (x0 ⬝ᵥ v + c) + l * R) ^ p)⁻¹ ≤
      ∫ x, ((x ⬝ᵥ v + c) ^ p)⁻¹ ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  have hfc := cont_aff hD hconv hne v c
  obtain ⟨xm, hxm, hmin⟩ := hD.exists_isMinOn hne hfc.continuousOn
  have hm0 : 0 < xm ⬝ᵥ v + c := hpos xm hxm
  have hint : Integrable (fun x => ((x ⬝ᵥ v + c) ^ p)⁻¹) (nvol D) := by
    refine Integrable.of_bound ((hfc.measurable.pow_const p).inv).aestronglyMeasurable
      (((xm ⬝ᵥ v + c) ^ p)⁻¹) ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    have h1 : xm ⬝ᵥ v + c ≤ x ⬝ᵥ v + c := hmin hx
    rw [Real.norm_eq_abs, abs_of_pos (by have := hpos x hx; positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hm0.le h1 p)
  have hR0 : 0 < R := lt_of_lt_of_le (hpos x0 hx0) (hR x0 hx0)
  refine contr_lb hD hconv hne hx0 hl0 hl1 hint (fun x hx => by
      have := hpos x hx; positivity) (by
        have := hpos x0 hx0; positivity) (fun x hx => ?_)
  have hHx : AffineMap.homothety x0 l x ∈ D := (nvol_hom hD hconv hne hx0 hl0 hl1).1 ⟨x, hx, rfl⟩
  have hp := hpos _ hHx
  refine inv_anti₀ (pow_pos hp p) (pow_le_pow_left₀ hp.le ?_ p)
  rw [aff_hom']
  have := hR x hx
  nlinarith

end Ineq

end J11


-- ===== Solutions.G26.Supp =====

/-! ### Support functions and extrema of affine fields on a compact body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ}

/-- the `ℓ¹` radius of `D` -/
noncomputable def rad1 (D : Set (Fin d → ℝ)) : ℝ := sSup ((fun u : Fin d → ℝ => ∑ i, |u i|) '' D)

lemma abs_dot_le (u v : Fin d → ℝ) : |u ⬝ᵥ v| ≤ (∑ i, |u i|) * ‖v‖ := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D)
include hD

lemma bdd_img (w : Fin d → ℝ) : BddAbove ((fun u => u ⬝ᵥ w) '' D) :=
  (hD.image (by simp only [dotProduct]; fun_prop)).bddAbove

lemma le_supp {u : Fin d → ℝ} (hu : u ∈ D) (w : Fin d → ℝ) : u ⬝ᵥ w ≤ supp D w :=
  le_csSup (bdd_img hD w) ⟨u, hu, rfl⟩

lemma supp_mem (hne : D.Nonempty) (w : Fin d → ℝ) : ∃ u ∈ D, u ⬝ᵥ w = supp D w := by
  have hc : IsCompact ((fun u => u ⬝ᵥ w) '' D) :=
    hD.image (by simp only [dotProduct]; fun_prop)
  obtain ⟨u, hu, he⟩ := hc.sSup_mem (hne.image _)
  exact ⟨u, hu, he⟩

lemma le_rad1 {u : Fin d → ℝ} (hu : u ∈ D) : ∑ i, |u i| ≤ rad1 D :=
  le_csSup (hD.image (by fun_prop)).bddAbove ⟨u, hu, rfl⟩

lemma supp_sub_le (hne : D.Nonempty) (w w' : Fin d → ℝ) :
    supp D w - supp D w' ≤ rad1 D * ‖w - w'‖ := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne w
  have h1 := le_supp hD hu w'
  have h2 := abs_dot_le u (w - w')
  have h3 : (∑ i, |u i|) * ‖w - w'‖ ≤ rad1 D * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right (le_rad1 hD hu) (norm_nonneg _)
  rw [dotProduct_sub] at h2
  have := (abs_le.1 h2).2
  linarith

lemma rad1_nonneg (hne : D.Nonempty) : 0 ≤ rad1 D := by
  obtain ⟨u, hu⟩ := hne
  exact le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) (le_rad1 hD hu)

lemma supp_lip (hne : D.Nonempty) : LipschitzWith (Real.toNNReal (rad1 D)) (supp D) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (rad1_nonneg hD hne)]
  refine abs_le.2 ⟨?_, supp_sub_le hD hne w w'⟩
  have := supp_sub_le hD hne w' w
  rw [norm_sub_rev] at this
  linarith

lemma supp_cont (hne : D.Nonempty) : Continuous (supp D) := (supp_lip hD hne).continuous

lemma negMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    -(u ⬝ᵥ V + c) ≤ negMax D V c := by
  have := le_supp hD hu (-V)
  rw [dotProduct_neg] at this
  unfold negMax; linarith

lemma posMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    u ⬝ᵥ V + c ≤ posMax D V c := by
  have := le_supp hD hu V
  unfold posMax; linarith

lemma abs_le_absMax {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    |u ⬝ᵥ V + c| ≤ absMax D V c := by
  unfold absMax
  refine abs_le.2 ⟨?_, le_trans (posMax_ge hD hu V c) (le_max_left _ _)⟩
  have := le_trans (negMax_ge hD hu V c) (le_max_right (posMax D V c) _)
  linarith

omit hD in
lemma negMax_le_absMax (V : Fin d → ℝ) (c : ℝ) : negMax D V c ≤ absMax D V c :=
  le_max_right _ _

lemma negMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, -(u ⬝ᵥ V + c) = negMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne (-V)
  refine ⟨u, hu, ?_⟩
  rw [dotProduct_neg] at he
  unfold negMax; linarith

lemma posMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, u ⬝ᵥ V + c = posMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne V
  exact ⟨u, hu, by unfold posMax; linarith⟩

/-- the absolute maximum is attained -/
lemma absMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, |u ⬝ᵥ V + c| = absMax D V c ∧ ∀ x ∈ D, |x ⬝ᵥ V + c| ≤ |u ⬝ᵥ V + c| := by
  obtain ⟨u1, hu1, h1⟩ := posMax_mem hD hne V c
  obtain ⟨u2, hu2, h2⟩ := negMax_mem hD hne V c
  rcases le_total (negMax D V c) (posMax D V c) with h | h
  · have hA : absMax D V c = posMax D V c := max_eq_left h
    have hval : |u1 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, h1]
      refine abs_of_nonneg ?_
      have := negMax_ge hD hu1 V c
      linarith
    exact ⟨u1, hu1, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩
  · have hA : absMax D V c = negMax D V c := max_eq_right h
    have hval : |u2 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, ← h2, abs_of_nonpos]
      have := posMax_ge hD hu2 V c
      linarith
    exact ⟨u2, hu2, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩

lemma negMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => negMax D p.1 p.2 := by
  unfold negMax
  exact ((supp_cont hD hne).comp continuous_fst.neg).sub continuous_snd

lemma posMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => posMax D p.1 p.2 := by
  unfold posMax
  exact ((supp_cont hD hne).comp continuous_fst).add continuous_snd

lemma absMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => absMax D p.1 p.2 :=
  (posMax_cont hD hne).max (negMax_cont hD hne)

lemma negMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => negMax D (V ω) (c ω) := by
  have h := (negMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

lemma absMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => absMax D (V ω) (c ω) := by
  have h := (absMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

end

end G26


-- ===== Solutions.G26.Iface =====

/-! ### The abstract affine-field interface of Lemma G.25 -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- the field at a fixed point is `F_n`-measurable -/
lemma FI.fz_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (u : Fin d → ℝ) :
    Measurable[F n] (fun ω => fz V c n ω u) := by
  unfold fz
  have h : Continuous fun p : (Fin d → ℝ) × ℝ => u ⬝ᵥ p.1 + p.2 := by
    simp only [dotProduct]; fun_prop
  exact h.measurable.comp ((I.Vm n hn).prodMk (I.cm n hn))

lemma FI.absMax_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable[F n] (fun ω => absMax D (V n ω) (c n ω)) :=
  G26.absMax_meas I.hD I.hne (I.Vm n hn) (I.cm n hn)

/-- deterministic envelope of the field and its extrema -/
lemma FI.env' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ᵐ ω ∂μ, absMax D (V n ω) (c n ω) ≤ r ∧
      ∀ u ∈ D, |fz V c n ω u| ≤ r := by
  obtain ⟨r, hr⟩ := I.env n hn
  refine ⟨max r 0, le_max_right _ _, ?_⟩
  filter_upwards [hr] with ω h
  obtain ⟨x0, hx0, hval, -⟩ := absMax_mem I.hD I.hne (V n ω) (c n ω)
  have hA : absMax D (V n ω) (c n ω) ≤ max r 0 := by
    rw [← hval]; exact (h x0 hx0).trans (le_max_left _ _)
  exact ⟨hA, fun u hu => (abs_le_absMax I.hD hu _ _).trans hA⟩

end

end G26


-- ===== Solutions.G26.Contr =====

/-! ### Contraction probability: a small minimum of a positive affine field is unlikely -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {D : Set (Fin d → ℝ)}

/-- deterministic contraction: `1 ≤ (2a)^p (b/a)^r ∫ f^{-p}` -/
lemma contr_one (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty) (v : Fin d → ℝ)
    (c : ℝ) (hpos : ∀ x ∈ D, 0 < x ⬝ᵥ v + c) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmin : ∃ x0 ∈ D, x0 ⬝ᵥ v + c ≤ a) (hmax : ∀ x ∈ D, x ⬝ᵥ v + c ≤ b) (p : ℕ) :
    1 ≤ (2 * a) ^ p * (b / a) ^ rdim D * ∫ x, ((x ⬝ᵥ v + c) ^ p)⁻¹ ∂(nvol D) := by
  obtain ⟨x0, hx0, hx0a⟩ := hmin
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hl0 : 0 < a / b := div_pos ha hb
  have hl1 : a / b ≤ 1 := (div_le_one hb).2 hab
  have h := inv_contr hD hconv hne v c hx0 hpos hmax hl0 hl1 p
  have hf0 := hpos x0 hx0
  have hlb : a / b * b = a := div_mul_cancel₀ a hb.ne'
  have hle : (1 - a / b) * (x0 ⬝ᵥ v + c) + a / b * b ≤ 2 * a := by
    have : (1 - a / b) * (x0 ⬝ᵥ v + c) ≤ (1 - a / b) * a :=
      mul_le_mul_of_nonneg_left hx0a (by linarith)
    nlinarith
  have hpos' : 0 < (1 - a / b) * (x0 ⬝ᵥ v + c) + a / b * b := by
    have : 0 ≤ (1 - a / b) * (x0 ⬝ᵥ v + c) := mul_nonneg (by linarith) hf0.le
    linarith
  have h2 : ((2 * a) ^ p)⁻¹ ≤ (((1 - a / b) * (x0 ⬝ᵥ v + c) + a / b * b) ^ p)⁻¹ :=
    inv_anti₀ (pow_pos hpos' p) (pow_le_pow_left₀ hpos'.le hle p)
  have h3 : (a / b) ^ rdim D * ((2 * a) ^ p)⁻¹ ≤ ∫ x, ((x ⬝ᵥ v + c) ^ p)⁻¹ ∂(nvol D) :=
    le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h
  have e1 : (2 * a) ^ p * (b / a) ^ rdim D * ((a / b) ^ rdim D * ((2 * a) ^ p)⁻¹) = 1 := by
    have : (b / a) * (a / b) = 1 := by field_simp
    rw [show (2 * a) ^ p * (b / a) ^ rdim D * ((a / b) ^ rdim D * ((2 * a) ^ p)⁻¹) =
      ((b / a) * (a / b)) ^ rdim D * ((2 * a) ^ p * ((2 * a) ^ p)⁻¹) by ring, this, one_pow,
      mul_inv_cancel₀ (by positivity), one_mul]
  calc (1 : ℝ) = (2 * a) ^ p * (b / a) ^ rdim D * ((a / b) ^ rdim D * ((2 * a) ^ p)⁻¹) := e1.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma ofReal_int_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ} (h0 : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  by_cases hf : Integrable f ν
  · rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall h0)]
  · rw [integral_undef hf]; simp

/-- **contraction probability, split form**: on `E`, a positive random affine field with a value
`≤ a` and maximum `≤ b` satisfies `P(E) ≤ P(b > ρ) + (2a)^p (ρ/a)^r K` where `K` bounds the
killed inverse moments `E[1_E |f(x)|^{-p}]` -/
theorem contr_split [IsProbabilityMeasure μ] (hD : IsCompact D) (hconv : Convex ℝ D)
    (hne : D.Nonempty) {V : Ω → Fin d → ℝ} {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c)
    {E : Set Ω} (hE : MeasurableSet E) {a : ℝ} (ha : 0 < a) {b : Ω → ℝ} (hbm : Measurable b)
    (p : ℕ) (hpos : ∀ ω ∈ E, ∀ x ∈ D, 0 < x ⬝ᵥ V ω + c ω)
    (hmin : ∀ ω ∈ E, ∃ x0 ∈ D, x0 ⬝ᵥ V ω + c ω ≤ a)
    (hmax : ∀ ω ∈ E, ∀ x ∈ D, x ⬝ᵥ V ω + c ω ≤ b ω) {ρ : ℝ} (haρ : a ≤ ρ) {K : ℝ} (hK : 0 ≤ K)
    (hinv : ∀ x ∈ D, ∫⁻ ω, E.indicator
      (fun ω => ENNReal.ofReal ((|x ⬝ᵥ V ω + c ω| ^ p)⁻¹)) ω ∂μ ≤ ENNReal.ofReal K) :
    μ.real E ≤ μ.real {ω | ρ < b ω} + (2 * a) ^ p * (ρ / a) ^ rdim D * K := by
  haveI := nvol_prob hD hconv hne
  set r := rdim D with hr
  set σ := nvol D with hσ
  set G : Ω × (Fin d → ℝ) → ℝ := fun z => (|z.2 ⬝ᵥ V z.1 + c z.1| ^ p)⁻¹ with hG
  have hGm : Measurable G := by
    have h1 : Measurable fun z : Ω × (Fin d → ℝ) => z.2 ⬝ᵥ V z.1 + c z.1 := by
      have hd : Measurable fun z : Ω × (Fin d → ℝ) => z.2 ⬝ᵥ V z.1 :=
        Continuous.measurable (f := fun q : (Fin d → ℝ) × (Fin d → ℝ) => q.1 ⬝ᵥ q.2)
          (by fun_prop) |>.comp (measurable_snd.prodMk (hV.comp measurable_fst))
      exact hd.add (hc.comp measurable_fst)
    exact (h1.abs.pow_const _).inv
  have hG0 : ∀ z, 0 ≤ G z := fun z => inv_nonneg.2 (pow_nonneg (abs_nonneg _) _)
  set E' := E ∩ {ω | b ω ≤ ρ} with hE'
  set cst := (2 * a) ^ p * (ρ / a) ^ r with hcst
  have hcst0 : 0 ≤ cst := by
    have : 0 ≤ ρ / a := div_nonneg (ha.le.trans haρ) ha.le
    positivity
  -- on `E'` the contraction bound holds with `ρ`
  have hpt : ∀ ω ∈ E', (1 : ℝ) ≤ cst * ∫ x, G (ω, x) ∂σ := by
    intro ω ⟨hω, hb⟩
    have h1 := contr_one hD hconv hne (V ω) (c ω) (hpos ω hω) ha haρ (hmin ω hω)
      (fun x hx => (hmax ω hω x hx).trans hb) p
    have e : ∫ x, ((x ⬝ᵥ V ω + c ω) ^ p)⁻¹ ∂σ = ∫ x, G (ω, x) ∂σ := by
      refine integral_congr_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
      simp only [Set.mem_compl_iff, not_not] at hx
      simp only [hG, abs_of_pos (hpos ω hω x hx)]
    rw [e] at h1
    exact h1
  -- Tonelli on `E`
  have hlin : ∫⁻ ω, E.indicator (fun ω => ∫⁻ x, ENNReal.ofReal (G (ω, x)) ∂σ) ω ∂μ ≤
      ENNReal.ofReal K := by
    calc ∫⁻ ω, E.indicator (fun ω => ∫⁻ x, ENNReal.ofReal (G (ω, x)) ∂σ) ω ∂μ
        = ∫⁻ ω, ∫⁻ x, E.indicator (fun ω => ENNReal.ofReal (G (ω, x))) ω ∂σ ∂μ := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ E
          · simp [Set.indicator_of_mem hω]
          · simp [Set.indicator_of_notMem hω]
      _ = ∫⁻ x, ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal (G (ω, x))) ω ∂μ ∂σ := by
          refine lintegral_lintegral_swap ?_
          have : Measurable fun z : Ω × (Fin d → ℝ) =>
              E.indicator (fun ω => ENNReal.ofReal (G (ω, z.2))) z.1 := by
            have h2 : Measurable fun z : Ω × (Fin d → ℝ) => ENNReal.ofReal (G z) :=
              ENNReal.measurable_ofReal.comp hGm
            have h3 : MeasurableSet {z : Ω × (Fin d → ℝ) | z.1 ∈ E} := measurable_fst hE
            convert h2.indicator h3 using 1
            ext z
            by_cases hz : z.1 ∈ E
            · simp [Set.indicator, hz]
            · simp [Set.indicator, hz]
          exact this.aemeasurable
      _ ≤ ∫⁻ _x, ENNReal.ofReal K ∂σ := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
          simp only [Set.mem_compl_iff, not_not] at hx
          exact hinv x hx
      _ = ENNReal.ofReal K := by simp
  -- the measure of `E'`
  have hE'le : μ E' ≤ ENNReal.ofReal (cst * K) := by
    have h1 : ∀ ω, E'.indicator (fun _ => (1 : ENNReal)) ω ≤
        ENNReal.ofReal cst * E.indicator (fun ω => ∫⁻ x, ENNReal.ofReal (G (ω, x)) ∂σ) ω := by
      intro ω
      by_cases hω : ω ∈ E'
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω.1]
        have h2 := hpt ω hω
        calc (1 : ENNReal) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal (cst * ∫ x, G (ω, x) ∂σ) := ENNReal.ofReal_le_ofReal h2
          _ = ENNReal.ofReal cst * ENNReal.ofReal (∫ x, G (ω, x) ∂σ) := ENNReal.ofReal_mul hcst0
          _ ≤ ENNReal.ofReal cst * ∫⁻ x, ENNReal.ofReal (G (ω, x)) ∂σ :=
              mul_le_mul_of_nonneg_left (ofReal_int_le fun x => hG0 _) (by positivity)
      · rw [Set.indicator_of_notMem hω]; positivity
    calc μ E' = ∫⁻ ω, E'.indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
          rw [lintegral_indicator (hE.inter (measurableSet_le hbm measurable_const))]; simp [hE']
      _ ≤ ∫⁻ ω, ENNReal.ofReal cst *
            E.indicator (fun ω => ∫⁻ x, ENNReal.ofReal (G (ω, x)) ∂σ) ω ∂μ := lintegral_mono h1
      _ = ENNReal.ofReal cst * ∫⁻ ω, E.indicator
            (fun ω => ∫⁻ x, ENNReal.ofReal (G (ω, x)) ∂σ) ω ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal cst * ENNReal.ofReal K := mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = ENNReal.ofReal (cst * K) := (ENNReal.ofReal_mul hcst0).symm
  have hE'r : μ.real E' ≤ cst * K :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hcst0 hK) hE'le
  have hsub : E ⊆ {ω | ρ < b ω} ∪ E' := by
    intro ω hω
    by_cases hb : ρ < b ω
    · exact Or.inl hb
    · exact Or.inr ⟨hω, not_lt.1 hb⟩
  calc μ.real E ≤ μ.real ({ω | ρ < b ω} ∪ E') := measureReal_mono hsub
    _ ≤ μ.real {ω | ρ < b ω} + μ.real E' := measureReal_union_le _ _
    _ ≤ _ := by linarith

end G26


-- ===== Solutions.G26.Freeze =====

/-! ### Freezing an affine field at a predictable stopping rule -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma survS_anti (A : ℕ → Set Ω) {m n : ℕ} (h : m ≤ n) : survS A n ⊆ survS A m := by
  intro ω hω
  simp only [survS, Set.mem_iInter, Finset.mem_range] at hω ⊢
  exact fun i hi => hω i (by omega)

/-- on the surviving set the frozen field is the field -/
lemma frz_eq {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) :
    ∀ n ω, (n = 0 ∨ ω ∈ survS A (n - 1)) → frz X A n ω = X n ω := by
  intro n ω h
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Nat.add_sub_cancel] at h
    rcases h with h | h
    · omega
    · simp only [frz, if_pos h]

lemma frz_eq_of_mem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∈ survS A n) : frz X A n ω = X n ω := by
  cases n with
  | zero => rfl
  | succ n => exact frz_eq X A (n + 1) ω (Or.inr (survS_anti A (by omega) h))

lemma frz_succ_of_notMem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∉ survS A n) : frz X A (n + 1) ω = frz X A n ω := by
  simp only [frz, if_neg h]

/-- once frozen at the first failure `i`, the field stays at its value at `i` -/
lemma frz_stop {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {i : ℕ} {ω : Ω}
    (hi : i = 0 ∨ ω ∈ survS A (i - 1)) (hfail : ω ∉ A i) :
    ∀ N, i ≤ N → frz X A N ω = X i ω := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact frz_eq X A i ω hi
  | succ N hiN ih =>
    have hnot : ω ∉ survS A N := by
      intro h
      have := survS_anti A hiN h
      simp only [survS, Set.mem_iInter, Finset.mem_range] at this
      exact hfail (this i (by omega))
    rw [frz_succ_of_notMem X A hnot, ih]

/-- the frozen pair `(V, c)` at time `n` equals the pair at a common earlier time -/
lemma frz_pair_exists (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) :
    ∀ n ω, ∃ i ≤ n, frz V A n ω = V i ω ∧ frz c A n ω = c i ω := by
  intro n ω
  induction n with
  | zero => exact ⟨0, le_rfl, rfl, rfl⟩
  | succ n ih =>
    by_cases h : ω ∈ survS A n
    · exact ⟨n + 1, le_rfl, by simp only [frz, if_pos h], by simp only [frz, if_pos h]⟩
    · obtain ⟨i, hi, he, he'⟩ := ih
      exact ⟨i, by omega, by rw [frz_succ_of_notMem V A h, he],
        by rw [frz_succ_of_notMem c A h, he']⟩

/-- the increment of the frozen field -/
lemma fxi_frz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω)
    (u : Fin d → ℝ) :
    fxi (frz V A) (frz c A) n ω u = (survS A n).indicator (fun ω => fxi V c n ω u) ω := by
  by_cases h : ω ∈ survS A n
  · rw [Set.indicator_of_mem h]
    unfold fxi fz
    rw [frz_eq_of_mem V A h, frz_eq_of_mem c A h]
    simp only [frz, if_pos h]
  · rw [Set.indicator_of_notMem h]
    unfold fxi fz
    rw [frz_succ_of_notMem V A h, frz_succ_of_notMem c A h]; ring

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.Fmono' (I : FI D μ F T V c J β B lo hi m0) {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ T) :
    F m ≤ F n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact (ih (by omega)).trans (I.Fmono n (by omega))

lemma FI.survS_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[F n] (survS A n) := by
  unfold survS
  refine Finset.measurableSet_biInter _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact I.Fmono' (by omega) hn _ (hA i (by omega))

lemma FI.frz_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (hX : ∀ n ≤ T, Measurable[F n] (X n)) :
    ∀ n ≤ T, Measurable[F n] (frz X A n) := by
  intro n hn
  induction n with
  | zero => exact hX 0 hn
  | succ n ih =>
    have hS := I.survS_meas hA (n := n) (by omega)
    have hmono := I.Fmono n (by omega)
    classical
    show Measurable[F (n + 1)] fun ω => if ω ∈ survS A n then X (n + 1) ω else frz X A n ω
    exact Measurable.ite (hmono _ hS) (hX (n + 1) hn) ((ih (by omega)).mono hmono le_rfl)

lemma FI.fxi_int [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n < T)
    {u : Fin d → ℝ} (hu : u ∈ D) :
    ∃ r : ℝ, Integrable (fun ω => fxi V c n ω u) μ ∧ ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r := by
  obtain ⟨r0, -, hr0⟩ := I.env' hn.le
  obtain ⟨r1, -, hr1⟩ := I.env' (n := n + 1) hn
  have hb : ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r1 + r0 := by
    filter_upwards [hr0, hr1] with ω h0 h1
    unfold fxi
    exact le_trans (abs_sub _ _) (add_le_add (h1.2 u hu) (h0.2 u hu))
  refine ⟨r1 + r0, ?_, hb⟩
  have hm : Measurable (fun ω => fxi V c n ω u) := by
    unfold fxi
    exact ((I.fz_meas hn u).mono (I.Fle (n + 1) hn) le_rfl).sub
      ((I.fz_meas hn.le u).mono (I.Fle n hn.le) le_rfl)
  exact Integrable.of_bound hm.aestronglyMeasurable _ (by
    filter_upwards [hb] with ω h; rwa [Real.norm_eq_abs])

lemma FI.frz_N0 (I : FI D μ F T V c J β B lo hi m0) (A : ℕ → Set Ω) {n : ℕ} (hn : n ≤ T) :
    ∀ᵐ ω ∂μ, 0 ≤ negMax D (frz V A n ω) (frz c A n ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1), 0 ≤ negMax D (V i ω) (c i ω) :=
    ae_all_iff.2 fun i => I.N0 i (by have := i.2; omega)
  filter_upwards [hall] with ω hω
  obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
  rw [hV, hc]; exact hω ⟨i, by omega⟩

/-- **freezing preserves the field interface** -/
theorem FI.freeze [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hβ : ∀ n, 0 ≤ β n) (hB : 0 < B) {J' : ℕ → Set Ω} (hJ'm : ∀ n ≤ T, MeasurableSet[F n] (J' n))
    (hJ'mono : ∀ n, J' (n + 1) ⊆ J' n) (hAJ : ∀ n, survS A n ∩ J' n ⊆ J n) :
    FI D μ F T (frz V A) (frz c A) J' β B lo hi m0 where
  hD := I.hD
  hconv := I.hconv
  hne := I.hne
  Fle := I.Fle
  Fmono := I.Fmono
  Vm := I.frz_meas hA V I.Vm
  cm := I.frz_meas hA c I.cm
  Jm := hJ'm
  Jmono := hJ'mono
  env := by
    intro n hn
    have : ∀ i ∈ Finset.range (n + 1), ∃ r : ℝ, ∀ᵐ ω ∂μ, ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r :=
      fun i hi => I.env i (by have := Finset.mem_range.1 hi; omega)
    choose r hr using this
    refine ⟨∑ i ∈ (Finset.range (n + 1)).attach, max (r i.1 i.2) 0, ?_⟩
    have hall : ∀ᵐ ω ∂μ, ∀ i : Finset.range (n + 1), ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r i.1 i.2 :=
      ae_all_iff.2 fun i => hr i.1 i.2
    filter_upwards [hall] with ω hω u hu
    obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
    have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have hle : max (r i hmem) 0 ≤ ∑ j ∈ (Finset.range (n + 1)).attach, max (r j.1 j.2) 0 :=
      Finset.single_le_sum (f := fun j : Finset.range (n + 1) => max (r j.1 j.2) 0)
        (fun j _ => le_max_right _ _) (Finset.mem_attach _ ⟨i, hmem⟩)
    rw [hV, hc]
    exact ((hω ⟨i, hmem⟩ u hu).trans (le_max_left _ _)).trans hle
  N0 := fun n hn => I.frz_N0 A hn
  drift := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, -⟩ := I.fxi_int hn hu
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u) =
          (survS A n).indicator (fun ω => fxi V c n ω u) := by
        funext ω; exact fxi_frz V c A n ω u
      rw [e]
      exact condExp_indicator hint hS
    filter_upwards [hce, I.drift n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω]; exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]; exact ⟨hlo, hhi⟩
  mag := by
    intro n hm0 hn
    filter_upwards [I.mag n hm0 hn, I.frz_N0 A hn.le] with ω hω hN hJ u hu
    by_cases hS : ω ∈ survS A n
    · rw [fxi_frz, Set.indicator_of_mem hS, fz, frz_eq_of_mem V A hS, frz_eq_of_mem c A hS]
      exact hω (hAJ n ⟨hS, hJ⟩) u hu
    · rw [fxi_frz, Set.indicator_of_notMem hS, abs_zero]
      have h1 := negMax_ge I.hD hu (frz V A n ω) (frz c A n ω)
      have h2 : 0 ≤ fz (frz V A) (frz c A) n ω u + 2 * negMax D (frz V A n ω) (frz c A n ω) := by
        unfold fz; linarith
      have := hβ n
      positivity
  sec := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, hb⟩ := I.fxi_int hn hu
    have hint2 : Integrable (fun ω => fxi V c n ω u ^ 2) μ := by
      refine Integrable.of_bound (hint.aestronglyMeasurable.pow 2) (r ^ 2) ?_
      filter_upwards [hb] with ω h
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u ^ 2 | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u ^ 2 | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u ^ 2) =
          (survS A n).indicator (fun ω => fxi V c n ω u ^ 2) := by
        funext ω
        rw [fxi_frz]
        by_cases hω : ω ∈ survS A n
        · simp [hω]
        · simp [hω]
      rw [e]
      exact condExp_indicator hint2 hS
    filter_upwards [hce, I.sec n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω, fz, frz_eq_of_mem V A hω, frz_eq_of_mem c A hω]
      exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]
      have := hβ n
      positivity

end

end G26


-- ===== Solutions.G26.NegRec =====

/-! ### The negative integral moment recurrence (Lemmas G.24, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma neg_fz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : Fin d → ℝ) :
    -fz V c n ω u = u ⬝ᵥ (-V n ω) + (-c n ω) := by
  unfold fz; rw [dotProduct_neg]; ring

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma vneg_lt (k : ℕ) (hk : 2 ≤ k) (B : ℝ) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) :
    1 + 1024 * (4 * k : ℝ) ^ 2 / B < 3 * k := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := by nlinarith
  have : 1024 * (4 * k : ℝ) ^ 2 / B ≤ k := by
    rw [div_le_iff₀ hB0]; nlinarith
  linarith

end G26


-- ===== Solutions.G26.RunK =====

/-! ### The loss-difference field on `K` satisfies the field interface (Lemma G.10) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

end

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Fx_lt {n : ℕ} (hn : n < T) : Fx R T n = R.G n := if_pos hn

lemma hist_le_m (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t ≤ T) : R.hist t ≤ mΩ := by
  unfold GRun.hist
  refine iSup₂_le fun s hs => ?_
  obtain ⟨⟨hX, hA, hY, -⟩, -⟩ := hR s (by omega)
  exact (hX.prodMk (hA.prodMk hY)).comap_le

lemma Fx_le (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (_ : n ≤ T) : Fx R T n ≤ mΩ := by
  unfold Fx; split_ifs with h
  · exact G2R.G_le hR h
  · exact le_rfl

lemma cumEst_Fx (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n ≤ T) :
    Measurable[Fx R T n] (R.cumEst n) := by
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt h]; exact (G2R.meas_cumEst hR hn).mono (G2R.hist_le_G hR h) le_rfl
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]; exact (G2R.meas_cumEst hR le_rfl).mono (hist_le_m hR le_rfl) le_rfl

lemma cumEst_succ (n : ℕ) (ω : Ω) : R.cumEst (n + 1) ω = R.cumEst n ω + R.thetaHat n ω := by
  simp [GRun.cumEst, Finset.sum_range_succ]

end G26R


-- ===== Solutions.G26.RunW =====

/-! ### The remaining-budget shifted field on `K` (Lemma G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ}

lemma setNorm_eq {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (w : Fin d → ℝ) :
    setNorm 𝒜 w = max (supp 𝒜 w) (supp 𝒜 (-w)) := by
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  apply le_antisymm
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    show |a ⬝ᵥ w| ≤ _
    rcases le_total 0 (a ⬝ᵥ w) with h | h
    · rw [abs_of_nonneg h]; exact (le_supp h𝒜 ha w).trans (le_max_left _ _)
    · rw [abs_of_nonpos h]
      have := le_supp h𝒜 ha (-w)
      rw [dotProduct_neg] at this
      exact this.trans (le_max_right _ _)
  · refine max_le ?_ ?_
    · obtain ⟨a, ha, he⟩ := supp_mem h𝒜 hne w
      rw [← he]
      exact (le_abs_self _).trans (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)
    · obtain ⟨a, ha, he⟩ := supp_mem h𝒜 hne (-w)
      rw [← he, dotProduct_neg]
      exact (neg_le_abs _).trans (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)

lemma setNorm_cont {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) :
    Continuous (setNorm 𝒜) := by
  have : setNorm 𝒜 = fun w => max (supp 𝒜 w) (supp 𝒜 (-w)) := funext (setNorm_eq h𝒜 hne)
  rw [this]
  exact (supp_cont h𝒜 hne).max ((supp_cont h𝒜 hne).comp continuous_neg)

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma G_mono (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {j n : ℕ} (hjn : j ≤ n) (hn : n < T) :
    R.G j ≤ R.G n := by
  induction n, hjn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hjn ih => exact (ih (by omega)).trans (hR n (by omega)).1.2.2.2.2.2.2.2.1

lemma Acum_Fx (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (θ : Fin d → ℝ) {n : ℕ} (hn : n ≤ T) : Measurable[Fx R T n] (Acum 𝒜 R θ n) := by
  unfold Acum
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hθj : Measurable[R.G j] (R.θs j) := (hR j (by omega)).1.2.2.2.2.2.2.1
  have hc := (setNorm_cont h𝒜 hne).measurable
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt h]
    exact hc.comp ((hθj.mono (G_mono hR hj'.le h) le_rfl).sub measurable_const)
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]
    exact hc.comp (((hR j hj').1.2.2.2.1).sub measurable_const)

lemma setNorm_nonneg (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (w : Fin d → ℝ) : 0 ≤ setNorm 𝒜 w := by
  obtain ⟨a, ha⟩ := hne
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  exact le_trans (abs_nonneg (a ⬝ᵥ w)) (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Acum_le (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) {θ : Fin d → ℝ} {C : ℝ}
    (hcor : IsCorruptedG P 𝒜 θ C T R) :
    ∀ᵐ ω ∂P, ∀ n ≤ T, 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C := by
  filter_upwards [hcor.2] with ω hω n hn
  refine ⟨Finset.sum_nonneg fun j _ => setNorm_nonneg h𝒜 hne _, le_trans ?_ hω⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
    (fun j _ _ => setNorm_nonneg h𝒜 hne _)

end G26R


-- ===== Solutions.G26.Geo =====

/-! ### The projective body of normalized directions (Lemma G.16) -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ}

variable {𝒜 ℬ : Set (Fin d → ℝ)} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma ne𝒜 : 𝒜.Nonempty := ⟨astar, H.hastar⟩

lemma haK : astar ∈ Kset ℬ := H.hgen.2 H.hastar

lemma Kc : IsCompact (Kset ℬ) := G2R.Kset_compact H.hℬ

omit H in
lemma Kconv : Convex ℝ (Kset ℬ) := convex_convexHull ℝ ℬ

lemma sig_pos : 0 < H.sig := (Classical.choose_spec H.hsharp).1

lemma sig_spec {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) :
    H.sig * sNorm ℬ (a - astar) ≤ gap θ astar a := by
  have h := (Classical.choose_spec H.hsharp).2 a (by rw [G1L.Kset_gen H.hgen]; exact ha)
  rw [G1L.sNorm_gen H.hgen] at h
  exact h

omit H in
lemma sNorm_nonneg (x : Fin d → ℝ) : 0 ≤ sNorm ℬ x := by unfold sNorm; exact gauge_nonneg _

lemma norm_le (x : Fin d → ℝ) : ‖x‖ ≤ sNorm ℬ x := by
  rw [← G1L.sNorm_gen H.hgen]; exact T31.norm_le_sNorm H.ne𝒜 H.hspan H.hball x

lemma gap_pos {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (hne : a ≠ astar) : 0 < gap θ astar a := by
  have h1 : 0 < ‖a - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h2 := H.norm_le (a - astar)
  exact lt_of_lt_of_le (mul_pos H.sig_pos (lt_of_lt_of_le h1 h2)) (H.sig_spec ha)

/-- duality of the gauge of `𝒮` and the norm `‖·‖_𝒜` -/
lemma abs_dot_le_sNorm (x w : Fin d → ℝ) : |x ⬝ᵥ w| ≤ sNorm ℬ x * setNorm 𝒜 w := by
  rw [← G1L.sNorm_gen H.hgen]
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  have hbdd := (H.h𝒜.image hcont).bddAbove
  have hS : ∀ y ∈ Sset 𝒜, |y ⬝ᵥ w| ≤ setNorm 𝒜 w := by
    intro y hy
    have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} := by
      have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ w) :=
        ⟨fun x y => add_dotProduct x y w, fun c x => smul_dotProduct c x w⟩
      have : {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} =
          {v | v ⬝ᵥ w ≤ setNorm 𝒜 w} ∩ {v | -setNorm 𝒜 w ≤ v ⬝ᵥ w} := by
        ext x; simp [abs_le, and_comm]
      rw [this]
      exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
    refine convexHull_min ?_ hcvx hy
    rintro a (ha | ha)
    · exact le_csSup hbdd ⟨a, ha, rfl⟩
    · have : -a ∈ 𝒜 := ha
      show |a ⬝ᵥ w| ≤ _
      have h := le_csSup hbdd ⟨-a, this, rfl⟩
      simp only [neg_dotProduct, abs_neg] at h
      exact h
  have habs : Absorbent ℝ (Sset 𝒜) := absorbent_nhds_zero (T31.Sset_nhds H.ne𝒜 H.hspan)
  have hsn : 0 ≤ setNorm 𝒜 w := le_trans (abs_nonneg _) (hS 0 (by
    have : (0 : Fin d → ℝ) ∈ Sset 𝒜 := mem_of_mem_nhds (T31.Sset_nhds H.ne𝒜 H.hspan)
    exact this))
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  -- for every `r > ‖x‖_S ‖w‖`, `|x·w| ≤ r`
  by_cases hw : setNorm 𝒜 w = 0
  · -- `w` is orthogonal to `𝒜`, hence zero
    have hz : ∀ a ∈ 𝒜, a ⬝ᵥ w = 0 := fun a ha => by
      have h1 : |a ⬝ᵥ w| ≤ setNorm 𝒜 w := le_csSup hbdd ⟨a, ha, rfl⟩
      rw [hw] at h1
      exact abs_nonpos_iff.1 h1
    have hw0 : w = 0 := by
      have : ∀ v ∈ Submodule.span ℝ 𝒜, v ⬝ᵥ w = 0 := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem x hx => exact hz x hx
        | zero => simp
        | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
        | smul c x _ hx => rw [smul_dotProduct, hx, smul_zero]
      rw [H.hspan] at this
      ext i
      have := this (Pi.single i 1) trivial
      simpa [single_dotProduct] using this
    rw [hw0, dotProduct_zero, abs_zero]
    rw [hw, mul_zero] at hr; exact hr.le
  · have hwpos : 0 < setNorm 𝒜 w := lt_of_le_of_ne hsn (Ne.symm hw)
    have hlt : gauge (Sset 𝒜) x < r / setNorm 𝒜 w := by
      rw [lt_div_iff₀ hwpos]; unfold sNorm at hr; exact hr
    obtain ⟨b, hb0, hbr, hxb⟩ := exists_lt_of_gauge_lt habs hlt
    obtain ⟨y, hy, rfl⟩ := hxb
    rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_pos hb0]
    calc b * |y ⬝ᵥ w| ≤ b * setNorm 𝒜 w := mul_le_mul_of_nonneg_left (hS y hy) hb0.le
      _ ≤ r / setNorm 𝒜 w * setNorm 𝒜 w := mul_le_mul_of_nonneg_right hbr.le hwpos.le
      _ = r := div_mul_cancel₀ r hwpos.ne'

end Sharp

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma U0_ne : (U0 ℬ θ astar).Nonempty := by
  obtain ⟨b, hb, hba⟩ := G1L.exists_ne H.hk astar
  exact ⟨_, b, ⟨subset_convexHull ℝ ℬ hb, hba⟩, rfl⟩

lemma U0_sNorm {u : Fin d → ℝ} (hu : u ∈ U0 ℬ θ astar) : sNorm ℬ u ≤ H.sig⁻¹ := by
  obtain ⟨a, ⟨ha, hne⟩, rfl⟩ := hu
  have h := H.gap_pos ha hne
  unfold ndir sNorm
  rw [gauge_smul_of_nonneg (inv_nonneg.2 h.le), smul_eq_mul]
  have h2 := H.sig_spec ha
  unfold sNorm at h2
  rw [inv_mul_le_iff₀ h]
  have hs := H.sig_pos
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  linarith

lemma U0_convex : Convex ℝ (U0 ℬ θ astar) := by
  rintro _ ⟨a1, ⟨ha1, hne1⟩, rfl⟩ _ ⟨a2, ⟨ha2, hne2⟩, rfl⟩ s t hs ht hst
  have g1 := H.gap_pos ha1 hne1
  have g2 := H.gap_pos ha2 hne2
  set Δ1 := gap θ astar a1
  set Δ2 := gap θ astar a2
  set c := s / Δ1 + t / Δ2 with hc
  have hc0 : 0 < c := by
    rcases eq_or_lt_of_le hs with h | h
    · have : 0 < t := by linarith
      rw [hc, ← h, zero_div, zero_add]; positivity
    · have : 0 ≤ t / Δ2 := by positivity
      rw [hc]; have : 0 < s / Δ1 := by positivity
      linarith
  set w1 := s / (c * Δ1)
  set w2 := t / (c * Δ2)
  have hw1 : 0 ≤ w1 := by positivity
  have hw2 : 0 ≤ w2 := by positivity
  have hw12 : w1 + w2 = 1 := by
    have : w1 + w2 = (s / Δ1 + t / Δ2) / c := by simp only [w1, w2]; field_simp
    rw [this, ← hc, div_self hc0.ne']
  set a := w1 • a1 + w2 • a2
  have haK : a ∈ Kset ℬ := Kconv ha1 ha2 hw1 hw2 hw12
  have hgap : gap θ astar a = 1 / c := by
    unfold gap
    have : a - astar = w1 • (a1 - astar) + w2 • (a2 - astar) := by
      simp only [a, smul_sub]
      have hh : astar = w1 • astar + w2 • astar := by rw [← add_smul, hw12, one_smul]
      conv_lhs => rw [hh]
      abel
    rw [this, add_dotProduct, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
    change w1 * Δ1 + w2 * Δ2 = 1 / c
    have e1 : w1 * Δ1 = s / c := by simp only [w1]; field_simp
    have e2 : w2 * Δ2 = t / c := by simp only [w2]; field_simp
    rw [e1, e2, ← add_div, hst]
  have hne : a ≠ astar := by
    intro h
    have := H.gap_pos haK
    rw [hgap] at this
    have h0 : gap θ astar a = 0 := by rw [h]; unfold gap; simp
    rw [hgap] at h0
    have : (1 : ℝ) / c ≠ 0 := by positivity
    exact this h0
  refine ⟨a, ⟨haK, hne⟩, ?_⟩
  unfold ndir
  rw [hgap]
  have : a - astar = w1 • (a1 - astar) + w2 • (a2 - astar) := by
    simp only [a, smul_sub]
    have hh : astar = w1 • astar + w2 • astar := by rw [← add_smul, hw12, one_smul]
    conv_lhs => rw [hh]
    abel
  rw [this, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  · congr 1; simp only [w1]; rw [show gap θ astar a1 = Δ1 from rfl]; field_simp
  · congr 1; simp only [w2]; rw [show gap θ astar a2 = Δ2 from rfl]; field_simp

lemma U0_bdd : U0 ℬ θ astar ⊆ Metric.closedBall 0 H.sig⁻¹ := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (H.norm_le u).trans (H.U0_sNorm hu)

lemma UT_compact : IsCompact (UT ℬ θ astar) :=
  (isCompact_closedBall (0 : Fin d → ℝ) H.sig⁻¹).of_isClosed_subset isClosed_closure
    (closure_minimal H.U0_bdd Metric.isClosed_closedBall)

lemma UT_convex : Convex ℝ (UT ℬ θ astar) := H.U0_convex.closure

lemma UT_ne : (UT ℬ θ astar).Nonempty := H.U0_ne.mono subset_closure

lemma UT_bdd {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) : ‖u‖ ≤ H.sig⁻¹ := by
  have := closure_minimal H.U0_bdd Metric.isClosed_closedBall hu
  rwa [Metric.mem_closedBall, dist_zero_right] at this

lemma DT_compact : IsCompact (DT ℬ θ astar) :=
  (isCompact_Icc.prod H.UT_compact).image (continuous_fst.smul continuous_snd)

lemma zero_mem_DT : (0 : Fin d → ℝ) ∈ DT ℬ θ astar := by
  obtain ⟨u, hu⟩ := H.UT_ne
  exact ⟨(0, u), ⟨⟨le_rfl, zero_le_one⟩, hu⟩, zero_smul _ _⟩

lemma DT_ne : (DT ℬ θ astar).Nonempty := ⟨0, H.zero_mem_DT⟩

lemma UT_sub_DT : UT ℬ θ astar ⊆ DT ℬ θ astar := fun u hu =>
  ⟨(1, u), ⟨⟨zero_le_one, le_rfl⟩, hu⟩, one_smul _ _⟩

lemma DT_mem {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) :
    ∃ l ∈ Icc (0 : ℝ) 1, ∃ u ∈ UT ℬ θ astar, w = l • u := by
  obtain ⟨⟨l, u⟩, ⟨hl, hu⟩, rfl⟩ := hw
  exact ⟨l, hl, u, hu, rfl⟩

/-- **homogeneous transfer**: a continuous degree-`k` homogeneous bound on centered differences
`φ(a − a*) ≤ Δ(a)^k M` passes to the cone body -/
lemma homog {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) {k : ℕ}
    (hhom : ∀ (c : ℝ) (w : Fin d → ℝ), 0 ≤ c → φ (c • w) = c ^ k * φ w) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ a ∈ Kset ℬ, a ≠ astar → φ (a - astar) ≤ gap θ astar a ^ k * M) :
    ∀ w ∈ DT ℬ θ astar, φ w ≤ M := by
  have hU0 : ∀ u ∈ U0 ℬ θ astar, φ u ≤ M := by
    rintro _ ⟨a, ⟨ha, hne⟩, rfl⟩
    have g := H.gap_pos ha hne
    unfold ndir
    rw [hhom _ _ (inv_nonneg.2 g.le), inv_pow]
    rw [inv_mul_le_iff₀ (pow_pos g k)]
    exact hK a ha hne
  have hUT : ∀ u ∈ UT ℬ θ astar, φ u ≤ M := fun u hu =>
    closure_minimal hU0 (isClosed_le hφ continuous_const) hu
  intro w hw
  obtain ⟨l, ⟨hl0, hl1⟩, u, hu, rfl⟩ := H.DT_mem hw
  rw [hhom _ _ hl0]
  have h1 := hUT u hu
  have h2 : l ^ k ≤ 1 := pow_le_one₀ hl0 hl1
  have h3 : 0 ≤ l ^ k := pow_nonneg hl0 k
  nlinarith

/-- `|u·w| ≤ ‖w‖_𝒜 / ς` on the cone body -/
lemma DT_dot_le (w : Fin d → ℝ) : ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ H.sig⁻¹ * setNorm 𝒜 w := by
  have hsn : 0 ≤ setNorm 𝒜 w := le_trans (abs_nonneg _)
    (le_csSup ((H.h𝒜.image (by simp only [dotProduct]; fun_prop :
      Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w|)).bddAbove) ⟨astar, H.hastar, rfl⟩)
  refine H.homog (φ := fun u => |u ⬝ᵥ w|) (by simp only [dotProduct]; fun_prop)
    (fun c v hc => by rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_nonneg hc, pow_one])
    (by have := H.sig_pos; positivity) ?_
  intro a ha hne
  have h1 := H.abs_dot_le_sNorm (a - astar) w
  have h2 := H.sig_spec ha
  have hs := H.sig_pos
  rw [pow_one]
  calc |(a - astar) ⬝ᵥ w| ≤ sNorm ℬ (a - astar) * setNorm 𝒜 w := h1
    _ ≤ (gap θ astar a / H.sig) * setNorm 𝒜 w := by
        gcongr; rw [le_div_iff₀ hs]; linarith
    _ = gap θ astar a * (H.sig⁻¹ * setNorm 𝒜 w) := by ring

/-- the cone body lies in the span of the centered differences -/
lemma DT_sub_span : DT ℬ θ astar ⊆
    (Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ) : Set (Fin d → ℝ)) := by
  set V := Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ)
  have hV : IsClosed (V : Set (Fin d → ℝ)) := Submodule.closed_of_finiteDimensional V
  have hU0 : U0 ℬ θ astar ⊆ V := by
    rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact V.smul_mem _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  have hUT : UT ℬ θ astar ⊆ V := closure_minimal hU0 hV
  rintro _ ⟨⟨l, u⟩, ⟨-, hu⟩, rfl⟩
  exact V.smul_mem l (hUT hu)

lemma DT_bdd {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) : ‖w‖ ≤ H.sig⁻¹ := by
  obtain ⟨l, ⟨hl0, hl1⟩, u, hu, rfl⟩ := H.DT_mem hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]
  have := H.UT_bdd hu
  have hs : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  nlinarith [norm_nonneg u]

/-- **projective extension (G.306)**: the normalized field is dominated by the centered field -/
lemma DT_span_bound : ∃ Λ1 : ℝ, 0 < Λ1 ∧ ∀ (w : Fin d → ℝ) (M : ℝ),
    (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) → ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M := by
  classical
  set s := (fun a => a - astar) '' Kset ℬ
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ s
  have : Finite b := hli.finite_of_isNoetherian
  haveI : Fintype b := Fintype.ofFinite b
  set L := Fintype.linearCombination ℝ (fun i : b => (i : Fin d → ℝ))
  have hL : LinearMap.range L = Submodule.span ℝ s := by
    rw [Fintype.range_linearCombination, Subtype.range_coe, hspan]
  obtain ⟨g, hg⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  set gc := LinearMap.toContinuousLinearMap g
  refine ⟨(Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1, add_pos_of_nonneg_of_pos (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) gc.opNorm_nonneg) (inv_nonneg.2 H.sig_pos.le)) one_pos, ?_⟩
  intro w M hM u hu
  have hM0 : 0 ≤ M := by
    have := hM astar H.haK
    simpa using le_trans (abs_nonneg _) this
  have huV : u ∈ LinearMap.range L := by rw [hL]; exact H.DT_sub_span hu
  set c := g ⟨u, huV⟩
  have hLc : L c = u := by
    have := congrArg Subtype.val (LinearMap.congr_fun hg ⟨u, huV⟩)
    simpa [c] using this
  have hc : ‖c‖ ≤ ‖gc‖ * H.sig⁻¹ := by
    have h1 : ‖c‖ ≤ ‖gc‖ * ‖(⟨u, huV⟩ : LinearMap.range L)‖ := gc.le_opNorm _
    have h2 : ‖(⟨u, huV⟩ : LinearMap.range L)‖ = ‖u‖ := rfl
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (H.DT_bdd hu) gc.opNorm_nonneg)
  rw [← hLc, Fintype.linearCombination_apply, sum_dotProduct]
  calc |∑ i : b, (c i • (i : Fin d → ℝ)) ⬝ᵥ w| ≤ ∑ i : b, |(c i • (i : Fin d → ℝ)) ⬝ᵥ w| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : b, ‖c‖ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [smul_dotProduct, smul_eq_mul, abs_mul]
        obtain ⟨a, ha, hai⟩ := hbs i.2
        have h1 : |(i : Fin d → ℝ) ⬝ᵥ w| ≤ M := by rw [← hai]; exact hM a ha
        have h2 : |c i| ≤ ‖c‖ := by
          have := norm_le_pi_norm c i
          rwa [Real.norm_eq_abs] at this
        exact mul_le_mul h2 h1 (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card b : ℝ) * ‖c‖ * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ((Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1) * M := by
        have : (Fintype.card b : ℝ) * ‖c‖ ≤ (Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1 := by
          have := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (Fintype.card b))
          linarith
        exact mul_le_mul_of_nonneg_right this hM0

end Sharp

end G26G


-- ===== Solutions.G26.RefGood =====

/-! ### A measurable sufficient condition for the reference to be `a*` -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

lemma goodS_meas (js n : ℕ) : MeasurableSet {S : Fin d → ℝ | goodS ℬ e js n S} := by
  have : {S : Fin d → ℝ | goodS ℬ e js n S} = ⋂ i : ℕ, {S | i ∈ Jset ℬ e → i ≠ js →
      cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js < cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} := by
    ext S; simp [goodS]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  by_cases h : i ∈ Jset ℬ e ∧ i ≠ js
  · have e1 : {S : Fin d → ℝ | i ∈ Jset ℬ e → i ≠ js →
        cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js < cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} =
        {S | cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js <
          cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} := by
      ext S; simp [h.1, h.2]
    rw [e1]
    exact measurableSet_lt (by simp only [dotProduct]; fun_prop) (by simp only [dotProduct]; fun_prop)
  · have e1 : {S : Fin d → ℝ | i ∈ Jset ℬ e → i ≠ js →
        cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js < cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} =
        univ := by
      ext S; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e1]; exact MeasurableSet.univ

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

lemma D0_nonneg : 0 ≤ H.D0 he :=
  Finset.sum_nonneg fun i _ => inv_nonneg.2 (sNorm_nonneg _)

end Sharp

end G26G


-- ===== Solutions.G26.RunN =====

/-! ### The normalized field on the cone body satisfies the field interface (Lemmas G.17, G.28) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma Lam1_eq : ∃ h, Lam1 ℬ θ astar = Classical.choose (p := fun Λ1 : ℝ => 0 < Λ1 ∧
    ∀ (w : Fin d → ℝ) (M : ℝ), (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) →
      ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M) h :=
  ⟨H.DT_span_bound, by unfold Lam1; rw [dif_pos H.DT_span_bound]⟩

lemma Lam1_pos : 0 < Lam1 ℬ θ astar := by
  obtain ⟨h, e⟩ := H.Lam1_eq; rw [e]; exact (Classical.choose_spec h).1

lemma Lam1_spec {w : Fin d → ℝ} {M : ℝ} (hM : ∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) {u : Fin d → ℝ}
    (hu : u ∈ DT ℬ θ astar) : |u ⬝ᵥ w| ≤ Lam1 ℬ θ astar * M := by
  obtain ⟨h, e⟩ := H.Lam1_eq; rw [e]; exact (Classical.choose_spec h).2 w M hM u hu

lemma kb_ge : 1 ≤ H.kb ∧ H.sig⁻¹ ≤ H.kb ∧ H.sig⁻¹ ^ 2 ≤ H.kb := by
  have : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  unfold kb; refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end Sharp

end G26G

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Fx_mono' (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {j n : ℕ} (hjn : j ≤ n) (hn : n ≤ T) :
    Fx R T j ≤ Fx R T n := by
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt (lt_of_le_of_lt hjn h), Fx_lt h]; exact G_mono hR hjn h
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]; exact Fx_le hR (le_trans hjn le_rfl)

lemma good_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (js : ℕ) {j : ℕ} (hj : j ≤ T) :
    MeasurableSet[Fx R T j] {ω | goodS ℬ e js (j + 1) (R.cumEst j ω)} :=
  cumEst_Fx hR hj (goodS_meas js (j + 1))

lemma JN_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (js m : ℕ) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[Fx R T n] (JN ℬ e js R m n) := by
  have : JN ℬ e js R m n = ⋂ j : ℕ, {ω | m ≤ j → j ≤ n → goodS ℬ e js (j + 1) (R.cumEst j ω)} := by
    ext ω; simp [JN]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  by_cases h : m ≤ j ∧ j ≤ n
  · have e1 : {ω | m ≤ j → j ≤ n → goodS ℬ e js (j + 1) (R.cumEst j ω)} =
        {ω | goodS ℬ e js (j + 1) (R.cumEst j ω)} := by
      ext ω; simp [h.1, h.2]
    rw [e1]
    exact Fx_mono' hR h.2 hn _ (good_meas hR js (le_trans h.2 hn))
  · have e1 : {ω | m ≤ j → j ≤ n → goodS ℬ e js (j + 1) (R.cumEst j ω)} = univ := by
      ext ω; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e1]; exact MeasurableSet.univ

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.Scalar =====

/-! ### Killed scalar local moments (Lemma G.22 and the local moments of Lemma G.28) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

lemma SI.Ym' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : Measurable (Y n) :=
  (S.Ym n hn).mono (S.Fle n hn) le_rfl

lemma SI.Im' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : MeasurableSet (I n) :=
  S.Fle n hn _ (S.Im n hn)

lemma SI.kinv_int [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B) {n : ℕ} (hmn : m ≤ n)
    (hn : n ≤ N) (P : ℕ) :
    Integrable ((I n).indicator (fun ω => (Y n ω)⁻¹ ^ P)) μ := by
  refine Integrable.of_bound (((S.Ym' hn).inv.pow_const P).indicator (S.Im' hn)).aestronglyMeasurable
    ((τ n)⁻¹ ^ P) ?_
  filter_upwards [S.low n hmn hn] with ω hω
  rw [Real.norm_eq_abs]
  by_cases h : ω ∈ I n
  · rw [Set.indicator_of_mem h]
    have hτ := S.τpos n
    have hy := hω h
    rw [abs_of_nonneg (by have : 0 < Y n ω := by linarith
                          positivity)]
    exact pow_le_pow_left₀ (by have : 0 < Y n ω := by linarith
                               positivity) (inv_anti₀ hτ hy) _
  · rw [Set.indicator_of_notMem h, abs_zero]; have := S.τpos n; positivity

end G26


-- ===== Solutions.G26.SIFreeze =====

/-! ### Freezing a scalar interface at a predictable success rule (Lemma G.29, (G.653)–(G.659)) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

open Classical in
/-- the freezing index: the first failure of the rule before `n`, or `n` -/
noncomputable def fidx (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ i, i < n ∧ ω ∉ A i then Nat.find h else n

lemma frz_fidx {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    frz X A n ω = X (fidx A n ω) ω ∧ fidx A n ω ≤ n ∧
      (fidx A n ω = n ∨ ω ∉ A (fidx A n ω)) ∧ ∀ j < fidx A n ω, ω ∈ A j := by
  classical
  unfold fidx
  split_ifs with h
  · have hspec := Nat.find_spec h
    have hmin : ∀ j < Nat.find h, ω ∈ A j := fun j hj => by
      by_contra hj'
      exact Nat.find_min h hj ⟨by have := hspec.1; omega, hj'⟩
    have hsurv : Nat.find h = 0 ∨ ω ∈ survS A (Nat.find h - 1) := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact hmin j (by omega)
    exact ⟨frz_stop X A hsurv hspec.2 n hspec.1.le, hspec.1.le, Or.inr hspec.2, hmin⟩
  · push Not at h
    have hs : n = 0 ∨ ω ∈ survS A (n - 1) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact h j (by omega)
    exact ⟨frz_eq X A n ω hs, le_rfl, Or.inl rfl, fun j hj => h j hj⟩

lemma frz_before {E : Type*} (X : ℕ → Ω → E) {A : ℕ → Set Ω} {u : ℕ} (hA : ∀ n < u, A n = univ) :
    frz X A u = X u := by
  funext ω
  refine frz_eq X A u ω ?_
  rcases Nat.eq_zero_or_pos u with h | h
  · exact Or.inl h
  · right
    simp only [survS, Set.mem_iInter, Finset.mem_range]
    intro j hj; rw [hA j (by omega)]; trivial

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26


-- ===== Solutions.G26.RunSIN =====

/-! ### Compensated normalized pointwise variables (Lemma G.28, (G.595)–(G.601)) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma EcorN_le {u : Fin d → ℝ} (hu : u ∈ DT ℬ θ astar) (n : ℕ) (ω : Ω) :
    |Ecor R θ u n ω| ≤ H.sig⁻¹ * Acum 𝒜 R θ n ω := by
  unfold Ecor Acum
  rw [Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => H.DT_dot_le _ u hu)

lemma IN_meas (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (C : ℝ)
    (τ : ℕ → ℝ) (m : ℕ) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[Fx R T n] (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C τ m n) := by
  refine (JN_meas hR _ m hn).inter ?_
  have : {ω | ∀ j, m ≤ j → j ≤ n → negMax (DT ℬ θ astar) (R.cumEst j ω)
      (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} = ⋂ j : ℕ, {ω | m ≤ j → j ≤ n →
      negMax (DT ℬ θ astar) (R.cumEst j ω) (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} := by
    ext ω; simp
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  by_cases h : m ≤ j ∧ j ≤ n
  · have e1 : {ω | m ≤ j → j ≤ n → negMax (DT ℬ θ astar) (R.cumEst j ω)
        (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} = {ω | negMax (DT ℬ θ astar) (R.cumEst j ω)
        (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} := by
      ext ω; simp [h.1, h.2]
    rw [e1]
    have hS := cumEst_Fx hR (le_trans h.2 hn)
    have hc : Measurable[Fx R T j] (cN 𝒜 R θ H.sig⁻¹ C j) :=
      (measurable_const.mul (measurable_const.sub
        (Acum_Fx H.h𝒜 H.ne𝒜 hR θ (le_trans h.2 hn)))).neg
    have hm := G26.negMax_meas H.DT_compact H.DT_ne hS hc
    exact Fx_mono' hR h.2 hn _ (measurableSet_le hm measurable_const)
  · have e1 : {ω | m ≤ j → j ≤ n → negMax (DT ℬ θ astar) (R.cumEst j ω)
        (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} = univ := by
      ext ω; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e1]; exact MeasurableSet.univ

lemma YN_low {u : Fin d → ℝ} (hu : u ∈ DT ℬ θ astar) {C : ℝ} {τ : ℕ → ℝ} {n : ℕ} {ω : Ω}
    (hA0 : 0 ≤ Acum 𝒜 R θ n ω) (hAC : Acum 𝒜 R θ n ω ≤ C)
    (hQ : negMax (DT ℬ θ astar) (R.cumEst n ω) (cN 𝒜 R θ H.sig⁻¹ C n ω) ≤ τ n) :
    τ n ≤ YN R θ H.sig⁻¹ C τ u n ω ∧ max 0 (u ⬝ᵥ R.cumEst n ω) ≤ YN R θ H.sig⁻¹ C τ u n ω ∧
      YN R θ H.sig⁻¹ C τ u n ω ≤ u ⬝ᵥ R.cumEst n ω + 2 * H.sig⁻¹ * C + 2 * τ n := by
  have hl : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  have hE := H.EcorN_le (R := R) hu n ω
  have h1 := negMax_ge H.DT_compact hu (R.cumEst n ω) (cN 𝒜 R θ H.sig⁻¹ C n ω)
  have h0 := negMax_ge H.DT_compact H.zero_mem_DT (R.cumEst n ω) (cN 𝒜 R θ H.sig⁻¹ C n ω)
  simp only [zero_dotProduct, zero_add] at h0
  unfold cN at h1 hQ h0
  have hex : H.sig⁻¹ * (C - Acum 𝒜 R θ n ω) = H.sig⁻¹ * C - H.sig⁻¹ * Acum 𝒜 R θ n ω := by ring
  rw [hex] at h1 hQ h0
  have hlA : H.sig⁻¹ * Acum 𝒜 R θ n ω ≤ H.sig⁻¹ * C := mul_le_mul_of_nonneg_left hAC hl
  have hlA0 : 0 ≤ H.sig⁻¹ * Acum 𝒜 R θ n ω := mul_nonneg hl hA0
  have hτ0 : 0 ≤ τ n := by linarith
  unfold YN
  have hE1 := (abs_le.1 hE).1
  have hE2 := (abs_le.1 hE).2
  refine ⟨?_, max_le ?_ ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

end Sharp

end G26G


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma rdim_le (D : Set (Fin d → ℝ)) : rdim D ≤ d := by
  unfold rdim
  have := Submodule.finrank_le (vectorSpan ℝ D)
  simpa using this

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.absMax_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ}
    (hn : n ≤ T) (P : ℕ) : Integrable (fun ω => absMax D (V n ω) (c n ω) ^ P) μ := by
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine Integrable.of_bound
    (((I.absMax_meas hn).mono (I.Fle n hn) le_rfl).pow_const P).aestronglyMeasurable (r ^ P) ?_
  filter_upwards [hr, I.N0 n hn] with ω h h0
  have h1 : 0 ≤ absMax D (V n ω) (c n ω) := h0.trans (negMax_le_absMax _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h1 _)]
  exact pow_le_pow_left₀ h1 h.1 P

end G26

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma kk_facts (d : ℕ) : 2 ≤ kk d ∧ 4 ≤ 4 * kk d ∧ Even (4 * kk d) ∧ d ≤ 4 * kk d ∧
    2 ^ 20 * ((4 * kk d : ℕ) : ℝ) ≤ gB d := by
  unfold kk gB
  refine ⟨by omega, by omega, ⟨2 * (1024 * (d + 1)), by ring⟩, by omega, ?_⟩
  push_cast; nlinarith

lemma cK_nonneg (d : ℕ) : 0 ≤ cK d := by
  unfold cK Cabs; positivity

lemma gbeta_le (d n : ℕ) : gbeta d (n + 1) ≤ (16 * d + 1) * ((n : ℝ) + 1) := by
  unfold gbeta
  have h1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; push_cast; nlinarith
  have h2 : (16 * d : ℝ) ≤ 16 * d * ((n : ℝ) + 1) := by
    have : (0 : ℝ) ≤ 16 * d := by positivity
    nlinarith
  nlinarith

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

/-- **the absolute envelope of the jointly frozen loss-difference field (G.288)** -/
theorem absK_env (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[Fx R T n] (A n)) {n : ℕ} (hn : n ≤ T) :
    ∫ ω, absMax (Kset ℬ) (frz R.cumEst A n ω)
      (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A n ω) ^ (4 * kk d) ∂P ≤
      cK d * ((n : ℝ) + 1) ^ (4 * kk d) := by
  obtain ⟨hk2, hP4, hev, hdP, hB⟩ := kk_facts d
  have I0 := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
  have I := I0.freeze hA (by norm_num) (by norm_num) (fun n => (G2R.gbeta_pos H.hd (n + 1)).le)
    G2R.gB_pos (J' := fun _ => univ) (fun _ _ => MeasurableSet.univ) (fun _ => subset_rfl)
    (fun _ => subset_univ _)
  have h0 : ∀ ω, Gf (Kset ℬ) (frz R.cumEst A) (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A)
      (4 * kk d) 0 ω = 0 := by
    intro ω
    unfold Gf fz
    simp only [frz, GRun.cumEst, Finset.range_zero, Finset.sum_empty, dotProduct_zero, neg_zero,
      add_zero]
    rw [zero_pow (by omega)]; simp
  have h := I.absMax_env (by norm_num) le_rfl hP4 hev ((rdim_le _).trans hdP) hB
    (fun n => G2R.gbeta_pos H.hd (n + 1)) (fun n => gbeta_le d n) h0 hn
  simp only [Set.indicator_univ] at h
  refine h.trans ?_
  unfold cK
  have h4 : (4 : ℝ) ^ rdim (Kset ℬ) ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (rdim_le _)
  have hC : 0 ≤ Cabs (4 * kk d) (16 * d + 1) (gB d) 0 := by unfold Cabs; positivity
  gcongr

end Sharp

end G26G


-- ===== Solutions.G26.Params =====

/-! ### Thresholds: buffers `τ_s = (s+1)^{7/8} + 4z` and logarithmic gap cutoffs -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

lemma p78_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ ((7 : ℝ) / 8) ≤ y ^ ((7 : ℝ) / 8) :=
  Real.rpow_le_rpow hx hxy (by norm_num)

lemma p78_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ ((7 : ℝ) / 8) :=
  Real.one_le_rpow hx (by norm_num)

lemma tauB_mono {z : ℝ} (s : ℕ) : tauB z s ≤ tauB z (s + 1) := by
  unfold tauB
  have := p78_mono (x := (s : ℝ) + 1) (y := ((s + 1 : ℕ) : ℝ) + 1) (by positivity) (by push_cast; linarith)
  linarith

lemma tauB_delta (z : ℝ) (s : ℕ) : tauB z (s + 1) - tauB z s ≤ 1 := by
  unfold tauB
  have h := Real.rpow_add_le_add_rpow (p := (7 : ℝ) / 8) (a := (s : ℝ) + 1) (b := 1)
    (by positivity) zero_le_one (by norm_num) (by norm_num)
  rw [Real.one_rpow] at h
  have e : ((s + 1 : ℕ) : ℝ) + 1 = (s : ℝ) + 1 + 1 := by push_cast; ring
  rw [e]; linarith

lemma tauB_ge {z : ℝ} (hz : 0 ≤ z) (s : ℕ) :
    ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ tauB z s ∧ 4 * z ≤ tauB z s ∧ 1 ≤ tauB z s := by
  unfold tauB
  have h1 := p78_ge_one (x := (s : ℝ) + 1) (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine ⟨by linarith, ?_, by linarith⟩
  have : 0 ≤ ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) := by positivity
  linarith

lemma tauB_pos {z : ℝ} (hz : 0 ≤ z) (s : ℕ) : 0 < tauB z s := by
  linarith [(tauB_ge hz s).2.2]

lemma root8_pow {x : ℝ} (hx : 0 ≤ x) : root8 x ^ 8 = x := by
  unfold root8
  have h1 : Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt (Real.sqrt x) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 8 =
      ((Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2, h3]

lemma root8_nonneg (x : ℝ) : 0 ≤ root8 x := Real.sqrt_nonneg _

lemma root8_mono {x y : ℝ} (hxy : x ≤ y) : root8 x ≤ root8 y := by
  unfold root8
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy))

end G26G

namespace G26G

lemma root8_eq_rpow {x : ℝ} (hx : 0 ≤ x) : root8 x = x ^ ((1 : ℝ) / 8) := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have h2 := root8_pow hx
  have hn1 : 0 ≤ x ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hx _
  exact (pow_left_inj₀ (root8_nonneg x) hn1 (by norm_num : (8 : ℕ) ≠ 0)).1 (h2.trans h1.symm)

lemma rpow78_eq {x : ℝ} (hx : 0 ≤ x) : x ^ ((7 : ℝ) / 8) = root8 x ^ 7 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma sqrt_eq_root8 {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x = root8 x ^ 4 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]; norm_num

end G26G


-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma markov' {μ : Measure Ω} {g : Ω → ℝ} (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω) (hgi : Integrable g μ) {c : ℝ}
    (hc : 0 < c) : μ.real {ω | c ≤ g ω} ≤ (∫ ω, g ω ∂μ) / c := by
  have := mul_meas_ge_le_integral_of_nonneg hg0 hgi c
  rw [le_div_iff₀ hc]; linarith

lemma frz_univ {E : Type*} (X : ℕ → Ω → E) (n : ℕ) : frz X (fun _ => univ) n = X n := by
  funext ω
  obtain ⟨h1, -, h3, -⟩ := frz_fidx X (fun _ => (univ : Set Ω)) n ω
  rcases h3 with h | h
  · rw [h1, h]
  · exact absurd trivial h

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

variable (he : Function.Surjective e)
include he

end Sharp

end G26G


-- ===== Solutions.G26.RefAlg =====

/-! ### Real-variable estimates for the reference block bound -/

open IAFTRL

namespace G26G

lemma tauB_ge_r7 {z : ℝ} (hz : 0 ≤ z) (n : ℕ) : root8 ((n : ℝ) + 1) ^ 7 ≤ tauB z n := by
  rw [← rpow78_eq (by positivity)]; exact (tauB_ge hz n).1

end G26G


-- ===== Solutions.G26.WinRef =====

/-! ### The alive window (Lemma G.28): dyadic blocks and reference errors -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the dyadic block containing a time of the window -/
lemma dyadic_cover {m t s : ℕ} (hm : 1 ≤ m) (hms : m ≤ s) (hst : s ≤ t) :
    ∃ i ∈ Finset.range (Nat.log 2 (t / m) + 1), 2 ^ i * m ≤ s ∧ s ≤ min (2 ^ (i + 1) * m) t := by
  have hsm : s / m ≠ 0 := (Nat.div_pos hms (by omega)).ne'
  refine ⟨Nat.log 2 (s / m), Finset.mem_range.2 (Nat.lt_succ_of_le
    (Nat.log_mono_right (Nat.div_le_div_right hst))), ?_, le_min ?_ hst⟩
  · calc 2 ^ Nat.log 2 (s / m) * m ≤ s / m * m :=
          Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 hsm)
      _ ≤ s := Nat.div_mul_le_self s m
  · have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (s / m)
    have h2 : s < (s / m + 1) * m := by
      have := Nat.lt_div_mul_add (a := s) (b := m) (by omega)
      linarith
    calc s ≤ (s / m + 1) * m := h2.le
      _ ≤ 2 ^ (Nat.log 2 (s / m) + 1) * m := Nat.mul_le_mul_right _ h1

lemma dyadic_start_le {m t i : ℕ} (hm : 1 ≤ m) (hmt : m ≤ t)
    (hi : i ∈ Finset.range (Nat.log 2 (t / m) + 1)) : 2 ^ i * m ≤ t := by
  have hi' : i ≤ Nat.log 2 (t / m) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hpos : 0 < t / m := Nat.div_pos hmt (by omega)
  calc 2 ^ i * m ≤ 2 ^ Nat.log 2 (t / m) * m :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hi')
    _ ≤ t / m * m := Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 hpos.ne')
    _ ≤ t := Nat.div_mul_le_self t m

/-- the union over the window is bounded by the sum over dyadic blocks -/
lemma dyadic_union (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω) {m t : ℕ} (hm : 1 ≤ m) :
    μ.real {ω | ∃ s, m ≤ s ∧ s ≤ t ∧ ω ∈ E s} ≤
      ∑ i ∈ Finset.range (Nat.log 2 (t / m) + 1),
        μ.real {ω | ∃ s, 2 ^ i * m ≤ s ∧ s ≤ min (2 ^ (i + 1) * m) t ∧ ω ∈ E s} := by
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
  rintro ω ⟨s, hms, hst, hE⟩
  obtain ⟨i, hi, h1, h2⟩ := dyadic_cover hm hms hst
  exact Set.mem_biUnion hi ⟨s, h1, h2, hE⟩

lemma geom16 (n : ℕ) : ∑ i ∈ Finset.range n, (1 / 16 : ℝ) ^ i ≤ 16 / 15 := by
  rw [geom_sum_eq (by norm_num)]
  have : (0 : ℝ) ≤ (1 / 16) ^ n := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

lemma Dexpr_nonneg (d : ℕ) {sig c0 : ℝ} (hs : 0 < sig) (hc0 : 0 ≤ c0) : 0 ≤ Dexpr d sig c0 := by
  obtain ⟨hk2, -, -, -, hB⟩ := kk_facts d
  have hB' : 2 ^ 20 * (4 * (kk d : ℝ)) ≤ gB d := by exact_mod_cast hB
  have hBp := G2R.gB_pos (d := d)
  have hHn : 0 ≤ Hneg (kk d) (16 * d + 1) (gB d) := by
    unfold Hneg Kneg
    have := vneg_lt (kk d) hk2 (gB d) hB'
    exact div_nonneg (by positivity) (by linarith)
  have hcK := cK_nonneg d
  have hsi : 0 ≤ sig⁻¹ := inv_nonneg.2 hs.le
  unfold Dexpr
  positivity

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

lemma Dref_nonneg : 0 ≤ H.Dref he :=
  Dexpr_nonneg d H.sig_pos (by have := H.D0_nonneg he; positivity)

/-- **reference errors in the window**: the probability of a non-strict reference somewhere in
`[m, t]` is `O(((nC+1)^4 + 1)/(m+1)^4)` -/
theorem ref_window (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R) {nC : ℕ} (hnC1 : 1 ≤ nC) (hCn : C ≤ nC) {m t : ℕ}
    (hmt : m ≤ t) (htT : t < T) (hmS : 2 * H.Sref he + 2 ≤ m)
    (hmH : 2 ^ 21 * (((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1))) ≤ (m : ℝ) + 1) :
    P.real {ω | ∃ s, m ≤ s ∧ s ≤ t ∧ ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)} ≤
      300 * H.Dref he * ((((nC : ℝ) + 1) ^ 4 + 1) / ((m : ℝ) + 1) ^ 4) := by
  have hm : 1 ≤ m := by omega
  have hD := H.Dref_nonneg he
  refine (dyadic_union P (fun s => {ω | ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)}) hm).trans ?_
  have hblock : ∀ i ∈ Finset.range (Nat.log 2 (t / m) + 1),
      P.real {ω | ∃ s, 2 ^ i * m ≤ s ∧ s ≤ min (2 ^ (i + 1) * m) t ∧
        ω ∈ {ω | ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)}} ≤
      H.Dref he * ((((nC : ℝ) + 1) ^ 4 + 1) * (256 / ((m : ℝ) + 1) ^ 4) * (1 / 16 : ℝ) ^ i) := by
    intro i hi
    have hst := dyadic_start_le hm hmt hi
    set b := min (2 ^ (i + 1) * m) t with hb
    set u := (b + 1) / 2 with hu
    have hbt : b ≤ t := min_le_right _ _
    have hb1 : b ≤ 2 ^ (i + 1) * m := min_le_left _ _
    have hbs : 2 ^ i * m ≤ b := le_min (by rw [pow_succ]; nlinarith [Nat.one_le_two_pow (n := i)]) hst
    have hub : u ≤ 2 ^ i * m := by
      rw [hu, Nat.div_le_iff_le_mul_add_pred (by norm_num)]
      rw [pow_succ] at hb1; nlinarith
    have hb2u : b ≤ 2 * u := by omega
    have h2uT : 2 * u ≤ T := by omega
    have hu2 : 2 ^ i * m ≤ 2 * u + 1 := by omega
    -- thresholds at `u`
    have hmu : m ≤ 2 * u + 1 := le_trans (Nat.le_mul_of_pos_left m (by positivity)) hu2
    have hSu : H.Sref he ≤ u := by omega
    have hlog : 0 ≤ ((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1)) := by
      have : 1 ≤ Real.exp 1 * ((nC : ℝ) + 1) := by
        have := Real.add_one_le_exp (1 : ℝ)
        nlinarith [(Nat.cast_nonneg nC : (0 : ℝ) ≤ nC)]
      exact mul_nonneg (by positivity) (Real.log_nonneg this)
    have hmu' : (m : ℝ) + 1 ≤ 2 * ((u : ℝ) + 1) := by
      have : ((m : ℕ) : ℝ) ≤ 2 * (u : ℝ) + 1 := by exact_mod_cast hmu
      linarith
    have huC : 2 ^ 20 * (((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1))) ≤ (u : ℝ) + 1 := by
      nlinarith
    have hrb := H.ref_block he hR hC hcor hnC1 hCn h2uT hSu huC
    have hsub : {ω | ∃ s, 2 ^ i * m ≤ s ∧ s ≤ b ∧
        ω ∈ {ω | ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)}} ⊆
        {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)} := by
      rintro ω ⟨s, h1, h2, h3⟩
      exact ⟨s, hub.trans h1, h2.trans hb2u, h3⟩
    refine (measureReal_mono hsub).trans (hrb.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hD
    -- `u + 1 ≥ 2^i (m+1) / 4`
    have hu4 : (2 : ℝ) ^ i * ((m : ℝ) + 1) ≤ 4 * ((u : ℝ) + 1) := by
      have h1 : ((2 ^ i * m : ℕ) : ℝ) ≤ 2 * (u : ℝ) + 1 := by exact_mod_cast hu2
      push_cast at h1
      have h2 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    have hu0 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
    have hinv : 1 / ((u : ℝ) + 1) ^ 4 ≤ 256 / ((m : ℝ) + 1) ^ 4 * (1 / 16 : ℝ) ^ i := by
      have h16 : (16 : ℝ) ^ i = ((2 : ℝ) ^ i) ^ 4 := by
        rw [← pow_mul, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, mul_comm]
      have e : (256 : ℝ) / ((m : ℝ) + 1) ^ 4 * (1 / 16 : ℝ) ^ i =
          1 / ((2 : ℝ) ^ i * ((m : ℝ) + 1) / 4) ^ 4 := by
        rw [_root_.one_div_pow, h16]
        field_simp
        ring
      rw [e]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 4)
    have e2 : (((nC : ℝ) + 1) / ((u : ℝ) + 1)) ^ 4 + 1 / ((u : ℝ) + 1) ^ 4 =
        (((nC : ℝ) + 1) ^ 4 + 1) * (1 / ((u : ℝ) + 1) ^ 4) := by
      rw [div_pow]; ring
    rw [e2, mul_assoc]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hg := geom16 (Nat.log 2 (t / m) + 1)
  have hX : 0 ≤ (((nC : ℝ) + 1) ^ 4 + 1) * (256 / ((m : ℝ) + 1) ^ 4) := by positivity
  calc H.Dref he * ((((nC : ℝ) + 1) ^ 4 + 1) * (256 / ((m : ℝ) + 1) ^ 4) *
        ∑ i ∈ Finset.range (Nat.log 2 (t / m) + 1), (1 / 16 : ℝ) ^ i)
      ≤ H.Dref he * ((((nC : ℝ) + 1) ^ 4 + 1) * (256 / ((m : ℝ) + 1) ^ 4) * (16 / 15)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hX) hD
    _ ≤ 300 * H.Dref he * ((((nC : ℝ) + 1) ^ 4 + 1) / ((m : ℝ) + 1) ^ 4) := by
        rw [div_eq_mul_one_div (((nC : ℝ) + 1) ^ 4 + 1), div_eq_mul_one_div (256 : ℝ)]
        have : 0 ≤ (((nC : ℝ) + 1) ^ 4 + 1) * (1 / ((m : ℝ) + 1) ^ 4) := by positivity
        nlinarith

end Sharp

end G26G


-- ===== Solutions.G26.WinCross =====

/-! ### The alive window (Lemma G.28): normalized crossings over dyadic blocks -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma Hneg_kb_nonneg : 0 ≤ Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) := by
  obtain ⟨hk2, -, -, -, hB⟩ := kk_facts d
  have hB' : 2 ^ 20 * (4 * (kk d : ℝ)) ≤ gB d := by exact_mod_cast hB
  have hBp := G2R.gB_pos (d := d)
  have : 0 ≤ H.kb := by linarith [H.kb_ge.1]
  unfold Hneg Kneg
  have := vneg_lt (kk d) hk2 (gB d) hB'
  exact div_nonneg (by positivity) (by linarith)

omit he in
lemma cX1_nonneg : 0 ≤ H.cX1 := by
  have := cK_nonneg d; have := H.Lam1_pos; unfold cX1; positivity

omit he in
lemma cXB_nonneg : 0 ≤ H.cXB := by
  have := H.Hneg_kb_nonneg; unfold cXB; positivity

end Sharp

end G26G


-- ===== Solutions.G26.WinMom =====

/-! ### The alive window (Lemma G.28): local per-point moments of the compensated variable -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma thr_win {n : ℕ} {z l kb : ℝ} (hz : 0 ≤ z) (hl : 0 ≤ l) (hkb : 0 ≤ kb)
    (hr : cTw d l kb ≤ root8 ((n : ℝ) + 1)) :
    gB d * (gbeta d (n + 1) * l + 2 * l + 2) ≤ tauB z n ∧
    40 * (((4 * kk d : ℕ) : ℝ) + 1) * (kb * gbeta d (n + 1)) * ((n : ℝ) + 1) ≤ tauB z n ^ 2 ∧
    10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1)) / tauB z n ≤ 1 ∧
    ((4 * kk d : ℕ) : ℝ) + 1 ≤ tauB z n ∧ ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
  set r := root8 ((n : ℝ) + 1)
  have hP0 : (0 : ℝ) ≤ ((4 * kk d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hB0 := G2R.gB_pos (d := d)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have t1 : 0 ≤ gB d * (l * (16 * d + 3) + 2) := by positivity
  have t2 : 0 ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) := by positivity
  have t3 : 0 ≤ 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) := by positivity
  have hc1 : 1 ≤ cTw d l kb := by unfold cTw; linarith
  have hr1 : 1 ≤ r := hc1.trans hr
  have hr8 : r ^ 8 = (n : ℝ) + 1 := root8_pow (by positivity)
  have hsq : Real.sqrt (((n + 1 : ℕ) : ℝ)) = r ^ 4 := by
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]; exact sqrt_eq_root8 (by positivity)
  have hg : gbeta d (n + 1) ≤ (16 * d + 1) * r ^ 4 := by
    unfold gbeta; rw [hsq]
    have : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr1
    nlinarith
  have hg0 : 0 ≤ gbeta d (n + 1) := by unfold gbeta; positivity
  have hτ := tauB_ge_r7 hz n
  have hr4 : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr1
  have hr47 : r ^ 5 ≤ r ^ 7 := pow_le_pow_right₀ hr1 (by norm_num)
  have h5 : r ^ 4 * r = r ^ 5 := by ring
  -- the pieces of the threshold
  have hc_a : gB d * (l * (16 * d + 3) + 2) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_b : 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_c : 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_d : ((4 * kk d : ℕ) : ℝ) + 1 ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the buffer dominates the update magnitude
    have h1 : gbeta d (n + 1) * l + 2 * l + 2 ≤ (l * (16 * d + 3) + 2) * r ^ 4 := by
      have := mul_le_mul_of_nonneg_left hg hl
      nlinarith [mul_nonneg hl hd0]
    calc gB d * (gbeta d (n + 1) * l + 2 * l + 2) ≤ gB d * ((l * (16 * d + 3) + 2) * r ^ 4) :=
          mul_le_mul_of_nonneg_left h1 hB0.le
      _ = gB d * (l * (16 * d + 3) + 2) * r ^ 4 := by ring
      _ ≤ r * r ^ 4 := mul_le_mul_of_nonneg_right hc_a (by positivity)
      _ = r ^ 5 := by ring
      _ ≤ tauB z n := hr47.trans hτ
  · have h7 : r ^ 14 ≤ tauB z n ^ 2 := by
      rw [show 14 = 7 * 2 by norm_num, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hτ 2
    have hP1 : 0 ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb := by positivity
    calc 40 * (((4 * kk d : ℕ) : ℝ) + 1) * (kb * gbeta d (n + 1)) * ((n : ℝ) + 1)
        = 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * gbeta d (n + 1) * r ^ 8 := by rw [hr8]; ring
      _ ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * ((16 * d + 1) * r ^ 4) * r ^ 8 := by gcongr
      _ = 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) * r ^ 12 := by ring
      _ ≤ r * r ^ 12 := mul_le_mul_of_nonneg_right hc_b (by positivity)
      _ = r ^ 13 := by ring
      _ ≤ r ^ 14 := pow_le_pow_right₀ hr1 (by norm_num)
      _ ≤ tauB z n ^ 2 := h7
  · have hτ0 : 0 < tauB z n := tauB_pos hz n
    rw [div_le_one hτ0]
    calc 10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1))
        ≤ 10 * ((4 * kk d : ℕ) : ℝ) * kb * ((16 * d + 1) * r ^ 4) := by
          have : 10 * (((4 * kk d : ℕ) : ℝ) - 1) ≤ 10 * ((4 * kk d : ℕ) : ℝ) := by linarith
          calc 10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1))
              ≤ 10 * ((4 * kk d : ℕ) : ℝ) * (kb * gbeta d (n + 1)) :=
                mul_le_mul_of_nonneg_right this (mul_nonneg hkb hg0)
            _ ≤ 10 * ((4 * kk d : ℕ) : ℝ) * (kb * ((16 * d + 1) * r ^ 4)) := by gcongr
            _ = _ := by ring
      _ = 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) * r ^ 4 := by ring
      _ ≤ r * r ^ 4 := mul_le_mul_of_nonneg_right hc_c (by positivity)
      _ = r ^ 5 := by ring
      _ ≤ tauB z n := hr47.trans hτ
  · calc ((4 * kk d : ℕ) : ℝ) + 1 ≤ r := hc_d
      _ ≤ r ^ 7 := le_self_pow₀ hr1 (by norm_num)
      _ ≤ tauB z n := hτ
  · have : r ≤ r ^ 8 := le_self_pow₀ hr1 (by norm_num)
    rw [hr8] at this; linarith

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma cTw_ge (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hr : cTw d H.sig⁻¹ H.kb ≤ root8 ((n : ℝ) + 1)) :
    gB d * (gbeta d (n + 1) * H.sig⁻¹ + 2 * H.sig⁻¹ + 2) ≤ tauB z n :=
  (thr_win hz (inv_nonneg.2 H.sig_pos.le) (by linarith [H.kb_ge.1]) hr).1

omit he in
lemma cTw_mono {m n : ℕ} (hmn : m ≤ n) (hr : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) :
    cTw d H.sig⁻¹ H.kb ≤ root8 ((n : ℝ) + 1) :=
  hr.trans (root8_mono (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
                           linarith))

omit he in
/-- the compensated scalar interface on the window -/
theorem win_SI (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hcor : IsCorruptedG P 𝒜 θ C T R) {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) {z : ℝ}
    (hz : 0 ≤ z) {m t : ℕ} (ht : t ≤ T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) :
    SI P (Fx R T) (YN R θ H.sig⁻¹ C (tauB z) u)
      (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m) m t (tauB z)
      (fun n => H.kb * gbeta d (n + 1)) (gB d) :=
  H.runN_SI he hR hcor (H.UT_sub_DT hu) (fun n => tauB_pos hz n) tauB_mono (tauB_delta z) ht
    (fun n hn => H.cTw_ge n hz (H.cTw_mono hn hmc))

end Sharp

end G26G


-- ===== Solutions.G26.WinContr =====

/-! ### Lemma G.26: the contraction step on the projective body -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the compensated direction vector: `YN(u) = u ⬝ᵥ Vc + (lC + 2τ)` -/
noncomputable def Vc (R : GRun d Ω) (θ : Fin d → ℝ) (n : ℕ) (ω : Ω) : Fin d → ℝ :=
  R.cumEst n ω - ∑ j ∈ Finset.range n, (R.θs j ω - θ)

lemma YN_eq (θ : Fin d → ℝ) (l C : ℝ) (τ : ℕ → ℝ) (u : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    YN R θ l C τ u n ω = u ⬝ᵥ Vc R θ n ω + (l * C + 2 * τ n) := by
  unfold YN Vc Ecor
  rw [dotProduct_sub, dotProduct_sum]; ring

lemma Vc_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (θ : Fin d → ℝ) {n : ℕ} (hn : n ≤ T) :
    Measurable (Vc R θ n) := by
  unfold Vc
  refine (((cumEst_Fx hR hn).mono (Fx_le hR hn) le_rfl)).sub (Finset.measurable_sum _ fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  exact (hR j (by omega)).1.2.2.2.1.sub measurable_const

lemma Agood_meas (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (θ : Fin d → ℝ) (C : ℝ) : MeasurableSet (Agood 𝒜 R θ C T) := by
  have e : Agood 𝒜 R θ C T = ⋂ n ∈ Finset.range (T + 1),
      {ω | 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C} := by
    ext ω; simp only [Agood, mem_setOf_eq, mem_iInter, Finset.mem_range]
    exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩
  rw [e]
  refine Finset.measurableSet_biInter _ fun n hn => ?_
  have hm := (Acum_Fx h𝒜 hne hR θ (n := n) (by have := Finset.mem_range.1 hn; omega)).mono
    (Fx_le hR (by have := Finset.mem_range.1 hn; omega)) le_rfl
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

lemma Agood_ae (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) {θ : Fin d → ℝ} {C : ℝ}
    (hcor : IsCorruptedG P 𝒜 θ C T R) : ∀ᵐ ω ∂P, ω ∈ Agood 𝒜 R θ C T :=
  Acum_le h𝒜 hne hcor

/-- the algebra of the contraction bound -/
lemma contr_alg {P r d : ℕ} (hrd : r ≤ d) (hdP : 2 * d ≤ P) {L cK τ t1 : ℝ} (hL : 0 ≤ L)
    (hcK : 0 ≤ cK) (hτ : 0 < τ) (hτt : τ ≤ t1) :
    (2 * L) ^ P * cK * t1 ^ P / (7 * t1 ^ 2 / τ) ^ P +
      (2 * (7 * τ)) ^ P * (7 * t1 ^ 2 / τ / (7 * τ)) ^ r * (4 / t1) ^ P ≤
      ((2 * L / 7) ^ P * cK + 56 ^ P) * (τ / t1) ^ (P - 2 * d) := by
  have ht : 0 < t1 := by linarith
  set y := τ / t1 with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := (div_le_one ht).2 hτt
  have e1 : (2 * L) ^ P * cK * t1 ^ P / (7 * t1 ^ 2 / τ) ^ P = (2 * L / 7) ^ P * cK * y ^ P := by
    have hin : 2 * L * t1 / (7 * t1 ^ 2 / τ) = 2 * L / 7 * y := by rw [hy]; field_simp
    calc (2 * L) ^ P * cK * t1 ^ P / (7 * t1 ^ 2 / τ) ^ P
        = cK * (2 * L * t1 / (7 * t1 ^ 2 / τ)) ^ P := by
          rw [div_pow (2 * L * t1) (7 * t1 ^ 2 / τ), mul_pow (2 * L) t1]; ring
      _ = (2 * L / 7) ^ P * cK * y ^ P := by rw [hin, mul_pow (2 * L / 7) y]; ring
  have e2 : 7 * t1 ^ 2 / τ / (7 * τ) = (y ^ 2)⁻¹ := by rw [hy]; field_simp
  have e3 : (2 * (7 * τ)) ^ P * (4 / t1) ^ P = 56 ^ P * y ^ P := by
    rw [← mul_pow, ← mul_pow, hy]; congr 1; field_simp; ring
  have hyP : y ^ P ≤ y ^ (P - 2 * d) := pow_le_pow_of_le_one hy0.le hy1 (by omega)
  have hinv : ((y ^ 2)⁻¹) ^ r ≤ ((y ^ 2)⁻¹) ^ d :=
    pow_le_pow_right₀ (one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ hy0.le hy1)) hrd
  have key : y ^ P * ((y ^ 2)⁻¹) ^ d = y ^ (P - 2 * d) := by
    rw [show P = (P - 2 * d) + 2 * d by omega, pow_add, inv_pow, ← pow_mul, mul_assoc,
      mul_inv_cancel₀ (by positivity), mul_one]
    congr 1; omega
  rw [e1, e2, mul_comm ((2 * (7 * τ)) ^ P), mul_assoc ((y ^ 2)⁻¹ ^ r), e3]
  have h2 : ((y ^ 2)⁻¹) ^ r * (56 ^ P * y ^ P) ≤ 56 ^ P * y ^ (P - 2 * d) := by
    calc ((y ^ 2)⁻¹) ^ r * (56 ^ P * y ^ P) ≤ ((y ^ 2)⁻¹) ^ d * (56 ^ P * y ^ P) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = 56 ^ P * (y ^ P * ((y ^ 2)⁻¹) ^ d) := by ring
      _ = 56 ^ P * y ^ (P - 2 * d) := by rw [key]
  have h1 : (2 * L / 7) ^ P * cK * y ^ P ≤ (2 * L / 7) ^ P * cK * y ^ (P - 2 * d) :=
    mul_le_mul_of_nonneg_left hyP (by positivity)
  nlinarith

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma cCo_nonneg : 0 ≤ H.cCo := by
  have := cK_nonneg d; have := H.Lam1_pos; unfold cCo; positivity

omit he in
lemma Bad_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (C z : ℝ) {t : ℕ} (ht : t ≤ T) :
    MeasurableSet (Bad ℬ 𝒜 R θ astar H.sig⁻¹ C z t) := by
  have hS := (cumEst_Fx hR ht).mono (Fx_le hR ht) le_rfl
  have hc : Measurable (cN 𝒜 R θ H.sig⁻¹ C t) := by
    unfold cN
    exact ((measurable_const.sub ((Acum_Fx H.h𝒜 H.ne𝒜 hR θ ht).mono (Fx_le hR ht) le_rfl)).const_mul
      _).neg
  exact measurableSet_lt measurable_const (negMax_meas H.UT_compact H.UT_ne hS hc)

omit he in
/-- **the contraction step (G.528)–(G.532)** -/
theorem win_contr (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t)
    (htT : t < T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1))
    (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1) (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1)
    (hmz : (m : ℝ) + 1 ≤ z) (hτt : tauB z t ≤ (t : ℝ) + 1) :
    P.real (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t ∩ Agood 𝒜 R θ C T ∩
        Bad ℬ 𝒜 R θ astar H.sig⁻¹ C z t) ≤
      H.cCo * (tauB z t / ((t : ℝ) + 1)) ^ (4 * kk d - 2 * d) := by
  set l := H.sig⁻¹ with hl
  have hl0 : 0 ≤ l := inv_nonneg.2 H.sig_pos.le
  set τ := tauB z t with hτ
  have hτ0 : 0 < τ := tauB_pos hz t
  have hτ4 : 4 * z ≤ τ := (tauB_ge hz t).2.1
  have hlCτ : 3 * (l * C) ≤ τ := by linarith
  have hlC0 : 0 ≤ l * C := mul_nonneg hl0 hC
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  set E := IN 𝒜 ℬ e (js ℬ e astar) R θ astar l C (tauB z) m t ∩ Agood 𝒜 R θ C T ∩
    Bad ℬ 𝒜 R θ astar l C z t with hE
  have hTt : t ≤ T := htT.le
  have hEm : MeasurableSet E :=
    ((Fx_le hR hTt _ (H.IN_meas he hR C (tauB z) m hTt)).inter
      (Agood_meas H.h𝒜 H.ne𝒜 hR θ C)).inter (H.Bad_meas hR C z hTt)
  have hSm : Measurable (R.cumEst t) := (cumEst_Fx hR hTt).mono (Fx_le hR hTt) le_rfl
  set RX := fun ω => absMax (Kset ℬ) (R.cumEst t ω) (-(astar ⬝ᵥ R.cumEst t ω)) with hRX
  have hRXm : Measurable RX := absMax_meas H.Kc ⟨astar, H.haK⟩ hSm
    ((G2R.meas_dot' measurable_const hSm).neg)
  have hRX0 : ∀ ω, 0 ≤ RX ω := fun ω =>
    (abs_nonneg _).trans (abs_le_absMax H.Kc H.haK (R.cumEst t ω) (-(astar ⬝ᵥ R.cumEst t ω)))
  have hL0 := H.Lam1_pos
  set b := fun ω => Lam1 ℬ θ astar * RX ω + (2 * (l * C) + 2 * τ) with hb
  have hbm : Measurable b := (hRXm.const_mul _).add measurable_const
  -- the pointwise facts on `E`
  have hdot : ∀ ω (x : Fin d → ℝ), x ∈ UT ℬ θ astar → |x ⬝ᵥ R.cumEst t ω| ≤ Lam1 ℬ θ astar * RX ω := by
    intro ω x hx
    have hM : ∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ R.cumEst t ω| ≤ RX ω := by
      intro a ha
      have := abs_le_absMax H.Kc ha (R.cumEst t ω) (-(astar ⬝ᵥ R.cumEst t ω))
      rwa [sub_dotProduct, sub_eq_add_neg]
    exact H.Lam1_spec hM (H.UT_sub_DT hx)
  have hlow : ∀ ω ∈ E, ∀ x ∈ UT ℬ θ astar, τ ≤ x ⬝ᵥ Vc R θ t ω + (l * C + 2 * τ) := by
    intro ω hω x hx
    obtain ⟨⟨hI, hA⟩, -⟩ := hω
    have := (H.YN_low (H.UT_sub_DT hx) (hA t hTt).1 (hA t hTt).2 (hI.2 t hmt le_rfl)).1
    rwa [YN_eq] at this
  have hpos : ∀ ω ∈ E, ∀ x ∈ UT ℬ θ astar, 0 < x ⬝ᵥ Vc R θ t ω + (l * C + 2 * τ) :=
    fun ω hω x hx => lt_of_lt_of_le hτ0 (hlow ω hω x hx)
  have hmin : ∀ ω ∈ E, ∃ x0 ∈ UT ℬ θ astar, x0 ⬝ᵥ Vc R θ t ω + (l * C + 2 * τ) ≤ 7 * τ := by
    intro ω hω
    obtain ⟨⟨hI, hA⟩, hB⟩ := hω
    obtain ⟨u0, hu0, heq⟩ := negMax_mem H.UT_compact H.UT_ne (R.cumEst t ω) (cN 𝒜 R θ l C t ω)
    refine ⟨u0, hu0, ?_⟩
    have hB' : -(4 * τ) < negMax (UT ℬ θ astar) (R.cumEst t ω) (cN 𝒜 R θ l C t ω) := hB
    rw [← heq] at hB'
    rw [← YN_eq]
    have hEc := H.EcorN_le (H.UT_sub_DT hu0) (R := R) t ω
    obtain ⟨hA0, hAC⟩ := hA t hTt
    unfold YN
    unfold cN at hB'
    have e1 : l * (C - Acum 𝒜 R θ t ω) = l * C - l * Acum 𝒜 R θ t ω := by ring
    have := neg_abs_le (Ecor R θ u0 t ω)
    have : l * Acum 𝒜 R θ t ω ≤ l * C := mul_le_mul_of_nonneg_left hAC hl0
    linarith
  have hmax : ∀ ω ∈ E, ∀ x ∈ UT ℬ θ astar, x ⬝ᵥ Vc R θ t ω + (l * C + 2 * τ) ≤ b ω := by
    intro ω hω x hx
    obtain ⟨⟨-, hA⟩, -⟩ := hω
    rw [← YN_eq]
    have hEc := H.EcorN_le (H.UT_sub_DT hx) (R := R) t ω
    obtain ⟨hA0, hAC⟩ := hA t hTt
    have h1 := hdot ω x hx
    unfold YN
    have := le_abs_self (x ⬝ᵥ R.cumEst t ω)
    have := neg_abs_le (Ecor R θ x t ω)
    have : l * Acum 𝒜 R θ t ω ≤ l * C := mul_le_mul_of_nonneg_left hAC hl0
    simp only [hb]
    linarith
  have hρ : 7 * τ ≤ 7 * ((t : ℝ) + 1) ^ 2 / τ := by
    rw [le_div_iff₀ hτ0]; nlinarith
  have hinv : ∀ x ∈ UT ℬ θ astar, ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal
      ((|x ⬝ᵥ Vc R θ t ω + (l * C + 2 * τ)| ^ (4 * kk d))⁻¹)) ω ∂P ≤
      ENNReal.ofReal ((4 / ((t : ℝ) + 1)) ^ (4 * kk d)) := by
    intro x hx
    have Sx := H.win_SI he hR hcor hx hz (t := t) hTt hmc
    have hk := H.win_inv he hR hcor hx hz hmt htT hmc hmhalf
    have hint := Sx.kinv_int hmt le_rfl (4 * kk d)
    have h0 : 0 ≤ᵐ[P] (IN 𝒜 ℬ e (js ℬ e astar) R θ astar l C (tauB z) m t).indicator
        (fun ω => (YN R θ l C (tauB z) x t ω)⁻¹ ^ (4 * kk d)) := by
      filter_upwards [Sx.low t hmt le_rfl] with ω hω
      by_cases hI : ω ∈ IN 𝒜 ℬ e (js ℬ e astar) R θ astar l C (tauB z) m t
      · rw [indicator_of_mem hI]
        exact pow_nonneg (inv_nonneg.2 ((tauB_pos hz t).le.trans (hω hI))) _
      · rw [indicator_of_notMem hI]; exact le_rfl
    calc ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal
          ((|x ⬝ᵥ Vc R θ t ω + (l * C + 2 * τ)| ^ (4 * kk d))⁻¹)) ω ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal ((IN 𝒜 ℬ e (js ℬ e astar) R θ astar l C (tauB z) m t).indicator
            (fun ω => (YN R θ l C (tauB z) x t ω)⁻¹ ^ (4 * kk d)) ω) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hωE : ω ∈ E
          · rw [indicator_of_mem hωE, indicator_of_mem hωE.1.1, YN_eq]
            have hp := hpos ω hωE x hx
            rw [abs_of_pos hp, inv_pow]
          · rw [indicator_of_notMem hωE]; exact bot_le
      _ = ENNReal.ofReal (kinv P (YN R θ l C (tauB z) x)
            (IN 𝒜 ℬ e (js ℬ e astar) R θ astar l C (tauB z) m) (4 * kk d) t) :=
          (ofReal_integral_eq_lintegral_ofReal hint h0).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hk
  have hcs := contr_split H.UT_compact H.UT_convex H.UT_ne (μ := P) (Vc_meas hR θ hTt)
    (measurable_const (a := l * C + 2 * τ)) hEm (a := 7 * τ) (by positivity) hbm (4 * kk d)
    hpos hmin hmax hρ (by positivity) hinv
  -- the tail of `b`
  have hb_tail : P.real {ω | 7 * ((t : ℝ) + 1) ^ 2 / τ < b ω} ≤
      (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * cK d * ((t : ℝ) + 1) ^ (4 * kk d) /
        (7 * ((t : ℝ) + 1) ^ 2 / τ) ^ (4 * kk d) := by
    set ρ := 7 * ((t : ℝ) + 1) ^ 2 / τ with hρdef
    have hρ0 : 0 < ρ := by positivity
    have IK := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
    have hK := H.absK_env hR (A := fun _ => univ) (fun _ _ => MeasurableSet.univ) hTt
    simp only [frz_univ] at hK
    have hint := IK.absMax_int hTt (4 * kk d)
    have hc2 : (0 : ℝ) < (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d) := by positivity
    have hm := markov' (Filter.Eventually.of_forall fun ω => pow_nonneg (hRX0 ω) (4 * kk d)) hint
      (c := (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d)) hc2
    have hsub : {ω | ρ < b ω} ⊆ {ω | (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d) ≤ RX ω ^ (4 * kk d)} := by
      intro ω hω
      have hω' : ρ < Lam1 ℬ θ astar * RX ω + (2 * (l * C) + 2 * τ) := hω
      show (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d) ≤ RX ω ^ (4 * kk d)
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    refine (measureReal_mono hsub).trans (hm.trans ?_)
    rw [div_pow, div_div_eq_mul_div]
    have : (0 : ℝ) < ρ ^ (4 * kk d) := pow_pos hρ0 _
    refine div_le_div_of_nonneg_right ?_ this.le
    calc (∫ ω, RX ω ^ (4 * kk d) ∂P) * (2 * Lam1 ℬ θ astar) ^ (4 * kk d)
        ≤ (cK d * ((t : ℝ) + 1) ^ (4 * kk d)) * (2 * Lam1 ℬ θ astar) ^ (4 * kk d) :=
          mul_le_mul_of_nonneg_right hK (by positivity)
      _ = (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * cK d * ((t : ℝ) + 1) ^ (4 * kk d) := by ring
  have hdP : 2 * d ≤ 4 * kk d := by have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
                                    rw [hkk]; omega
  have halg := contr_alg (P := 4 * kk d) (r := rdim (UT ℬ θ astar)) (rdim_le _) hdP
    (L := Lam1 ℬ θ astar) (cK := cK d) (τ := τ) (t1 := (t : ℝ) + 1) hL0.le (cK_nonneg d) hτ0 hτt
  refine hcs.trans ?_
  unfold cCo
  linarith

end Sharp

end G26G


-- ===== Solutions.G26.WinFail =====

/-! ### Lemma G.26: the failure probability of the good event at a fixed round -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
/-- **(G.536)–(G.537)**: the failure probability of the good event, before parameter algebra -/
theorem win_fail (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {nC : ℕ} (hnC1 : 1 ≤ nC) (hCn : C ≤ nC)
    {z : ℝ} (hz : 0 < z) {m t : ℕ} (hm : 1 ≤ m) (hmt : m ≤ t) (htT : t < T)
    (hmS : 2 * H.Sref he + 2 ≤ m)
    (hmH : 2 ^ 21 * (((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1))) ≤ (m : ℝ) + 1)
    (hzx : (((m : ℝ) + 1) / z) ^ 8 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1))
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (htm : ((t : ℝ) + 1) / ((m : ℝ) + 1) ≤ (m : ℝ) + 1)
    (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1))
    (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1) (hmz : (m : ℝ) + 1 ≤ z)
    (hτt : tauB z t ≤ (t : ℝ) + 1) :
    P.real (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t)ᶜ ≤
      300 * H.Dref he * ((((nC : ℝ) + 1) ^ 4 + 1) / ((m : ℝ) + 1) ^ 4) +
      (2 * H.cX1 * (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4 + 18 * H.cXB / ((m : ℝ) + 1) ^ 4) +
      H.cCo * (tauB z t / ((t : ℝ) + 1)) ^ (4 * kk d - 2 * d) := by
  set l := H.sig⁻¹ with hl
  set A1 := {ω | ∃ s, m ≤ s ∧ s ≤ t ∧ ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)} with hA1
  set A2 := {ω | ∃ s, m ≤ s ∧ s ≤ t ∧ ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
    tauB z s < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ l C s ω)} with hA2
  set A3 := IN 𝒜 ℬ e (js ℬ e astar) R θ astar l C (tauB z) m t ∩ Agood 𝒜 R θ C T ∩
    Bad ℬ 𝒜 R θ astar l C z t with hA3
  have hsub : (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar l C z T m t)ᶜ ⊆
      ((A1 ∪ A2) ∪ (Agood 𝒜 R θ C T)ᶜ) ∪ A3 := by
    intro ω hω
    simp only [Gev, mem_compl_iff, mem_inter_iff, not_and, not_not] at hω
    by_cases hI : ω ∈ IN 𝒜 ℬ e (js ℬ e astar) R θ astar l C (tauB z) m t
    · by_cases hAg : ω ∈ Agood 𝒜 R θ C T
      · exact Or.inr ⟨⟨hI, hAg⟩, hω ⟨hI, hAg⟩⟩
      · exact Or.inl (Or.inr hAg)
    · left; left
      simp only [IN, mem_inter_iff, mem_setOf_eq, not_and_or, not_forall, not_le] at hI
      rcases hI with hJ | ⟨j, hj1, hj2, hj3⟩
      · simp only [JN, mem_setOf_eq, not_forall] at hJ
        obtain ⟨j, hj1, hj2, hj3⟩ := hJ
        exact Or.inl ⟨j, hj1, hj2, hj3⟩
      · by_cases hJ : ω ∈ JN ℬ e (js ℬ e astar) R m t
        · exact Or.inr ⟨j, hj1, hj2, fun i hi1 hi2 => hJ i hi1 (hi2.trans hj2), hj3⟩
        · simp only [JN, mem_setOf_eq, not_forall] at hJ
          obtain ⟨i, hi1, hi2, hi3⟩ := hJ
          exact Or.inl ⟨i, hi1, hi2, hi3⟩
  have hAg0 : P.real (Agood 𝒜 R θ C T)ᶜ = 0 := by
    rw [measureReal_eq_zero_iff]
    exact ae_iff.1 (Agood_ae H.h𝒜 H.ne𝒜 hcor)
  have h1 := H.ref_window he hR hC hcor hnC1 hCn hmt htT hmS hmH
  have h2 := H.cross_window he hR hC hcor hz hm hmt htT hzx hlC htm
  have h3 := H.win_contr he hR hC hcor hz.le hmt htT hmc hmhalf hlC hmz hτt
  calc P.real (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar l C z T m t)ᶜ
      ≤ P.real (((A1 ∪ A2) ∪ (Agood 𝒜 R θ C T)ᶜ) ∪ A3) := measureReal_mono hsub
    _ ≤ P.real ((A1 ∪ A2) ∪ (Agood 𝒜 R θ C T)ᶜ) + P.real A3 := measureReal_union_le _ _
    _ ≤ (P.real (A1 ∪ A2) + P.real (Agood 𝒜 R θ C T)ᶜ) + P.real A3 := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ ((P.real A1 + P.real A2) + 0) + P.real A3 := by
        rw [hAg0]; gcongr; exact measureReal_union_le _ _
    _ ≤ _ := by linarith

end Sharp

end G26G


-- ===== Solutions.G26.WinPar =====

/-! ### Lemma G.26: the window parameters and the per-round failure bound -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma log_e_ge {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.log (Real.exp 1 * x) := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  linarith [Real.log_nonneg hx]

lemma Hcf_facts {C : ℝ} (hC : 0 ≤ C) : 1 ≤ nCf C ∧ C ≤ nCf C ∧ (nCf C : ℝ) + 1 ≤ Hcf C ∧ 1 ≤ Hcf C := by
  have h1 : C ≤ (nCf C : ℝ) := by
    unfold nCf; push_cast; linarith [Nat.le_ceil C]
  have hn : (1 : ℝ) ≤ (nCf C : ℝ) + 1 := by linarith [(Nat.cast_nonneg (nCf C) : (0 : ℝ) ≤ _)]
  have hl := log_e_ge hn
  have h3 : (nCf C : ℝ) + 1 ≤ Hcf C := by
    unfold Hcf; nlinarith
  exact ⟨by unfold nCf; omega, h1, h3, by linarith⟩

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

end Sharp

end G26G


-- ===== Solutions.G26.WinSum =====

/-! ### Lemma G.26: the per-round failure bound and the weighted failure sum -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

set_option maxHeartbeats 1000000 in
omit he in
/-- **(G.525), per round**: `P(G_tᶜ) ≤ D (t^{-2} + (H/t)^2)` for `t ≥ t0` -/
theorem win_round (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {t : ℕ} (htT : t < T)
    (ht0 : H.t0f he C ≤ t) :
    P.real (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (zw (mw (H.M0 he) (Hcf C) t) t) T
        (mw (H.M0 he) (Hcf C) t) t)ᶜ ≤
      H.Dθ he * (1 / ((t : ℝ) + 1) ^ 2 + (Hcf C / ((t : ℝ) + 1)) ^ 2) := by
  obtain ⟨hn1, hCn, -, -⟩ := Hcf_facts hC
  obtain ⟨hm, hmt, hmhalf, hmc, hlC, hmS, hmH, hz0, hmz, -, -, hzx, htm, hτt, hy16, hx4, hb1, hb2⟩ :=
    H.win_ok he hC ht0
  set m := mw (H.M0 he) (Hcf C) t with hm_def
  set z := zw m t with hz_def
  have hf := H.win_fail he hR hC hcor hn1 hCn hz0 hm hmt htT hmS hmH hzx hlC htm hmc hmhalf hmz hτt
  refine hf.trans ?_
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  set A := 1 / ((t : ℝ) + 1) ^ 2 with hA
  set h2 := (Hcf C / ((t : ℝ) + 1)) ^ 2 with hh2
  set x4 := (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4 with hx4d
  set M := ((H.M0 he : ℝ) + 3) ^ 4 + 1 with hM
  have hA0 : 0 ≤ A := by positivity
  have hh0 : 0 ≤ h2 := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hD := H.Dref_nonneg he
  have hc1 := H.cX1_nonneg
  have hcB := H.cXB_nonneg
  have hcC := H.cCo_nonneg
  -- the contraction term
  have hy0 : 0 ≤ tauB z t / ((t : ℝ) + 1) := div_nonneg (tauB_pos hz0.le t).le ht1.le
  have hy1 : tauB z t / ((t : ℝ) + 1) ≤ 1 := (div_le_one ht1).2 hτt
  have hkd : 16 ≤ 4 * kk d - 2 * d := by
    have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
    rw [hkk]; omega
  have hyP : (tauB z t / ((t : ℝ) + 1)) ^ (4 * kk d - 2 * d) ≤ 2 ^ 16 * (A + 4 ^ 16 * (16 * M * h2)) :=
    calc (tauB z t / ((t : ℝ) + 1)) ^ (4 * kk d - 2 * d) ≤ (tauB z t / ((t : ℝ) + 1)) ^ 16 :=
          pow_le_pow_of_le_one hy0 hy1 hkd
      _ ≤ 2 ^ 16 * (A + 4 ^ 16 * x4) := hy16
      _ ≤ 2 ^ 16 * (A + 4 ^ 16 * (16 * M * h2)) := by gcongr
  have t1 : 300 * H.Dref he * ((((nCf C : ℝ) + 1) ^ 4 + 1) / ((m : ℝ) + 1) ^ 4) ≤
      300 * H.Dref he * (h2 + A) := mul_le_mul_of_nonneg_left hb1 (by positivity)
  have t2 : 2 * H.cX1 * x4 ≤ 2 * H.cX1 * (16 * M * h2) := mul_le_mul_of_nonneg_left hx4 (by positivity)
  have t3 : 18 * H.cXB / ((m : ℝ) + 1) ^ 4 ≤ 18 * H.cXB * A := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hb2 (by positivity)
  have t4 : H.cCo * (tauB z t / ((t : ℝ) + 1)) ^ (4 * kk d - 2 * d) ≤
      H.cCo * (2 ^ 16 * (A + 4 ^ 16 * (16 * M * h2))) := mul_le_mul_of_nonneg_left hyP hcC
  have hDθ : H.Dθ he = 300 * H.Dref he + 32 * H.cX1 * M + 18 * H.cXB +
      2 ^ 16 * H.cCo * (1 + 16 * 4 ^ 16 * M) := rfl
  rw [hDθ]
  have p1 : 0 ≤ 300 * H.Dref he * h2 := by positivity
  have p2 : 0 ≤ 32 * H.cX1 * M * A := by positivity
  have p3 : 0 ≤ 18 * H.cXB * h2 := by positivity
  have p4 : 0 ≤ 2 ^ 16 * H.cCo * (16 * 4 ^ 16 * M) * A := by positivity
  have p5 : 0 ≤ 2 ^ 16 * H.cCo * h2 := by positivity
  nlinarith [t1, t2, t3, t4, p1, p2, p3, p4, p5]

end Sharp

end G26G


theorem _root_.solution : type_of% @G26G.Sharp.win_round := @G26G.Sharp.win_round
