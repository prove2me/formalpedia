-- Prove2me | solution 1 for G26G.Sharp.cross_window
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:36:32.905201+00:00
-- url     : https://prove2.me/submissions/e533dcd1-3b73-4647-b9aa-c2a75dd1adda

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_G26_FI_absMax_env
import Theorems.Thm_G26_FI_cross_env
import Theorems.Thm_G26G_Sharp_runN_FI
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


-- ===== Solutions.G2.Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

lemma Kset_compact {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

/-! #### Runs -/

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma feas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsFeasible3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) :=
  ((hR t ht).2.1.2 ω).1

lemma p_supp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    R.p t ω (Kset ℬ)ᶜ = 0 :=
  (feas hR ht ω).2.1

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

end

section Ineq

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

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


-- ===== Solutions.G26.Step =====

/-! ### The killed one-step expectation tool, pointwise and integrated over a body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : ℕ → MeasurableSpace Ω} {n : ℕ}

lemma int_of_ae_bdd {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {c : ℝ}
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ c) : Integrable f μ :=
  Integrable.of_bound hf c (by filter_upwards [h] with ω hω; rwa [Real.norm_eq_abs])

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

lemma FI.Vm' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) : Measurable (V n) :=
  (I.Vm n hn).mono (I.Fle n hn) le_rfl

lemma FI.cm' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) : Measurable (c n) :=
  (I.cm n hn).mono (I.Fle n hn) le_rfl

/-- the field at a fixed point is `F_n`-measurable -/
lemma FI.fz_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (u : Fin d → ℝ) :
    Measurable[F n] (fun ω => fz V c n ω u) := by
  unfold fz
  have h : Continuous fun p : (Fin d → ℝ) × ℝ => u ⬝ᵥ p.1 + p.2 := by
    simp only [dotProduct]; fun_prop
  exact h.measurable.comp ((I.Vm n hn).prodMk (I.cm n hn))

/-- joint measurability of the field -/
lemma FI.fz_jmeas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable (Function.uncurry fun (u : Fin d → ℝ) (ω : Ω) => fz V c n ω u) := by
  unfold fz Function.uncurry
  have h : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ p.2.1 + p.2.2 := by
    simp only [dotProduct]; fun_prop
  exact h.measurable.comp (measurable_fst.prodMk (((I.Vm' hn).comp measurable_snd).prodMk
    ((I.cm' hn).comp measurable_snd)))

lemma FI.negMax_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable[F n] (fun ω => negMax D (V n ω) (c n ω)) :=
  G26.negMax_meas I.hD I.hne (I.Vm n hn) (I.cm n hn)

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


-- ===== Solutions.G26.AbsRec =====

/-! ### The absolute integral moment recurrence (Lemmas G.23, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma cont_bdd_int (hD : IsCompact D) {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) :
    Integrable φ (nvol D) := by
  have : IsFiniteMeasure (nvol D) := by
    unfold nvol; infer_instance
  obtain ⟨Cb, hCb⟩ := hD.exists_bound_of_continuousOn hφ.continuousOn
  refine Integrable.of_bound hφ.aestronglyMeasurable Cb ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
  simp only [Set.mem_compl_iff, not_not] at hx
  exact hCb x hx

omit mΩ in
lemma fz_cont (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun u => fz V c n ω u := by
  unfold fz; simp only [dotProduct]; fun_prop

end

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

omit mΩ in
lemma Ff_nonneg (P : ℕ) (n : ℕ) (ω : Ω) : 0 ≤ Ff D V c P n ω :=
  integral_nonneg fun _ => pow_nonneg (le_max_right _ _) _

lemma FI.Ff_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (P : ℕ) :
    StronglyMeasurable (Ff D V c P n) := by
  have := nvol_prob I.hD I.hconv I.hne
  have h : StronglyMeasurable (fun p : Ω × (Fin d → ℝ) => (max (-fz V c n p.1 p.2) 0) ^ P) := by
    have h0 : Measurable (fun p : (Fin d → ℝ) × Ω => (max (-fz V c n p.2 p.1) 0) ^ P) :=
      ((I.fz_jmeas hn).neg.max (measurable_const (a := (0 : ℝ)))).pow_const P
    exact (h0.comp measurable_swap).stronglyMeasurable
  exact h.integral_prod_right'

/-- `F_n ≤ N_n^P` -/
lemma FI.Ff_le (I : FI D μ F T V c J β B lo hi m0) (P : ℕ) (n : ℕ) (ω : Ω)
    (hN : 0 ≤ negMax D (V n ω) (c n ω)) :
    Ff D V c P n ω ≤ negMax D (V n ω) (c n ω) ^ P := by
  have := nvol_prob I.hD I.hconv I.hne
  have hint := cont_bdd_int I.hD (φ := fun u => (max (-fz V c n ω u) 0) ^ P)
    (((fz_cont V c n ω).neg.max continuous_const).pow P)
  calc Ff D V c P n ω ≤ ∫ _u, negMax D (V n ω) (c n ω) ^ P ∂(nvol D) := by
        refine integral_mono_ae hint (integrable_const _) ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp I.hD)] with u hu
        simp only [Set.mem_compl_iff, not_not] at hu
        refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ hN) _
        exact negMax_ge I.hD hu _ _
    _ = _ := by simp

lemma FI.Ff_bdd [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T)
    (P : ℕ) : ∃ r : ℝ, ∀ᵐ ω ∂μ, |Ff D V c P n ω| ≤ r := by
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine ⟨r ^ P, ?_⟩
  filter_upwards [hr, I.N0 n hn] with ω hω hN
  rw [abs_of_nonneg (Ff_nonneg P n ω)]
  refine (I.Ff_le P n ω hN).trans (pow_le_pow_left₀ hN ?_ _)
  exact (negMax_le_absMax _ _).trans hω.1

lemma FI.Ff_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T)
    (P : ℕ) (S : Set Ω) (hS : MeasurableSet S) : Integrable (S.indicator (Ff D V c P n)) μ := by
  obtain ⟨r, hr⟩ := I.Ff_bdd hn P
  exact (int_of_ae_bdd (I.Ff_meas hn P).aestronglyMeasurable hr).indicator hS

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


-- ===== Solutions.G26.Cross =====

/-! ### Block maxima of negative maxima by freezing at the first crossing -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.crossA_meas (I : FI D μ F T V c J β B lo hi m0) (v : ℕ) (lam : ℝ) :
    ∀ n ≤ T, MeasurableSet[F n] (crossA D V c J v lam n) := by
  intro n hn
  refine (I.Jm n hn).inter ?_
  by_cases h : n < v
  · simp [h]
  · simp only [h, false_or]
    exact measurableSet_le (I.negMax_meas hn) measurable_const

/-- the field frozen at the first crossing still satisfies the interface, without killing -/
lemma FI.cross_FI [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) (hlo : lo ≤ 0)
    (hhi : 0 ≤ hi) (hβ : ∀ n, 0 ≤ β n) (hB : 0 < B) (v : ℕ) (lam : ℝ) :
    FI D μ F T (frz V (crossA D V c J v lam)) (frz c (crossA D V c J v lam)) (fun _ => univ)
      β B lo hi m0 :=
  I.freeze (I.crossA_meas v lam) hlo hhi hβ hB (fun _ _ => MeasurableSet.univ)
    (fun _ => subset_rfl) (fun n ω hω => by
      have h1 : ω ∈ crossA D V c J v lam n := by
        have := hω.1
        simp only [survS, Set.mem_iInter, Finset.mem_range] at this
        exact this n (by omega)
      exact h1.1)

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

lemma cumEst_succ (n : ℕ) (ω : Ω) : R.cumEst (n + 1) ω = R.cumEst n ω + R.thetaHat n ω := by
  simp [GRun.cumEst, Finset.sum_range_succ]

end G26R


-- ===== Solutions.G26.RunW =====

/-! ### The remaining-budget shifted field on `K` (Lemma G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ}

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

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

lemma sig_pos : 0 < H.sig := (Classical.choose_spec H.hsharp).1

lemma sig_spec {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) :
    H.sig * sNorm ℬ (a - astar) ≤ gap θ astar a := by
  have h := (Classical.choose_spec H.hsharp).2 a (by rw [G1L.Kset_gen H.hgen]; exact ha)
  rw [G1L.sNorm_gen H.hgen] at h
  exact h

lemma norm_le (x : Fin d → ℝ) : ‖x‖ ≤ sNorm ℬ x := by
  rw [← G1L.sNorm_gen H.hgen]; exact T31.norm_le_sNorm H.ne𝒜 H.hspan H.hball x

lemma gap_pos {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (hne : a ≠ astar) : 0 < gap θ astar a := by
  have h1 : 0 < ‖a - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h2 := H.norm_le (a - astar)
  exact lt_of_lt_of_le (mul_pos H.sig_pos (lt_of_lt_of_le h1 h2)) (H.sig_spec ha)

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

lemma U0_bdd : U0 ℬ θ astar ⊆ Metric.closedBall 0 H.sig⁻¹ := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (H.norm_le u).trans (H.U0_sNorm hu)

lemma UT_compact : IsCompact (UT ℬ θ astar) :=
  (isCompact_closedBall (0 : Fin d → ℝ) H.sig⁻¹).of_isClosed_subset isClosed_closure
    (closure_minimal H.U0_bdd Metric.isClosed_closedBall)

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

lemma DT_mem {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) :
    ∃ l ∈ Icc (0 : ℝ) 1, ∃ u ∈ UT ℬ θ astar, w = l • u := by
  obtain ⟨⟨l, u⟩, ⟨hl, hu⟩, rfl⟩ := hw
  exact ⟨l, hl, u, hu, rfl⟩

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

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma gbeta_ge16 (n : ℕ) : 16 ≤ gbeta d (n + 1) := by
  unfold gbeta; have : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ); linarith

end Sharp

end G26G


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


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma rdim_le (D : Set (Fin d → ℝ)) : rdim D ≤ d := by
  unfold rdim
  have := Submodule.finrank_le (vectorSpan ℝ D)
  simpa using this

lemma absMax_le_of_forall {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hne : D.Nonempty)
    {V : Fin d → ℝ} {c r : ℝ} (h : ∀ u ∈ D, |u ⬝ᵥ V + c| ≤ r) : absMax D V c ≤ r := by
  obtain ⟨u, hu, he, -⟩ := absMax_mem hD hne V c
  rw [← he]; exact h u hu

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

lemma tauB_mono' {z : ℝ} {s t : ℕ} (h : s ≤ t) : tauB z s ≤ tauB z t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact ih.trans (tauB_mono t)

lemma tauB_ge {z : ℝ} (hz : 0 ≤ z) (s : ℕ) :
    ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ tauB z s ∧ 4 * z ≤ tauB z s ∧ 1 ≤ tauB z s := by
  unfold tauB
  have h1 := p78_ge_one (x := (s : ℝ) + 1) (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine ⟨by linarith, ?_, by linarith⟩
  have : 0 ≤ ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) := by positivity
  linarith

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

lemma le_root8 {x a : ℝ} (ha : 0 ≤ a) (h : a ^ 8 ≤ x) : a ≤ root8 x := by
  have hx : 0 ≤ x := le_trans (by positivity) h
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt (root8_nonneg x) (by norm_num : (8 : ℕ) ≠ 0)
  rw [root8_pow hx] at this
  linarith

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

lemma one_le_root8 {x : ℝ} (hx : 1 ≤ x) : 1 ≤ root8 x :=
  le_root8 zero_le_one (by simpa using hx)

end G26G


-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma measureReal_le_of_ae {μ : Measure Ω} [IsFiniteMeasure μ] {s t : Set Ω}
    (h : ∀ᵐ ω ∂μ, ω ∈ s → ω ∈ t) : μ.real s ≤ μ.real t := by
  have h0 : μ {ω | ¬ (ω ∈ s → ω ∈ t)} = 0 := ae_iff.1 h
  have h0' : μ.real {ω | ¬ (ω ∈ s → ω ∈ t)} = 0 := by
    rw [Measure.real, h0, ENNReal.toReal_zero]
  calc μ.real s ≤ μ.real (t ∪ {ω | ¬ (ω ∈ s → ω ∈ t)}) := by
        refine measureReal_mono fun ω hω => ?_
        by_cases ht : ω ∈ t
        · exact Or.inl ht
        · exact Or.inr fun h => ht (h hω)
    _ ≤ μ.real t + μ.real {ω | ¬ (ω ∈ s → ω ∈ t)} := measureReal_union_le _ _
    _ = μ.real t := by rw [h0', add_zero]

lemma add_pow_le_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  rcases le_total x y with h | h
  · have h1 : (x + y) ^ n ≤ (2 * y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ x ^ n := pow_nonneg hx n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have h1 : (x + y) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ y ^ n := pow_nonneg hy n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]

lemma markov' {μ : Measure Ω} {g : Ω → ℝ} (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω) (hgi : Integrable g μ) {c : ℝ}
    (hc : 0 < c) : μ.real {ω | c ≤ g ω} ≤ (∫ ω, g ω ∂μ) / c := by
  have := mul_meas_ge_le_integral_of_nonneg hg0 hgi c
  rw [le_div_iff₀ hc]; linarith

lemma gbeta_sq (d n : ℕ) : gbeta d (n + 1) ^ 2 ≤ (16 * (d : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) := by
  unfold gbeta
  rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
  have h1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have h2 : 16 * (d : ℝ) + Real.sqrt ((n : ℝ) + 1) ≤ (16 * d + 1) * Real.sqrt ((n : ℝ) + 1) := by
    have : (0 : ℝ) ≤ 16 * d := by positivity
    nlinarith
  have h3 := pow_le_pow_left₀ (by positivity) h2 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h3
  exact h3

lemma hW_d (d : ℕ) : 1 + 1024 * (4 * (kk d : ℝ)) ^ 2 / gB d ≤ ((d + 2 : ℕ) : ℝ) := by
  unfold kk gB
  push_cast
  rw [show (1024 : ℝ) * (4 * (1024 * ((d : ℝ) + 1))) ^ 2 / (2 ^ 36 * ((d : ℝ) + 1)) = ((d : ℝ) + 1) / 4 by
    field_simp; ring]
  linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]

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

lemma alg_B2 {d k m0 u : ℕ} {lam Hn Rr : ℝ} (hlam : root8 ((m0 : ℝ) + 1) ^ 7 ≤ lam)
    (hu : (u : ℝ) + 1 ≤ 4 * ((m0 : ℝ) + 1)) (hkd : 8 * d + 32 ≤ 4 * k) (hR0 : 0 ≤ Rr)
    (hRu : Rr ≤ (u : ℝ) + 1) (hHn : 0 ≤ Hn) :
    2 ^ (4 * k) * 4 ^ d * Rr ^ d / lam ^ (4 * k) * (Hn * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k)) ≤
      2 ^ (4 * k) * 4 ^ d * Hn * 4 ^ d * 8 ^ (3 * k) * 256 / ((u : ℝ) + 1) ^ 4 := by
  set r := root8 ((m0 : ℝ) + 1)
  have hr1 : 1 ≤ r := one_le_root8 (by linarith [(Nat.cast_nonneg m0 : (0:ℝ) ≤ m0)])
  have hr8 : r ^ 8 = (m0 : ℝ) + 1 := root8_pow (by positivity)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have e1 : r ^ (8 * d) = ((m0 : ℝ) + 1) ^ d := by rw [pow_mul r 8 d, hr8]
  have e2 : r ^ (24 * k) = ((m0 : ℝ) + 1) ^ (3 * k) := by
    rw [show 24 * k = 8 * (3 * k) by ring, pow_mul r 8 (3 * k), hr8]
  have e3 : r ^ 32 = ((m0 : ℝ) + 1) ^ 4 := by rw [show 32 = 8 * 4 by ring, pow_mul r 8 4, hr8]
  have h1 : Rr ^ d ≤ 4 ^ d * r ^ (8 * d) := by
    rw [e1, ← mul_pow]; exact pow_le_pow_left₀ hR0 (by linarith) d
  have h2 : (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) ≤ 8 ^ (3 * k) * r ^ (24 * k) := by
    rw [e2, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
  have h3 : ((u : ℝ) + 1) ^ 4 ≤ 256 * r ^ 32 := by
    rw [e3]
    have := pow_le_pow_left₀ hu1.le hu 4
    rw [mul_pow] at this; norm_num at this; linarith
  have h4 : r ^ (8 * d) * r ^ (24 * k) * r ^ 32 ≤ r ^ (28 * k) := by
    rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hr1 (by omega)
  have h5 : r ^ (28 * k) ≤ lam ^ (4 * k) := by
    rw [show 28 * k = 7 * (4 * k) by ring, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hlam _
  have key : Rr ^ d * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) * ((u : ℝ) + 1) ^ 4 ≤
      4 ^ d * 8 ^ (3 * k) * 256 * lam ^ (4 * k) := by
    calc Rr ^ d * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) * ((u : ℝ) + 1) ^ 4
        ≤ (4 ^ d * r ^ (8 * d)) * (8 ^ (3 * k) * r ^ (24 * k)) * (256 * r ^ 32) := by
          gcongr
      _ = 4 ^ d * 8 ^ (3 * k) * 256 * (r ^ (8 * d) * r ^ (24 * k) * r ^ 32) := by ring
      _ ≤ 4 ^ d * 8 ^ (3 * k) * 256 * lam ^ (4 * k) := by gcongr; exact h4.trans h5
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : (0 : ℝ) ≤ 2 ^ (4 * k) * 4 ^ d * Hn := by positivity
  calc 2 ^ (4 * k) * 4 ^ d * Rr ^ d * (Hn * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k)) * ((u : ℝ) + 1) ^ 4
      = (2 ^ (4 * k) * 4 ^ d * Hn) *
          (Rr ^ d * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * k) * ((u : ℝ) + 1) ^ 4) := by ring
    _ ≤ (2 ^ (4 * k) * 4 ^ d * Hn) * (4 ^ d * 8 ^ (3 * k) * 256 * lam ^ (4 * k)) :=
        mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

end G26G


-- ===== Solutions.G26.Window =====

/-! ### The alive window (Lemma G.28): normalized crossings on a block -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- the comparison of the normalized field with the raw loss-difference field -/
lemma absN_le {S : Fin d → ℝ} {Ac C : ℝ} (hA0 : 0 ≤ Ac) (hAC : Ac ≤ C) :
    absMax (DT ℬ θ astar) S (-(H.sig⁻¹ * (C - Ac))) ≤
      Lam1 ℬ θ astar * absMax (Kset ℬ) S (-(astar ⬝ᵥ S)) + H.sig⁻¹ * C := by
  have hl : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  refine absMax_le_of_forall H.DT_compact H.DT_ne fun u hu => ?_
  have hM : ∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ S| ≤ absMax (Kset ℬ) S (-(astar ⬝ᵥ S)) := by
    intro a ha
    have := abs_le_absMax H.Kc ha S (-(astar ⬝ᵥ S))
    rwa [sub_dotProduct, sub_eq_add_neg]
  have h1 := H.Lam1_spec hM hu
  have h2 : |-(H.sig⁻¹ * (C - Ac))| ≤ H.sig⁻¹ * C := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg hl (by linarith))]
    exact mul_le_mul_of_nonneg_left (by linarith) hl
  exact (abs_add_le _ _).trans (by linarith)

omit he in
/-- **normalized crossing on a block**: after reference identification at `m`, the probability that
the normalized negative maximum crosses `τ v` somewhere in `[v, N]` -/
theorem win_cross (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {m v N : ℕ} (hmN : m ≤ N) (hN : N ≤ T)
    {lam ρ : ℝ} (hlam : 1 ≤ lam) (hlρ : lam ≤ ρ) (hρC : 2 * (H.sig⁻¹ * C) ≤ ρ) :
    P.real {ω | ∃ s, v ≤ s ∧ s ≤ N ∧ ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
        lam < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)} ≤
      (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * cK d * ((N : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) +
      2 ^ (4 * kk d) * 4 ^ d * (ρ / lam) ^ d / lam ^ (4 * kk d) *
        (Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) * ((N : ℝ) + 1) ^ (3 * kk d) +
          (((N : ℝ) + 1) / ((m : ℝ) + 1)) ^ (d + 2) *
            (2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * cK d * ((m : ℝ) + 1) ^ (4 * kk d) +
              (H.sig⁻¹ * C) ^ (4 * kk d)))) := by
  obtain ⟨hk2, hP4, hev, hdP, hB⟩ := kk_facts d
  have hB0 := G2R.gB_pos (d := d)
  have hl : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  have hL0 := H.Lam1_pos
  have hβ0 : ∀ n, 0 ≤ gbeta d (n + 1) := fun n => (G2R.gbeta_pos H.hd (n + 1)).le
  have hkb := H.kb_ge
  have hβN0 : ∀ n, 0 ≤ H.kb * gbeta d (n + 1) := fun n => mul_nonneg (by linarith) (hβ0 n)
  have I := H.runN_FI he hR hC hcor m
  have IK := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
  set A := crossA (DT ℬ θ astar) R.cumEst (cN 𝒜 R θ H.sig⁻¹ C) (JN ℬ e (js ℬ e astar) R m) v lam
    with hAdef
  have hAm : ∀ n ≤ T, MeasurableSet[Fx R T n] (A n) := I.crossA_meas v lam
  have IKf := IK.freeze hAm (by norm_num) (by norm_num) hβ0 hB0 (J' := fun _ => univ)
    (fun _ _ => MeasurableSet.univ) (fun _ => subset_rfl) (fun _ => subset_univ _)
  have hρ0 : 0 < ρ := by linarith
  -- comparison of the frozen normalized field with the frozen raw field
  have hcmp : ∀ n, ∀ᵐ ω ∂P, n ≤ T →
      absMax (DT ℬ θ astar) (frz R.cumEst A n ω) (frz (cN 𝒜 R θ H.sig⁻¹ C) A n ω) ≤
        Lam1 ℬ θ astar * absMax (Kset ℬ) (frz R.cumEst A n ω)
          (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A n ω) + H.sig⁻¹ * C := by
    intro n
    filter_upwards [Acum_le H.h𝒜 H.ne𝒜 hcor] with ω hA hn
    obtain ⟨e1, hi, -, -⟩ := frz_fidx R.cumEst A n ω
    obtain ⟨e2, -, -, -⟩ := frz_fidx (cN 𝒜 R θ H.sig⁻¹ C) A n ω
    obtain ⟨e3, -, -, -⟩ := frz_fidx (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A n ω
    rw [e1, e2, e3]
    obtain ⟨hA0, hAC⟩ := hA (fidx A n ω) (hi.trans hn)
    exact H.absN_le he hA0 hAC
  -- the tail of the frozen absolute maximum
  have hpA : P.real {ω | ρ < absMax (DT ℬ θ astar) (frz R.cumEst A N ω)
      (frz (cN 𝒜 R θ H.sig⁻¹ C) A N ω)} ≤
      (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * cK d * ((N : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) := by
    have hK := H.absK_env hR hAm hN
    have hint := IKf.absMax_int hN (4 * kk d)
    have h0 : ∀ᵐ ω ∂P, 0 ≤ absMax (Kset ℬ) (frz R.cumEst A N ω)
        (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A N ω) ^ (4 * kk d) := by
      filter_upwards [IKf.N0 N hN] with ω h
      exact pow_nonneg (h.trans (negMax_le_absMax _ _)) _
    have hc2 : (0 : ℝ) < (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d) := pow_pos (by positivity) _
    have hm := markov' h0 hint (c := (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d)) hc2
    have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ρ < absMax (DT ℬ θ astar) (frz R.cumEst A N ω)
        (frz (cN 𝒜 R θ H.sig⁻¹ C) A N ω)} → ω ∈ {ω | (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d) ≤
        absMax (Kset ℬ) (frz R.cumEst A N ω)
          (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A N ω) ^ (4 * kk d)} := by
      filter_upwards [hcmp N] with ω h hω
      have h' := h hN
      have hω' : ρ < absMax (DT ℬ θ astar) (frz R.cumEst A N ω)
        (frz (cN 𝒜 R θ H.sig⁻¹ C) A N ω) := hω
      show (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d) ≤ absMax (Kset ℬ) (frz R.cumEst A N ω)
        (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A N ω) ^ (4 * kk d)
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    refine (measureReal_le_of_ae hsub).trans (hm.trans ?_)
    have e : (ρ / (2 * Lam1 ℬ θ astar)) ^ (4 * kk d) = ρ ^ (4 * kk d) / (2 * Lam1 ℬ θ astar) ^ (4 * kk d) :=
      div_pow ρ _ _
    rw [e, div_div_eq_mul_div]
    have h2p : (0 : ℝ) < (2 * Lam1 ℬ θ astar) ^ (4 * kk d) := pow_pos (by positivity) _
    have : (0 : ℝ) < ρ ^ (4 * kk d) := pow_pos hρ0 _
    refine div_le_div_of_nonneg_right ?_ this.le
    calc (∫ ω, absMax (Kset ℬ) (frz R.cumEst A N ω)
          (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A N ω) ^ (4 * kk d) ∂P) *
            (2 * Lam1 ℬ θ astar) ^ (4 * kk d)
        = (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * ∫ ω, absMax (Kset ℬ) (frz R.cumEst A N ω)
          (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A N ω) ^ (4 * kk d) ∂P := mul_comm _ _
      _ ≤ (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * (cK d * ((N : ℝ) + 1) ^ (4 * kk d)) :=
          mul_le_mul_of_nonneg_left hK h2p.le
      _ = (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * cK d * ((N : ℝ) + 1) ^ (4 * kk d) := (mul_assoc _ _ _).symm
  -- the initial negative integral at `m`
  have I' := I.cross_FI le_rfl (by linarith) hβN0 hB0 v lam
  have hF0 : ∫ ω, Ff (DT ℬ θ astar) (frz R.cumEst A) (frz (cN 𝒜 R θ H.sig⁻¹ C) A) (4 * kk d) m ω ∂P ≤
      2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * cK d * ((m : ℝ) + 1) ^ (4 * kk d) +
        (H.sig⁻¹ * C) ^ (4 * kk d)) := by
    have hmT : m ≤ T := hmN.trans hN
    have hK := H.absK_env hR hAm hmT
    have hintK := IKf.absMax_int hmT (4 * kk d)
    have hFi : Integrable (Ff (DT ℬ θ astar) (frz R.cumEst A) (frz (cN 𝒜 R θ H.sig⁻¹ C) A)
        (4 * kk d) m) P := by
      have := I'.Ff_int hmT (4 * kk d) univ MeasurableSet.univ; simpa using this
    calc ∫ ω, Ff (DT ℬ θ astar) (frz R.cumEst A) (frz (cN 𝒜 R θ H.sig⁻¹ C) A) (4 * kk d) m ω ∂P
        ≤ ∫ ω, 2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * absMax (Kset ℬ) (frz R.cumEst A m ω)
            (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A m ω) ^ (4 * kk d) +
              (H.sig⁻¹ * C) ^ (4 * kk d)) ∂P := by
          refine integral_mono_ae hFi
            (((hintK.const_mul _).add (integrable_const _)).const_mul _) ?_
          filter_upwards [hcmp m, I'.N0 m hmT, IKf.N0 m hmT] with ω h hN0 hK0
          have h' := h hmT
          refine (I'.Ff_le (4 * kk d) m ω hN0).trans ?_
          have h1 := negMax_le_absMax (D := DT ℬ θ astar) (frz R.cumEst A m ω)
            (frz (cN 𝒜 R θ H.sig⁻¹ C) A m ω)
          have hR0 := hK0.trans (negMax_le_absMax _ _)
          calc negMax (DT ℬ θ astar) (frz R.cumEst A m ω) (frz (cN 𝒜 R θ H.sig⁻¹ C) A m ω) ^ (4 * kk d)
              ≤ (Lam1 ℬ θ astar * absMax (Kset ℬ) (frz R.cumEst A m ω)
                  (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A m ω) + H.sig⁻¹ * C) ^ (4 * kk d) :=
                pow_le_pow_left₀ hN0 (h1.trans h') _
            _ ≤ 2 ^ (4 * kk d) * ((Lam1 ℬ θ astar * absMax (Kset ℬ) (frz R.cumEst A m ω)
                  (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A m ω)) ^ (4 * kk d) +
                    (H.sig⁻¹ * C) ^ (4 * kk d)) :=
                add_pow_le_two (by positivity) (by positivity) _
            _ = _ := by rw [mul_pow]
      _ = 2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * ∫ ω, absMax (Kset ℬ) (frz R.cumEst A m ω)
            (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A m ω) ^ (4 * kk d) ∂P +
              (H.sig⁻¹ * C) ^ (4 * kk d)) := by
          rw [integral_const_mul, integral_add (hintK.const_mul _) (integrable_const _),
            integral_const, integral_const_mul]
          simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (by positivity)
          calc Lam1 ℬ θ astar ^ (4 * kk d) * ∫ ω, absMax (Kset ℬ) (frz R.cumEst A m ω)
                (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A m ω) ^ (4 * kk d) ∂P
              ≤ Lam1 ℬ θ astar ^ (4 * kk d) * (cK d * ((m : ℝ) + 1) ^ (4 * kk d)) :=
                mul_le_mul_of_nonneg_left hK (by positivity)
            _ = _ := (mul_assoc _ _ _).symm
  have hB' : 2 ^ 20 * (4 * (kk d : ℝ)) ≤ gB d := by exact_mod_cast hB
  have hbeta : ∀ n, (H.kb * gbeta d (n + 1)) ^ 2 ≤ (H.kb * (16 * d + 1)) ^ 2 * ((n : ℝ) + 1) := by
    intro n
    rw [mul_pow, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (gbeta_sq d n) (by positivity)
  have hc := I.cross_env (by linarith) hk2 ((rdim_le _).trans hdP) hB' (b := H.kb * (16 * d + 1))
    (mul_nonneg (by linarith) (by positivity)) (fun n => by nlinarith [H.gbeta_ge16 n]) hbeta
    (W := d + 2) (hW_d d) (v := v) (N := N) (m := m) le_rfl hmN hN hlam hlρ hpA hF0
  refine hc.trans ?_
  have hrat : 1 ≤ ρ / lam := by rw [le_div_iff₀ (by linarith)]; linarith
  have h4 : (4 : ℝ) ^ rdim (DT ℬ θ astar) * (ρ / lam) ^ rdim (DT ℬ θ astar) ≤ 4 ^ d * (ρ / lam) ^ d :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) (rdim_le _))
      (pow_le_pow_right₀ hrat (rdim_le _)) (by positivity) (by positivity)
  have hHn : 0 ≤ Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) := by
    unfold Hneg Kneg
    have := vneg_lt (kk d) hk2 (gB d) hB'
    have : 0 ≤ H.kb := by linarith
    exact div_nonneg (by positivity) (by linarith)
  have hcK := cK_nonneg d
  have hX : 0 ≤ Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) * ((N : ℝ) + 1) ^ (3 * kk d) +
      (((N : ℝ) + 1) / ((m : ℝ) + 1)) ^ (d + 2) *
        (2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * cK d * ((m : ℝ) + 1) ^ (4 * kk d) +
          (H.sig⁻¹ * C) ^ (4 * kk d))) := by positivity
  have hτp : 0 < lam ^ (4 * kk d) := pow_pos (by linarith) _
  have h5 : 2 ^ (4 * kk d) * 4 ^ rdim (DT ℬ θ astar) * (ρ / lam) ^ rdim (DT ℬ θ astar) /
      lam ^ (4 * kk d) ≤ 2 ^ (4 * kk d) * 4 ^ d * (ρ / lam) ^ d / lam ^ (4 * kk d) := by
    refine div_le_div_of_nonneg_right ?_ hτp.le
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have := mul_le_mul_of_nonneg_right h5 hX
  linarith

end Sharp

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

lemma dyadic_count {m t : ℕ} (hm : 1 ≤ m) (hmt : m ≤ t) :
    ((Nat.log 2 (t / m) + 1 : ℕ) : ℝ) ≤ 2 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) := by
  have hpos : 0 < t / m := Nat.div_pos hmt (by omega)
  have h1 : Nat.log 2 (t / m) + 1 ≤ 2 ^ Nat.log 2 (t / m) := Nat.lt_two_pow_self
  have h2 := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 ^ Nat.log 2 (t / m) : ℕ) * m ≤ t :=
    (Nat.mul_le_mul_right _ h2).trans (Nat.div_mul_le_self t m)
  have h1' : ((Nat.log 2 (t / m) + 1 : ℕ) : ℝ) ≤ ((2 ^ Nat.log 2 (t / m) : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h3' : ((2 ^ Nat.log 2 (t / m) : ℕ) : ℝ) * (m : ℝ) ≤ t := by exact_mod_cast h3
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 ≤ ((2 ^ Nat.log 2 (t / m) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith

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

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

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

lemma cw_A {P q : ℕ} (hPq : P = 8 * q) {L cK N1 t1 m1 lam z x : ℝ} (hL : 0 ≤ L) (hcK : 0 ≤ cK)
    (hN1 : 0 ≤ N1) (hNt : N1 ≤ t1) (hm1 : 0 < m1) (ht1 : 0 < t1) (hz : 0 < z) (hlz : 4 * z ≤ lam)
    (hzx : (m1 / z) ^ 8 ≤ x) :
    (2 * L) ^ P * cK * N1 ^ P / (lam * (t1 / m1)) ^ P ≤ (L / 2) ^ P * cK * x ^ q := by
  have hlam : 0 < lam := by linarith
  have hw0 : 0 ≤ N1 / (lam * (t1 / m1)) := by positivity
  have hw : N1 / (lam * (t1 / m1)) ≤ m1 / (4 * z) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : N1 * (4 * z) ≤ t1 * lam := by nlinarith
    calc N1 * (4 * z) = N1 * (4 * z) * m1 / m1 := by field_simp
      _ ≤ t1 * lam * m1 / m1 := by gcongr
      _ = m1 * (lam * (t1 / m1)) := by field_simp
  have hmz0 : 0 ≤ (m1 / z) ^ 8 := by positivity
  calc (2 * L) ^ P * cK * N1 ^ P / (lam * (t1 / m1)) ^ P
      = (2 * L) ^ P * cK * (N1 / (lam * (t1 / m1))) ^ P := by rw [div_pow]; ring
    _ ≤ (2 * L) ^ P * cK * (m1 / (4 * z)) ^ P := by gcongr
    _ = (2 * L * (m1 / (4 * z))) ^ P * cK := by rw [mul_pow (2 * L) (m1 / (4 * z))]; ring
    _ = (L / 2) ^ P * (m1 / z) ^ P * cK := by
        rw [show 2 * L * (m1 / (4 * z)) = L / 2 * (m1 / z) by field_simp; ring, mul_pow]
    _ = (L / 2) ^ P * cK * ((m1 / z) ^ 8) ^ q := by rw [← pow_mul, ← hPq]; ring
    _ ≤ (L / 2) ^ P * cK * x ^ q := by gcongr

lemma cw_C {P q d : ℕ} (hPq : P = 8 * q) (hq : 2 * d + 2 ≤ q) {L cK l C N1 t1 m1 lam z x : ℝ}
    (hL : 0 ≤ L) (hcK : 0 ≤ cK) (hl : 0 ≤ l) (hC0 : 0 ≤ C) (hlC : l * C ≤ m1) (hN1 : 0 ≤ N1)
    (hNt : N1 ≤ t1) (hm1 : 0 < m1) (hmt : m1 ≤ t1) (hz : 0 < z) (hlz : 4 * z ≤ lam)
    (hzx : (m1 / z) ^ 8 ≤ x) (hx : x = m1 / t1) :
    2 ^ P * 4 ^ d * (lam * (t1 / m1) / lam) ^ d / lam ^ P *
        ((N1 / m1) ^ (d + 2) * (2 ^ P * (L ^ P * cK * m1 ^ P + (l * C) ^ P))) ≤
      4 ^ d * (L ^ P * cK + 1) * x ^ (q - 2 * d - 2) := by
  have hlam : 0 < lam := by linarith
  have ht1 : 0 < t1 := by linarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have e1 : lam * (t1 / m1) / lam = t1 / m1 := by field_simp
  rw [e1]
  have hN : (N1 / m1) ^ (d + 2) ≤ (t1 / m1) ^ (d + 2) := by gcongr
  have hlC' : (l * C) ^ P ≤ m1 ^ P := pow_le_pow_left₀ (by positivity) hlC P
  have hF : L ^ P * cK * m1 ^ P + (l * C) ^ P ≤ (L ^ P * cK + 1) * m1 ^ P := by nlinarith
  have hml : m1 ^ P / lam ^ P ≤ x ^ q / 4 ^ P := by
    rw [← div_pow]
    have h1 : m1 / lam ≤ m1 / (4 * z) := div_le_div_of_nonneg_left hm1.le (by positivity) hlz
    have h2 : (m1 / (4 * z)) ^ P = ((m1 / z) ^ 8) ^ q / 4 ^ P := by
      rw [← pow_mul, ← hPq, div_mul_eq_div_div, div_pow, div_pow, div_pow]; ring
    calc (m1 / lam) ^ P ≤ (m1 / (4 * z)) ^ P := pow_le_pow_left₀ (by positivity) h1 P
      _ = ((m1 / z) ^ 8) ^ q / 4 ^ P := h2
      _ ≤ x ^ q / 4 ^ P := by gcongr
  have key : x ^ q * ((t1 / m1) ^ d * (t1 / m1) ^ (d + 2)) = x ^ (q - 2 * d - 2) := by
    have hxt : x * (t1 / m1) = 1 := by rw [hx]; field_simp
    rw [← pow_add, show q = (q - 2 * d - 2) + (d + (d + 2)) by omega, pow_add, mul_assoc, ← mul_pow,
      hxt, one_pow, mul_one]
    congr 1; omega
  have h2P : (2 : ℝ) ^ P * 2 ^ P = 4 ^ P := by rw [← mul_pow]; norm_num
  have h4P : (0 : ℝ) < 4 ^ P := by positivity
  calc 2 ^ P * 4 ^ d * (t1 / m1) ^ d / lam ^ P *
        ((N1 / m1) ^ (d + 2) * (2 ^ P * (L ^ P * cK * m1 ^ P + (l * C) ^ P)))
      ≤ 2 ^ P * 4 ^ d * (t1 / m1) ^ d / lam ^ P *
        ((t1 / m1) ^ (d + 2) * (2 ^ P * ((L ^ P * cK + 1) * m1 ^ P))) := by gcongr
    _ = 4 ^ d * (L ^ P * cK + 1) * ((2 ^ P * 2 ^ P) * (m1 ^ P / lam ^ P)) *
          ((t1 / m1) ^ d * (t1 / m1) ^ (d + 2)) := by ring
    _ ≤ 4 ^ d * (L ^ P * cK + 1) * ((2 ^ P * 2 ^ P) * (x ^ q / 4 ^ P)) *
          ((t1 / m1) ^ d * (t1 / m1) ^ (d + 2)) := by gcongr
    _ = 4 ^ d * (L ^ P * cK + 1) * (x ^ q * ((t1 / m1) ^ d * (t1 / m1) ^ (d + 2))) := by
        rw [h2P, mul_div_cancel₀ _ h4P.ne']; ring
    _ = 4 ^ d * (L ^ P * cK + 1) * x ^ (q - 2 * d - 2) := by rw [key]

lemma cw_sum {c1 cB x m1 : ℝ} {n : ℕ} (hc1 : 0 ≤ c1) (hcB : 0 ≤ cB) (hx0 : 0 ≤ x) (hm1 : 0 < m1)
    {a : ℕ → ℝ} (hab : ∀ i ∈ Finset.range n, a i ≤ c1 * x + cB * (16 / m1 ^ 4 * (1 / 16) ^ i)) :
    ∑ i ∈ Finset.range n, a i ≤ n * (c1 * x) + 18 * cB / m1 ^ 4 := by
  refine (Finset.sum_le_sum hab).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hg := geom16 n
  have h1 : cB * (16 / m1 ^ 4 * ∑ i ∈ Finset.range n, (1 / 16 : ℝ) ^ i) ≤ cB * (16 / m1 ^ 4 * (16 / 15)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by positivity)) hcB
  have h2 : cB * (16 / m1 ^ 4 * (16 / 15)) ≤ 18 * cB / m1 ^ 4 := by
    rw [show cB * (16 / m1 ^ 4 * (16 / 15)) = (256 / 15) * cB / m1 ^ 4 by ring]
    gcongr; norm_num
  linarith

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

omit he in
/-- **one dyadic block of normalized crossings** -/
theorem cross_block (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {m t i : ℕ} {z : ℝ} (hz0 : 0 < z)
    (hm : 1 ≤ m) (hmt : m ≤ t) (htT : t < T) (hi : i ∈ Finset.range (Nat.log 2 (t / m) + 1))
    (hzx : (((m : ℝ) + 1) / z) ^ 8 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1))
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (htm : ((t : ℝ) + 1) / ((m : ℝ) + 1) ≤ (m : ℝ) + 1) :
    P.real {ω | ∃ s, 2 ^ i * m ≤ s ∧ s ≤ min (2 ^ (i + 1) * m) t ∧
        ω ∈ {ω | ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
          tauB z s < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)}} ≤
      H.cX1 * (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ (512 * (d + 1) - 2 * d - 2) +
        H.cXB * (16 / ((m : ℝ) + 1) ^ 4 * (1 / 16) ^ i) := by
  have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
  have hkq : 4 * kk d = 8 * (512 * (d + 1)) := by rw [hkk]; ring
  have hq : 2 * d + 2 ≤ 512 * (d + 1) := by omega
  have hkB2 : 8 * d + 32 ≤ 4 * kk d := by rw [hkk]; omega
  have hst := dyadic_start_le hm hmt hi
  set v := 2 ^ i * m with hv
  set b := min (2 ^ (i + 1) * m) t with hb
  have hbt : b ≤ t := min_le_right _ _
  have hb1 : b ≤ 2 * v := by rw [hv, ← mul_assoc, ← pow_succ']; exact min_le_left _ _
  have hvb : v ≤ b := le_min (by rw [hv, pow_succ]; nlinarith [Nat.one_le_two_pow (n := i)]) hst
  have hmv : m ≤ v := Nat.le_mul_of_pos_left m (by positivity)
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hmt' : (m : ℝ) + 1 ≤ (t : ℝ) + 1 := by linarith [(by exact_mod_cast hmt : (m : ℝ) ≤ t)]
  have hx1 : ((m : ℝ) + 1) / ((t : ℝ) + 1) ≤ 1 := (div_le_one ht1).2 hmt'
  have hx0 : 0 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1) := by positivity
  have hmz : (m : ℝ) + 1 ≤ z := by
    have h1 : (((m : ℝ) + 1) / z) ^ 8 ≤ 1 := hzx.trans hx1
    have h2 : ((m : ℝ) + 1) / z ≤ 1 := by
      by_contra hc; push_neg at hc
      have := one_lt_pow₀ hc (by norm_num : (8 : ℕ) ≠ 0); linarith
    rwa [div_le_one hz0] at h2
  set lam := tauB z v with hlam
  have hlam4 : 4 * z ≤ lam := (tauB_ge hz0.le v).2.1
  have hlam1 : 1 ≤ lam := (tauB_ge hz0.le v).2.2
  have hlam0 : 0 < lam := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ, lam * (((t : ℝ) + 1) / ((m : ℝ) + 1)) = ρ := ⟨_, rfl⟩
  have hrat : 1 ≤ ((t : ℝ) + 1) / ((m : ℝ) + 1) := by rw [le_div_iff₀ hm1]; linarith
  have hlρ : lam ≤ ρ := hρ ▸ le_mul_of_one_le_right hlam0.le hrat
  have hl0 : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  have hρC : 2 * (H.sig⁻¹ * C) ≤ ρ := by linarith
  have hwc := H.win_cross he hR hC hcor (m := m) (v := v) (N := b) (hmv.trans hvb) (by omega)
    hlam1 hlρ hρC
  have hsub : {ω | ∃ s, v ≤ s ∧ s ≤ b ∧
      ω ∈ {ω | ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
        tauB z s < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)}} ⊆
      {ω | ∃ s, v ≤ s ∧ s ≤ b ∧ ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
        lam < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)} := by
    rintro ω ⟨s, h1, h2, h3, h4⟩
    exact ⟨s, h1, h2, h3, lt_of_le_of_lt (tauB_mono' h1) h4⟩
  refine (measureReal_mono hsub).trans (hwc.trans ?_)
  -- the three terms
  have hcK := cK_nonneg d
  have hL0 := H.Lam1_pos
  have hN1 : ((b : ℝ) + 1) ≤ (t : ℝ) + 1 := by linarith [(by exact_mod_cast hbt : (b : ℝ) ≤ t)]
  have hA := cw_A hkq (L := Lam1 ℬ θ astar) (cK := cK d) (N1 := (b : ℝ) + 1) (t1 := (t : ℝ) + 1)
    (m1 := (m : ℝ) + 1) (lam := lam) (z := z) (x := ((m : ℝ) + 1) / ((t : ℝ) + 1)) hL0.le hcK
    (by positivity) hN1 hm1 ht1 hz0 hlam4 hzx
  have hCt := cw_C hkq hq (L := Lam1 ℬ θ astar) (cK := cK d) (l := H.sig⁻¹) (C := C) (N1 := (b : ℝ) + 1)
    (t1 := (t : ℝ) + 1) (m1 := (m : ℝ) + 1) (lam := lam) (z := z)
    (x := ((m : ℝ) + 1) / ((t : ℝ) + 1)) hL0.le hcK hl0 hC hlC (by positivity) hN1 hm1 hmt' hz0
    hlam4 hzx rfl
  have hHn := H.Hneg_kb_nonneg
  have hB := alg_B2 (d := d) (k := kk d) (m0 := v) (u := v) (lam := lam)
    (Hn := Hneg (kk d) (H.kb * (16 * d + 1)) (gB d)) (Rr := ((t : ℝ) + 1) / ((m : ℝ) + 1))
    (tauB_ge_r7 hz0.le v) (by linarith [(Nat.cast_nonneg v : (0 : ℝ) ≤ v)]) hkB2 (by positivity)
    (htm.trans (by linarith [(by exact_mod_cast hmv : (m : ℝ) ≤ v)])) hHn
  have hNB : ((b : ℝ) + 1) ^ (3 * kk d) ≤ (((2 * v : ℕ) : ℝ) + 1) ^ (3 * kk d) := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (b : ℝ) ≤ ((2 * v : ℕ) : ℝ) := by exact_mod_cast hb1
    linarith
  have hBterm : 2 ^ (4 * kk d) * 4 ^ d * (ρ / lam) ^ d / lam ^ (4 * kk d) *
      (Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) * ((b : ℝ) + 1) ^ (3 * kk d)) ≤
      H.cXB * (16 / ((m : ℝ) + 1) ^ 4 * (1 / 16) ^ i) := by
    have e : ρ / lam = ((t : ℝ) + 1) / ((m : ℝ) + 1) := by rw [← hρ]; field_simp
    rw [e]
    refine le_trans ?_ (hB.trans ?_)
    · refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNB hHn) (by positivity)
    · unfold cXB
      rw [div_eq_mul_one_div (2 ^ (4 * kk d) * 4 ^ d * Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) *
        4 ^ d * 8 ^ (3 * kk d) * 256)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      -- `v + 1 ≥ 2^i (m+1)/2`
      have hv2 : (2 : ℝ) ^ i * ((m : ℝ) + 1) ≤ 2 * ((v : ℝ) + 1) := by
        rw [hv]; push_cast
        have h3 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        have h2 : (1 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith
      have h16 : (16 : ℝ) ^ i = ((2 : ℝ) ^ i) ^ 4 := by
        rw [← pow_mul, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, mul_comm]
      have e2 : (16 : ℝ) / ((m : ℝ) + 1) ^ 4 * (1 / 16) ^ i =
          1 / ((2 : ℝ) ^ i * ((m : ℝ) + 1) / 2) ^ 4 := by
        rw [_root_.one_div_pow, h16]; field_simp; ring
      rw [e2]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hxq : (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ (512 * (d + 1)) ≤
      (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ (512 * (d + 1) - 2 * d - 2) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  rw [hρ] at hA hCt
  have hAx := hA.trans (mul_le_mul_of_nonneg_left hxq (by positivity))
  obtain ⟨X, hX⟩ : ∃ X, (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ (512 * (d + 1) - 2 * d - 2) = X :=
    ⟨_, rfl⟩
  rw [hX] at hAx hCt ⊢
  calc _ = (2 * Lam1 ℬ θ astar) ^ (4 * kk d) * cK d * ((b : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) +
        (2 ^ (4 * kk d) * 4 ^ d * (ρ / lam) ^ d / lam ^ (4 * kk d) *
          (Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) * ((b : ℝ) + 1) ^ (3 * kk d)) +
        2 ^ (4 * kk d) * 4 ^ d * (ρ / lam) ^ d / lam ^ (4 * kk d) *
          ((((b : ℝ) + 1) / ((m : ℝ) + 1)) ^ (d + 2) *
            (2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * cK d * ((m : ℝ) + 1) ^ (4 * kk d) +
              (H.sig⁻¹ * C) ^ (4 * kk d))))) := by rw [mul_add]
    _ ≤ (Lam1 ℬ θ astar / 2) ^ (4 * kk d) * cK d * X +
        (H.cXB * (16 / ((m : ℝ) + 1) ^ 4 * (1 / 16) ^ i) +
          4 ^ d * (Lam1 ℬ θ astar ^ (4 * kk d) * cK d + 1) * X) :=
        add_le_add hAx (add_le_add hBterm hCt)
    _ = H.cX1 * X + H.cXB * (16 / ((m : ℝ) + 1) ^ 4 * (1 / 16) ^ i) := by unfold cX1; ring

omit he in
/-- **normalized crossings in the window** -/
theorem cross_window (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {m t : ℕ} {z : ℝ} (hz0 : 0 < z)
    (hm : 1 ≤ m) (hmt : m ≤ t) (htT : t < T)
    (hzx : (((m : ℝ) + 1) / z) ^ 8 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1))
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (htm : ((t : ℝ) + 1) / ((m : ℝ) + 1) ≤ (m : ℝ) + 1) :
    P.real {ω | ∃ s, m ≤ s ∧ s ≤ t ∧ ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
        tauB z s < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)} ≤
      2 * H.cX1 * (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4 + 18 * H.cXB / ((m : ℝ) + 1) ^ 4 := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hmt' : (m : ℝ) + 1 ≤ (t : ℝ) + 1 := by linarith [(by exact_mod_cast hmt : (m : ℝ) ≤ t)]
  have hx1 : ((m : ℝ) + 1) / ((t : ℝ) + 1) ≤ 1 := (div_le_one ht1).2 hmt'
  have hx0 : 0 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1) := by positivity
  have h := dyadic_union P (fun s => {ω | ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
    tauB z s < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)}) (t := t) hm
  refine h.trans ?_
  obtain ⟨x, hx⟩ : ∃ x, ((m : ℝ) + 1) / ((t : ℝ) + 1) = x := ⟨_, rfl⟩
  have hs := cw_sum (c1 := H.cX1) (cB := H.cXB) (m1 := (m : ℝ) + 1)
    (x := x ^ (512 * (d + 1) - 2 * d - 2)) (n := Nat.log 2 (t / m) + 1) H.cX1_nonneg H.cXB_nonneg
    (by rw [← hx]; positivity) hm1
    (a := fun i => P.real {ω | ∃ s, 2 ^ i * m ≤ s ∧ s ≤ min (2 ^ (i + 1) * m) t ∧
        ω ∈ {ω | ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
          tauB z s < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)}})
    (fun i hi => by
      have := H.cross_block he hR hC hcor hz0 hm hmt htT hi hzx hlC htm
      rw [hx] at this; exact this)
  refine hs.trans ?_
  have hcnt := dyadic_count hm hmt
  rw [hx] at hx1 hx0
  have hx4 : x ^ (512 * (d + 1) - 2 * d - 2) = x * x ^ (512 * (d + 1) - 2 * d - 3) := by
    rw [← pow_succ']; congr 1; omega
  have hx5 : x ^ (512 * (d + 1) - 2 * d - 3) ≤ x ^ 4 := pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hc1 := H.cX1_nonneg
  have h1 : ((Nat.log 2 (t / m) + 1 : ℕ) : ℝ) * x ≤ 2 := by
    have : 2 * x = 2 * (((m : ℝ) + 1) / ((t : ℝ) + 1)) := by rw [hx]
    have hxe : x * (((t : ℝ) + 1) / ((m : ℝ) + 1)) = 1 := by rw [← hx]; field_simp
    nlinarith
  rw [hx4]
  have h2 : ((Nat.log 2 (t / m) + 1 : ℕ) : ℝ) * (H.cX1 * (x * x ^ (512 * (d + 1) - 2 * d - 3))) ≤
      2 * H.cX1 * x ^ 4 := by
    have hp : 0 ≤ x ^ (512 * (d + 1) - 2 * d - 3) := by positivity
    calc ((Nat.log 2 (t / m) + 1 : ℕ) : ℝ) * (H.cX1 * (x * x ^ (512 * (d + 1) - 2 * d - 3)))
        = H.cX1 * x ^ (512 * (d + 1) - 2 * d - 3) * (((Nat.log 2 (t / m) + 1 : ℕ) : ℝ) * x) := by ring
      _ ≤ H.cX1 * x ^ (512 * (d + 1) - 2 * d - 3) * 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ H.cX1 * x ^ 4 * 2 := by gcongr
      _ = 2 * H.cX1 * x ^ 4 := by ring
  push_cast at h2 ⊢
  rw [hx]
  linarith

end Sharp

end G26G


theorem _root_.solution : type_of% @G26G.Sharp.cross_window := @G26G.Sharp.cross_window
