-- Prove2me | solution 1 for G26G.Sharp.far_prob
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:36:31.294455+00:00
-- url     : https://prove2.me/submissions/e4c99401-1045-42aa-9028-ed6cba877c88

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_G26_FI_absMax_env
import Theorems.Thm_G26_SI_inv_moment
import Theorems.Thm_G26G_Sharp_runF_SI
import Theorems.Thm_G26R_runK_FI
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_J_4

-- ===== Solutions.C37.Base =====

/-! # Elementary inequalities for the scalar moment analysis (v1 Appendix I.5 and helpers) -/

namespace C37

/-! ## Second-order remainders of powers -/

/-- `(y+z)^{m+2} − y^{m+2} − (m+2) y^{m+1} z` is at most `(m+2)(m+1)/2 (|y|+|z|)^m z²` in absolute
value (v1 (I.8), by induction on the exponent). -/
lemma binom_rem (y z : ℝ) (m : ℕ) :
    |(y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z| ≤
      ((m + 2) * (m + 1) / 2 : ℝ) * (|y| + |z|) ^ m * z ^ 2 := by
  induction m with
  | zero =>
    have e : (y + z) ^ (0 + 2) - y ^ (0 + 2) - ((0 : ℕ) + 2 : ℝ) * y ^ (0 + 1) * z = z ^ 2 := by
      push_cast; ring
    rw [e]; simp [abs_of_nonneg (sq_nonneg z)]
  | succ m ih =>
    have e : (y + z) ^ (m + 1 + 2) - y ^ (m + 1 + 2) - ((m + 1 : ℕ) + 2 : ℝ) * y ^ (m + 1 + 1) * z =
        (y + z) * ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z) +
          (m + 2) * y ^ (m + 1) * z ^ 2 := by
      push_cast; ring
    rw [e]
    have hyz : |y + z| ≤ |y| + |z| := abs_add_le y z
    have hs0 : 0 ≤ |y| + |z| := by positivity
    have hy : |y| ^ (m + 1) ≤ (|y| + |z|) ^ (m + 1) :=
      pow_le_pow_left₀ (abs_nonneg y) (by linarith [abs_nonneg z]) _
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    calc |(y + z) * ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z) +
          (m + 2) * y ^ (m + 1) * z ^ 2|
        ≤ |y + z| * |(y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z| +
            (m + 2) * |y| ^ (m + 1) * z ^ 2 := by
          refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) (le_of_eq ?_))
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hz2, abs_of_nonneg (by positivity : (0:ℝ) ≤ m + 2)]
      _ ≤ (|y| + |z|) * (((m + 2) * (m + 1) / 2 : ℝ) * (|y| + |z|) ^ m * z ^ 2) +
            (m + 2) * (|y| + |z|) ^ (m + 1) * z ^ 2 := by
          gcongr
      _ = (((m + 1 : ℕ) + 2) * ((m + 1 : ℕ) + 1) / 2 : ℝ) * (|y| + |z|) ^ (m + 1) * z ^ 2 := by
          push_cast; ring

/-- the upper Taylor bound for an arbitrary power `P ≥ 2` -/
lemma pow_taylor (y z : ℝ) (P : ℕ) (hP : 2 ≤ P) :
    (y + z) ^ P ≤ y ^ P + P * y ^ (P - 1) * z +
      ((P : ℝ) * (P - 1) / 2) * (|y| + |z|) ^ (P - 2) * z ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
  have h := le_abs_self ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z)
  have h2 := binom_rem y z m
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  push_cast
  have e3 : ((m : ℝ) + 2) * ((m : ℝ) + 2 - 1) / 2 = ((m + 2) * (m + 1) / 2 : ℝ) := by ring
  rw [e3]
  linarith

/-- (C.202a): the inverse-power bound for small relative increments, `Pε ≤ 1/2` -/
lemma inv_pow_taylor (y z ε : ℝ) (P : ℕ) (hP : 2 ≤ P) (hy : 0 < y) (hε : 0 ≤ ε)
    (hz : |z| ≤ ε * y) (hεP : (P : ℝ) * ε ≤ 1 / 2) :
    1 / (y + z) ^ P ≤ 1 / y ^ P - P * z / y ^ (P + 1) + (P : ℝ) * (P + 1) * z ^ 2 / y ^ (P + 2) := by
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hε1 : ε ≤ 1 / 4 := by nlinarith
  have hzy : z ≥ -(ε * y) := by have := neg_abs_le z; linarith
  have hyz : 0 < y + z := by nlinarith
  set x := z / y with hx
  have hxa : |x| ≤ ε := by rw [hx, abs_div, abs_of_pos hy, div_le_iff₀ hy]; exact hz
  have hx1 : 0 < 1 + x := by
    have := neg_abs_le x; linarith
  set w := -x / (1 + x) with hw
  -- `(y/(y+z))^P = (1 + w)^P`
  have hq : y / (y + z) = 1 + w := by
    rw [hw, hx]; field_simp; ring
  have hT := pow_taylor 1 w P hP
  simp only [one_pow, mul_one, abs_one] at hT
  -- bounds on `w`
  have hxle : 1 - ε ≤ 1 + x := by have := neg_abs_le x; linarith
  have h1ε : 0 < 1 - ε := by linarith
  have hw_abs : |w| ≤ ε / (1 - ε) := by
    rw [hw, abs_div, abs_neg, abs_of_pos hx1]
    exact div_le_div₀ hε hxa h1ε hxle
  have hwlin : (P : ℝ) * w ≤ -(P * x) + P * (2 * x ^ 2) := by
    have e : w = -x + x ^ 2 / (1 + x) := by rw [hw]; field_simp; ring
    rw [e]
    have : x ^ 2 / (1 + x) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ hx1]; nlinarith [sq_nonneg x]
    nlinarith
  have hw2 : w ^ 2 ≤ x ^ 2 / (1 - ε) ^ 2 := by
    rw [hw, div_pow, neg_sq]
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (pow_le_pow_left₀ h1ε.le hxle 2)
  have hgeo : (1 + |w|) ^ (P - 2) / (1 - ε) ^ 2 ≤ 2 := by
    have hb : 1 + |w| ≤ 1 / (1 - ε) := by
      have : 1 + ε / (1 - ε) = 1 / (1 - ε) := by field_simp; ring
      linarith
    have hpe : (1 - ε) ^ P ≥ 1 / 2 := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) P
      have e : (1 + -ε) = 1 - ε := by ring
      rw [e] at h
      linarith
    have e : (1 / (1 - ε)) ^ (P - 2) / (1 - ε) ^ 2 = 1 / (1 - ε) ^ P := by
      obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
      have : m + 2 - 2 = m := by omega
      rw [this, one_div_pow, div_div, ← pow_add]
    calc (1 + |w|) ^ (P - 2) / (1 - ε) ^ 2 ≤ (1 / (1 - ε)) ^ (P - 2) / (1 - ε) ^ 2 := by
          gcongr
      _ = 1 / (1 - ε) ^ P := e
      _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hcoef : ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * w ^ 2 ≤
      ((P : ℝ) * (P - 1)) * x ^ 2 := by
    have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by nlinarith
    calc ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * w ^ 2
        ≤ ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * (x ^ 2 / (1 - ε) ^ 2) := by gcongr
      _ = ((P : ℝ) * (P - 1) / 2) * ((1 + |w|) ^ (P - 2) / (1 - ε) ^ 2) * x ^ 2 := by ring
      _ ≤ ((P : ℝ) * (P - 1) / 2) * 2 * x ^ 2 := by gcongr
      _ = ((P : ℝ) * (P - 1)) * x ^ 2 := by ring
  have hmain : (1 + w) ^ P ≤ 1 - P * x + (P : ℝ) * (P + 1) * x ^ 2 := by
    have e : (P : ℝ) * (P + 1) * x ^ 2 = P * (2 * x ^ 2) + ((P : ℝ) * (P - 1)) * x ^ 2 := by ring
    rw [e]
    linarith
  -- rescale by `y^{-P}`
  have hfrac : 1 / (y + z) ^ P = (y / (y + z)) ^ P / y ^ P := by
    rw [div_pow]; field_simp
  rw [hfrac, hq]
  have hyP : 0 < y ^ P := pow_pos hy P
  calc (1 + w) ^ P / y ^ P ≤ (1 - P * x + (P : ℝ) * (P + 1) * x ^ 2) / y ^ P :=
        div_le_div_of_nonneg_right hmain hyP.le
    _ = 1 / y ^ P - P * z / y ^ (P + 1) + (P : ℝ) * (P + 1) * z ^ 2 / y ^ (P + 2) := by
        rw [hx]; field_simp; ring

end C37


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

lemma ae_mem {n : Measure (Fin d → ℝ)} {𝒜 : Set (Fin d → ℝ)} (hn : n 𝒜ᶜ = 0) :
    ∀ᵐ a ∂n, a ∈ 𝒜 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hn] with a ha
  simpa using ha

lemma integrable_cpt {F : Type*} [NormedAddCommGroup F] {n : Measure (Fin d → ℝ)}
    [IsFiniteMeasure n] {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hn : n 𝒜ᶜ = 0)
    {f : (Fin d → ℝ) → F} (hf : Continuous f) : Integrable f n := by
  obtain ⟨C, hC⟩ := h𝒜.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (by filter_upwards [ae_mem hn] with a ha using hC a ha)

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


-- ===== Solutions.G2.Lex =====

/-! ### Lexicographic minimizers exist on compact sets -/

open Set IAFTRL

namespace G2L

variable {d : ℕ}

lemma lex_min_exists {M : Set (Fin d → ℝ)} (hM : IsCompact M) (hne : M.Nonempty) :
    ∃ b ∈ M, ∀ b' ∈ M, toLex b ≤ toLex b' := by
  have key : ∀ n : ℕ, ∃ b ∈ M, ∀ b' ∈ M, (∀ j : Fin d, j.val < n → b j = b' j) ∨
      ∃ i : Fin d, i.val < n ∧ (∀ j : Fin d, j < i → b j = b' j) ∧ b i < b' i := by
    intro n
    induction n with
    | zero =>
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, hb, fun b' _ => Or.inl fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨b, hbM, hb⟩ := ih
      by_cases hnd : n < d
      · set M' := {b' ∈ M | ∀ j : Fin d, j.val < n → b' j = b j} with hM'
        have hM'c : IsCompact M' := by
          change IsCompact (M ∩ {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j})
          refine hM.inter_right ?_
          have : {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j} =
              ⋂ j : Fin d, ⋂ (_ : j.val < n), {b' | b' j = b j} := by
            ext b'; simp
          rw [this]
          exact isClosed_iInter fun j => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply j) continuous_const
        have hM'ne : M'.Nonempty := ⟨b, hbM, fun _ _ => rfl⟩
        obtain ⟨bs, ⟨hbsM, hbsb⟩, hmin⟩ :=
          hM'c.exists_isMinOn hM'ne (continuous_apply (⟨n, hnd⟩ : Fin d)).continuousOn
        refine ⟨bs, hbsM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · have hb'M' : b' ∈ M' := ⟨hb'M, fun j hj => (hA j hj).symm⟩
          have hle : bs ⟨n, hnd⟩ ≤ b' ⟨n, hnd⟩ := hmin hb'M'
          rcases hle.lt_or_eq with hlt | heq
          · refine Or.inr ⟨⟨n, hnd⟩, Nat.lt_succ_self n, fun j hj => ?_, hlt⟩
            have hj' : j.val < n := hj
            rw [hbsb j hj', hA j hj']
          · refine Or.inl fun j hj => ?_
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · rw [hbsb j hj', hA j hj']
            · have : j = ⟨n, hnd⟩ := Fin.ext hj'
              rw [this, heq]
        · refine Or.inr ⟨i, Nat.lt_succ_of_lt hi, fun j hj => ?_, ?_⟩
          · have hj' : j.val < n := lt_trans hj hi
            rw [hbsb j hj', hpre j hj]
          · rw [hbsb i hi]; exact hlt
      · refine ⟨b, hbM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · exact Or.inl fun j _ => hA j (lt_of_lt_of_le j.isLt (not_lt.1 hnd))
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hpre, hlt⟩
  obtain ⟨b, hbM, hb⟩ := key d
  refine ⟨b, hbM, fun b' hb'M => ?_⟩
  rcases hb b' hb'M with hA | ⟨i, -, hpre, hlt⟩
  · have : b = b' := funext fun j => hA j j.isLt
    rw [this]
  · exact le_of_lt ⟨i, hpre, hlt⟩

lemma lexMinimizer_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (v : Fin d → ℝ) : lexMinimizer ℬ v ∈ ℬ := by
  have hc : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v := by
    simp only [dotProduct]; fun_prop
  obtain ⟨b₀, hb₀, hmin⟩ := hℬ.exists_isMinOn hne hc.continuousOn
  set M := ℬ ∩ {b | b ⬝ᵥ v ≤ b₀ ⬝ᵥ v} with hM
  have hMc : IsCompact M := hℬ.inter_right (isClosed_le hc continuous_const)
  obtain ⟨b, ⟨hbℬ, hbv⟩, hlex⟩ := lex_min_exists hMc ⟨b₀, hb₀, show b₀ ⬝ᵥ v ≤ b₀ ⬝ᵥ v from le_refl _⟩
  have h : ∃ b ∈ ℬ, (∀ a ∈ ℬ, b ⬝ᵥ v ≤ a ⬝ᵥ v) ∧
      ∀ b' ∈ ℬ, (∀ a ∈ ℬ, b' ⬝ᵥ v ≤ a ⬝ᵥ v) → toLex b ≤ toLex b' :=
    ⟨b, hbℬ, fun a ha => le_trans hbv (hmin ha),
      fun b' hb' hb'min => hlex b' ⟨hb', hb'min b₀ hb₀⟩⟩
  unfold lexMinimizer
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

lemma cand_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) (m : ℕ) : cand ℬ e m ∈ ℬ :=
  lexMinimizer_mem hℬ hne _

lemma gref_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ) : gref ℬ e t S ∈ ℬ :=
  cand_mem hℬ hne e _

end G2L


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


-- ===== Solutions.G2.Law =====

/-! ### Joint law of a sub-σ-algebra measurable statistic and a conditionally distributed variable -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace G2W

variable {Ω : Type*} {G : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
  [IsProbabilityMeasure P] (hG : G ≤ mΩ)
  {𝒵 : Type*} [MeasurableSpace 𝒵] {Z : Ω → 𝒵} (hZ : Measurable[G] Z)
  {E : Type*} [MeasurableSpace E] {X : Ω → E} (hX : Measurable X)
  (κ : Kernel 𝒵 E) [IsMarkovKernel κ]
  (hlaw : ∀ s, MeasurableSet s →
    P[(X ⁻¹' s).indicator (fun _ => (1 : ℝ)) | G] =ᵐ[P] fun ω => (κ (Z ω) s).toReal)
include hG hZ hX hlaw

theorem law_eq : P.map (fun ω => (Z ω, X ω)) = (P.map Z) ⊗ₘ κ := by
  have hZm : Measurable Z := hZ.mono hG le_rfl
  have hpair : Measurable fun ω => (Z ω, X ω) := hZm.prodMk hX
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZm.aemeasurable
  haveI : IsProbabilityMeasure (P.map fun ω => (Z ω, X ω)) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨B, hB, s, hs, rfl⟩
  rw [Measure.map_apply hpair (hB.prod hs), Measure.compProd_apply_prod hB hs,
    setLIntegral_map hB (κ.measurable_coe hs) hZm]
  have hZB : MeasurableSet[G] (Z ⁻¹' B) := hZ hB
  have hpre : (fun ω => (Z ω, X ω)) ⁻¹' (B ×ˢ s) = Z ⁻¹' B ∩ X ⁻¹' s := by ext; simp
  rw [hpre]
  have hint : Integrable ((X ⁻¹' s).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hX hs)
  have h1 := setIntegral_condExp hG hint hZB
  rw [setIntegral_congr_ae (hG _ hZB) (by filter_upwards [hlaw s hs] with ω hω _ using hω)] at h1
  -- both sides as real numbers
  have hL : ∫ ω in Z ⁻¹' B, (X ⁻¹' s).indicator (fun _ => (1 : ℝ)) ω ∂P =
      P.real (Z ⁻¹' B ∩ X ⁻¹' s) := by
    rw [integral_indicator (hX hs), Measure.restrict_restrict (hX hs), setIntegral_const,
      smul_eq_mul, mul_one, Set.inter_comm]
  have hR : ∫ ω in Z ⁻¹' B, (κ (Z ω) s).toReal ∂P =
      (∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P).toReal := by
    exact integral_toReal (f := fun ω => κ (Z ω) s) ((κ.measurable_coe hs).comp hZm).aemeasurable
      (ae_of_all _ fun ω => measure_lt_top _ _)
  rw [hL, hR] at h1
  have hfin : ∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top (measure_ne_top (P.restrict (Z ⁻¹' B)) univ) ?_
    calc ∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P ≤ ∫⁻ _ in Z ⁻¹' B, 1 ∂P :=
          lintegral_mono fun ω => prob_le_one
      _ = (P.restrict (Z ⁻¹' B)) univ := by simp
  rw [measureReal_def] at h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin).1 h1.symm

theorem integral_law {F : 𝒵 × E → ℝ} (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F (Z ω, X ω)) P) :
    ∫ ω, F (Z ω, X ω) ∂P = ∫ ω, ∫ x, F (Z ω, x) ∂(κ (Z ω)) ∂P := by
  have hZm : Measurable Z := hZ.mono hG le_rfl
  have hpair : Measurable fun ω => (Z ω, X ω) := hZm.prodMk hX
  have hlawe := law_eq P hG hZ hX κ hlaw
  have hFi' : Integrable F ((P.map Z) ⊗ₘ κ) := by
    rw [← hlawe]
    exact (integrable_map_measure hF.aestronglyMeasurable hpair.aemeasurable).2 hFi
  rw [← integral_map hpair.aemeasurable hF.aestronglyMeasurable, hlawe,
    Measure.integral_compProd hFi',
    integral_map hZm.aemeasurable (hF.integral_kernel_prod_right').aestronglyMeasurable]

end G2W


-- ===== Solutions.G2.Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

lemma conv_eq {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) :
    convexHull ℝ 𝒜 = Kset ℬ :=
  (convexHull_min hgen.2 (convex_convexHull ℝ ℬ)).antisymm (convexHull_mono hgen.1)

lemma abs_dot_le_one {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hgen : IsGenerator 𝒜 ℬ)
    {θ : Fin d → ℝ} (hθ : setNorm 𝒜 θ ≤ 1) {x : Fin d → ℝ} (hx : x ∈ Kset ℬ) :
    |x ⬝ᵥ θ| ≤ 1 := by
  rw [← conv_eq hgen] at hx
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ θ| := by
    simp only [dotProduct]; fun_prop
  have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ} := by
    have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ θ) :=
      ⟨fun x y => add_dotProduct x y θ, fun c x => smul_dotProduct c x θ⟩
    have : {x : Fin d → ℝ | |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ} =
        {w | w ⬝ᵥ θ ≤ setNorm 𝒜 θ} ∩ {w | -setNorm 𝒜 θ ≤ w ⬝ᵥ θ} := by
      ext x; simp [abs_le, and_comm]
    rw [this]
    exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
  have := convexHull_min (fun a ha => le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩) hcvx hx
  exact le_trans (show |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ from this) hθ

lemma Kset_compact {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

lemma span_B {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : Submodule.span ℝ ℬ = ⊤ := by
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 fun a ha => ?_
  have : convexHull ℝ ℬ ⊆ Submodule.span ℝ ℬ :=
    convexHull_min Submodule.subset_span (Submodule.span ℝ ℬ).convex
  exact this (hgen.2 ha)

lemma B_nonempty {𝒜 ℬ : Set (Fin d → ℝ)} (hd : 1 ≤ d) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : ℬ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have := span_B hgen hspan
  rw [h, Submodule.span_empty] at this
  have hne : (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) ∈ (⊤ : Submodule ℝ (Fin d → ℝ)) := trivial
  rw [← this, Submodule.mem_bot] at hne
  have := congrFun hne ⟨0, hd⟩
  simp at this

/-- the gauge of `𝒮` is at most `2` on differences of points of `𝒦` -/
lemma sNorm_sub_le {𝒜 ℬ : Set (Fin d → ℝ)} (hd : 1 ≤ d) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {u w : Fin d → ℝ} (hu : u ∈ Kset ℬ) (hw : w ∈ Kset ℬ) :
    sNorm ℬ (u - w) ≤ 2 := by
  have hBne := B_nonempty hd hgen hspan
  have habs : Absorbent ℝ (Sset ℬ) := absorbent_nhds_zero (T31.Sset_nhds hBne (span_B hgen hspan))
  have hconv : Convex ℝ (Sset ℬ) := convex_convexHull ℝ _
  have hsub : Kset ℬ ⊆ Sset ℬ := convexHull_mono subset_union_left
  have hsymm : ∀ x ∈ Sset ℬ, -x ∈ Sset ℬ := by
    intro x hx
    have h' : -(ℬ ∪ -ℬ) = ℬ ∪ -ℬ := by
      ext y; simp only [Set.mem_neg, Set.mem_union, neg_neg]; tauto
    have : -x ∈ -convexHull ℝ (ℬ ∪ -ℬ) := by rw [Set.neg_mem_neg]; exact hx
    rw [← convexHull_neg, h'] at this
    exact this
  have h1 : gauge (Sset ℬ) u ≤ 1 := gauge_le_one_of_mem (hsub hu)
  have h2 : gauge (Sset ℬ) (-w) ≤ 1 := gauge_le_one_of_mem (hsymm _ (hsub hw))
  have := gauge_add_le hconv habs u (-w)
  rw [← sub_eq_add_neg] at this
  unfold sNorm
  linarith

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

/-- the latent action lies in `𝒦` almost surely -/
lemma X_mem_K [IsProbabilityMeasure P] (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (hℬ : IsCompact ℬ)
    {t : ℕ} (ht : t < T) : ∀ᵐ ω ∂P, R.X t ω ∈ Kset ℬ := by
  have hKc := (Kset_compact hℬ).isClosed.measurableSet.compl
  have hX : Measurable (R.X t) := (hR t ht).1.1
  have hlaw := (hR t ht).2.2.1 _ hKc
  have hGle := G_le hR ht
  have hint : Integrable ((R.X t ⁻¹' (Kset ℬ)ᶜ).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hX hKc)
  have h1 := integral_condExp hGle (μ := P) (f := (R.X t ⁻¹' (Kset ℬ)ᶜ).indicator fun _ => (1 : ℝ))
  rw [integral_congr_ae hlaw] at h1
  simp only [p_supp hR ht, ENNReal.toReal_zero, integral_zero] at h1
  rw [integral_indicator (hX hKc), setIntegral_const, smul_eq_mul, mul_one] at h1
  have h0 : P (R.X t ⁻¹' (Kset ℬ)ᶜ) = 0 := by
    simp only [measureReal_restrict_apply_univ, measureReal_def] at h1
    exact (ENNReal.toReal_eq_zero_iff _).1 h1.symm |>.resolve_right (measure_ne_top _ _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  simpa using hω

end Run

/-! #### Deterministic range bounds -/

/-- the deterministic range recursion -/
noncomputable def rho (d : ℕ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => rho d t + 2 * (gbeta d (t + 1) + rho d t / gB d)

lemma gbeta_pos (hd : 1 ≤ d) (t : ℕ) : 0 < gbeta d t := by
  unfold gbeta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

lemma gB_pos : 0 < gB d := by unfold gB; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma v_bound (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    (ω : Ω) {ρ : ℝ}
    (hS : ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ, |(u - w) ⬝ᵥ R.cumEst t ω| ≤ ρ) :
    ∀ x ∈ Kset ℬ, ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ gv (R.p t ω) x| ≤ 2 * (gbeta d (t + 1) + ρ / gB d) := by
  intro x hX u hu w hw
  set S := R.cumEst t ω
  set b := gref ℬ e (t + 1) S
  have hbK : b ∈ Kset ℬ :=
    subset_convexHull ℝ ℬ (G2L.gref_mem hℬ (B_nonempty hd hgen hspan) e (t + 1) S)
  have hU := (feas hR ht ω).2.2.2.2.1
  have hβ := gbeta_pos hd (t + 1)
  have hB := gB_pos (d := d)
  have hUb : ∀ x ∈ Kset ℬ, gU ℬ e (t + 1) S x ≤ gbeta d (t + 1) + ρ / gB d := by
    intro y hy
    unfold gU
    have h1 : sNorm ℬ (y - gref ℬ e (t + 1) S) ≤ 2 := sNorm_sub_le hd hgen hspan hy hbK
    have h2 : gZ ℬ e (t + 1) S y ≤ ρ := by
      unfold gZ
      refine max_le ?_ ?_
      · exact le_trans (abs_nonneg _) (hS y hy b hbK)
      · have := hS y hy b hbK
        rw [sub_dotProduct] at this
        exact le_trans (le_abs_self _) this
    have h3 : gbeta d (t + 1) / 2 * sNorm ℬ (y - gref ℬ e (t + 1) S) ≤ gbeta d (t + 1) := by
      nlinarith
    have h4 : gZ ℬ e (t + 1) S y / gB d ≤ ρ / gB d := div_le_div_of_nonneg_right h2 hB.le
    linarith
  have h1 := hU u hu x hX
  have h2 := hU w hw x hX
  have heq : (u - w) ⬝ᵥ gv (R.p t ω) x =
      (u - b) ⬝ᵥ gv (R.p t ω) x - (w - b) ⬝ᵥ gv (R.p t ω) x := by
    simp only [sub_dotProduct]; ring
  rw [heq]
  calc |(u - b) ⬝ᵥ gv (R.p t ω) x - (w - b) ⬝ᵥ gv (R.p t ω) x|
      ≤ |(u - b) ⬝ᵥ gv (R.p t ω) x| + |(w - b) ⬝ᵥ gv (R.p t ω) x| :=
        abs_sub _ _
    _ ≤ gU ℬ e (t + 1) S u + gU ℬ e (t + 1) S w := add_le_add h1 h2
    _ ≤ 2 * (gbeta d (t + 1) + ρ / gB d) := by linarith [hUb u hu, hUb w hw]

lemma range_bound [IsProbabilityMeasure P] (hd : 1 ≤ d) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) :
    ∀ t, t ≤ T → ∀ᵐ ω ∂P, ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ R.cumEst t ω| ≤ rho d t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ae_of_all _ fun ω u _ w _ => by simp [GRun.cumEst, rho]
  | succ t ih =>
    intro ht
    have ht' : t < T := by omega
    filter_upwards [ih (by omega), X_mem_K hR hℬ ht'] with ω hS hX
    intro u hu w hw
    have hv := v_bound hd hℬ hgen hspan hR ht' ω hS (R.X t ω) hX u hu w hw
    have hY : |R.Y t ω| ≤ 1 := (hR t ht').2.2.2.2.1.1 ω
    have hsum : R.cumEst (t + 1) ω = R.cumEst t ω + R.thetaHat t ω := by
      simp [GRun.cumEst, Finset.sum_range_succ]
    rw [hsum, dotProduct_add]
    have hθ : |(u - w) ⬝ᵥ R.thetaHat t ω| ≤ 2 * (gbeta d (t + 1) + rho d t / gB d) := by
      rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
      calc |R.Y t ω| * |(u - w) ⬝ᵥ gv (R.p t ω) (R.X t ω)|
          ≤ 1 * (2 * (gbeta d (t + 1) + rho d t / gB d)) :=
            mul_le_mul hY hv (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc |(u - w) ⬝ᵥ R.cumEst t ω + (u - w) ⬝ᵥ R.thetaHat t ω|
        ≤ |(u - w) ⬝ᵥ R.cumEst t ω| + |(u - w) ⬝ᵥ R.thetaHat t ω| := abs_add_le _ _
      _ ≤ rho d t + 2 * (gbeta d (t + 1) + rho d t / gB d) := add_le_add (hS u hu w hw) hθ
      _ = rho d (t + 1) := rfl

/-- the almost sure bound on reconstruction differences in round `t` -/
lemma v_bound_ae [IsProbabilityMeasure P] (hd : 1 ≤ d) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    ∀ᵐ ω ∂P, R.X t ω ∈ Kset ℬ ∧ ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ 2 * (gbeta d (t + 1) + rho d t / gB d) := by
  filter_upwards [range_bound hd hℬ hgen hspan hR t ht.le, X_mem_K hR hℬ ht] with ω hS hX
  exact ⟨hX, v_bound hd hℬ hgen hspan hR ht ω hS (R.X t ω) hX⟩

end Bounds

end G2R


-- ===== Solutions.G2.Exp =====

/-! ### Conditional expectation identities along a GIA-FTRL run -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G2E

variable {d : ℕ}

/-- the statistic space `(p_t, S_t, θ_t)` -/
abbrev Zsp (d : ℕ) := Measure (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ)

/-- the conditional law kernel of the latent action -/
noncomputable def kZ : Kernel (Zsp d) (Fin d → ℝ) := G2M.kmk.comap Prod.fst measurable_fst

instance : IsMarkovKernel (kZ (d := d)) := by unfold kZ; infer_instance

/-- the dot product as a continuous bilinear map -/
noncomputable def dotB : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x ⬝ᵥ y) (fun x y z => add_dotProduct x y z)
    (fun c x y => smul_dotProduct c x y) (fun x y z => dotProduct_add x y z)
    (fun c x y => dotProduct_smul c x y)

noncomputable def dotL : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin d → ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ dotB)

@[simp] lemma dotL_apply (x y : Fin d → ℝ) : dotL x y = x ⬝ᵥ y := rfl

lemma bil_designMat {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν] {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (a θ : Fin d → ℝ) :
    ∫ x, (a ⬝ᵥ x) * (x ⬝ᵥ θ) ∂ν = a ⬝ᵥ (designMat ν *ᵥ θ) := by
  have hI : ∀ i j, Integrable (fun x : Fin d → ℝ => a i * θ j * (x i * x j)) ν := fun i j =>
    T31.integrable_cpt hK hν (by fun_prop)
  have hfun : (fun x : Fin d → ℝ => (a ⬝ᵥ x) * (x ⬝ᵥ θ)) =
      fun x => ∑ i, ∑ j, a i * θ j * (x i * x j) := by
    funext x
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  simp only [dotProduct, Matrix.mulVec, designMat, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; ring

/-- the reconstruction identity `∫ (wᵀ M⁻¹ x)(xᵀ θ) p(dx) = wᵀ θ` -/
lemma recon {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hPD : (designMat ν).PosDef) (w θ : Fin d → ℝ) :
    ∫ x, (w ⬝ᵥ gv ν x) * (x ⬝ᵥ θ) ∂ν = w ⬝ᵥ θ := by
  have hdet : IsUnit (designMat ν).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit
  have h1 : ∀ x, w ⬝ᵥ gv ν x = (Matrix.vecMul w (designMat ν)⁻¹) ⬝ᵥ x := fun x => by
    rw [gv, gM, Matrix.dotProduct_mulVec]
  simp_rw [h1]
  rw [bil_designMat hK hν, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- the statistic `(p_t, S_t, θ_t)` -/
noncomputable def Zst (R : GRun d Ω) (t : ℕ) (ω : Ω) : Zsp d := (R.p t ω, R.cumEst t ω, R.θs t ω)

lemma kZ_Zst (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    kZ (Zst R t ω) = R.p t ω := by
  haveI := G2R.p_prob hR ht ω
  simp [kZ, Zst, G2M.kmk, G2M.mk_eq]

end Run

/-- the σ-algebra `G_t ∨ σ(X_t)` -/
def mX {Ω : Type*} (R : GRun d Ω) (t : ℕ) : MeasurableSpace Ω :=
  R.G t ⊔ MeasurableSpace.comap (R.X t) inferInstance

/-- the σ-algebra `G_t ∨ σ(X_t, A_t)` -/
def mXA {Ω : Type*} (R : GRun d Ω) (t : ℕ) : MeasurableSpace Ω :=
  R.G t ⊔ MeasurableSpace.comap (fun ω => (R.X t ω, R.A t ω)) inferInstance

section Ident

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma integrable_A (hℬ : IsCompact ℬ) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    Integrable (R.A t) P := by
  obtain ⟨C, hC⟩ := hℬ.exists_bound_of_continuousOn continuous_id.continuousOn
  exact Integrable.of_bound (hR t ht).1.2.1.aestronglyMeasurable C
    (ae_of_all _ fun ω => hC _ ((hR t ht).2.2.2.1.1 ω))

end Ident

end G2E


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


-- ===== Solutions.G26.Step =====

/-! ### The killed one-step expectation tool, pointwise and integrated over a body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : ℕ → MeasurableSpace Ω} {n : ℕ}

lemma int_of_ae_bdd {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {c : ℝ}
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ c) : Integrable f μ :=
  Integrable.of_bound hf c (by filter_upwards [h] with ω hω; rwa [Real.norm_eq_abs])

/-- **Killed second-order step.** If on `J ∈ F` the next value obeys a second-order
expansion `H ≤ g₀ + g₁ ξ + g₂ ξ²` with `F`-measurable `g₁, g₂ ≥ 0`, then the conditional
drift and second-moment bounds may be substituted. -/
lemma pstep (hF : F n ≤ mΩ) {J : Set Ω} (hJ : MeasurableSet[F n] J)
    {H g0 g1 g2 ξ b1 V : Ω → ℝ} {c : ℝ}
    (hHm : AEStronglyMeasurable H μ) (hg0m : AEStronglyMeasurable g0 μ)
    (hg1m : StronglyMeasurable[F n] g1) (hg2m : StronglyMeasurable[F n] g2)
    (hξm : AEStronglyMeasurable ξ μ) (hb1m : AEStronglyMeasurable b1 μ)
    (hVm : AEStronglyMeasurable V μ)
    (hbd : ∀ᵐ ω ∂μ, |H ω| ≤ c ∧ |g0 ω| ≤ c ∧ |g1 ω| ≤ c ∧ |g2 ω| ≤ c ∧ |ξ ω| ≤ c ∧
      |b1 ω| ≤ c ∧ |V ω| ≤ c)
    (hpt : ∀ᵐ ω ∂μ, ω ∈ J → H ω ≤ g0 ω + g1 ω * ξ ω + g2 ω * ξ ω ^ 2)
    (hdr : ∀ᵐ ω ∂μ, ω ∈ J → g1 ω * μ[ξ | F n] ω ≤ b1 ω)
    (hse : ∀ᵐ ω ∂μ, ω ∈ J → μ[fun ω => ξ ω ^ 2 | F n] ω ≤ V ω)
    (hg2n : ∀ᵐ ω ∂μ, ω ∈ J → 0 ≤ g2 ω) :
    ∫ ω, J.indicator H ω ∂μ ≤ ∫ ω, J.indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ := by
  have hJm : MeasurableSet J := hF _ hJ
  set G1 := J.indicator g1 with hG1
  set G2 := J.indicator g2 with hG2
  have hG1m : StronglyMeasurable[F n] G1 := hg1m.indicator hJ
  have hG2m : StronglyMeasurable[F n] G2 := hg2m.indicator hJ
  have hc : ∀ᵐ ω ∂μ, 0 ≤ c := by
    filter_upwards [hbd] with ω h; exact le_trans (abs_nonneg _) h.1
  have hbG1 : ∀ᵐ ω ∂μ, ‖G1 ω‖ ≤ c := by
    filter_upwards [hbd, hc] with ω h hc0
    simp only [G1, Real.norm_eq_abs]
    by_cases hω : ω ∈ J
    · rw [Set.indicator_of_mem hω]; exact h.2.2.1
    · rw [Set.indicator_of_notMem hω, abs_zero]; exact hc0
  have hbG2 : ∀ᵐ ω ∂μ, ‖G2 ω‖ ≤ c := by
    filter_upwards [hbd, hc] with ω h hc0
    simp only [G2, Real.norm_eq_abs]
    by_cases hω : ω ∈ J
    · rw [Set.indicator_of_mem hω]; exact h.2.2.2.1
    · rw [Set.indicator_of_notMem hω, abs_zero]; exact hc0
  have hξi : Integrable ξ μ := int_of_ae_bdd hξm (by filter_upwards [hbd] with ω h; exact h.2.2.2.2.1)
  have hξ2i : Integrable (fun ω => ξ ω ^ 2) μ := by
    refine int_of_ae_bdd (hξm.pow 2) (c := c ^ 2) ?_
    filter_upwards [hbd] with ω h
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h.2.2.2.2.1 2
  have hG1a : AEStronglyMeasurable G1 μ := (hG1m.mono hF).aestronglyMeasurable
  have hG2a : AEStronglyMeasurable G2 μ := (hG2m.mono hF).aestronglyMeasurable
  have i1 : Integrable (G1 * ξ) μ := hξi.bdd_mul hG1a hbG1
  have i2 : Integrable (G2 * fun ω => ξ ω ^ 2) μ := hξ2i.bdd_mul hG2a hbG2
  have hg0i : Integrable (J.indicator g0) μ :=
    (int_of_ae_bdd hg0m (by filter_upwards [hbd] with ω h; exact h.2.1)).indicator hJm
  have hHi : Integrable (J.indicator H) μ :=
    (int_of_ae_bdd hHm (by filter_upwards [hbd] with ω h; exact h.1)).indicator hJm
  -- the conditional substitutions
  have e1 : ∫ ω, (G1 * ξ) ω ∂μ = ∫ ω, (G1 * μ[ξ | F n]) ω ∂μ := by
    rw [← integral_condExp hF]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hG1m i1 hξi)
  have e2 : ∫ ω, (G2 * fun ω => ξ ω ^ 2) ω ∂μ =
      ∫ ω, (G2 * μ[fun ω => ξ ω ^ 2 | F n]) ω ∂μ := by
    rw [← integral_condExp hF]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hG2m i2 hξ2i)
  have j1 : Integrable (G1 * μ[ξ | F n]) μ := integrable_condExp.bdd_mul hG1a hbG1
  have j2 : Integrable (G2 * μ[fun ω => ξ ω ^ 2 | F n]) μ := integrable_condExp.bdd_mul hG2a hbG2
  have hRi : Integrable (J.indicator fun ω => g0 ω + b1 ω + g2 ω * V ω) μ := by
    refine (int_of_ae_bdd (c := c + c + c * c) ((hg0m.add hb1m).add
      ((hg2m.mono hF).aestronglyMeasurable.mul hVm)) ?_).indicator hJm
    filter_upwards [hbd] with ω h
    obtain ⟨-, h0, -, h2, -, hb, hV⟩ := h
    calc |g0 ω + b1 ω + g2 ω * V ω| ≤ |g0 ω| + |b1 ω| + |g2 ω| * |V ω| := by
          rw [← abs_mul]
          exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ c + c + c * c := by
          gcongr
          exact le_trans (abs_nonneg _) h0
  calc ∫ ω, J.indicator H ω ∂μ
      ≤ ∫ ω, (J.indicator g0 ω + (G1 * ξ) ω + (G2 * fun ω => ξ ω ^ 2) ω) ∂μ := by
        refine integral_mono_ae hHi ((hg0i.add i1).add i2) ?_
        filter_upwards [hpt] with ω hω
        by_cases hJω : ω ∈ J
        · simp only [Set.indicator_of_mem hJω, G1, G2, Pi.mul_apply]
          exact hω hJω
        · simp [Set.indicator_of_notMem hJω, G1, G2]
    _ = ∫ ω, J.indicator g0 ω ∂μ + ∫ ω, (G1 * ξ) ω ∂μ + ∫ ω, (G2 * fun ω => ξ ω ^ 2) ω ∂μ := by
        rw [integral_add (f := fun ω => J.indicator g0 ω + (G1 * ξ) ω)
          (g := fun ω => (G2 * fun ω => ξ ω ^ 2) ω) (hg0i.add i1) i2,
          integral_add (f := fun ω => J.indicator g0 ω) (g := fun ω => (G1 * ξ) ω) hg0i i1]
    _ = ∫ ω, (J.indicator g0 ω + (G1 * μ[ξ | F n]) ω + (G2 * μ[fun ω => ξ ω ^ 2 | F n]) ω) ∂μ := by
        rw [e1, e2, integral_add (f := fun ω => J.indicator g0 ω + (G1 * μ[ξ | F n]) ω)
          (g := fun ω => (G2 * μ[fun ω => ξ ω ^ 2 | F n]) ω) (hg0i.add j1) j2,
          integral_add (f := fun ω => J.indicator g0 ω) (g := fun ω => (G1 * μ[ξ | F n]) ω)
            hg0i j1]
    _ ≤ ∫ ω, J.indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ := by
        refine integral_mono_ae ((hg0i.add j1).add j2) hRi ?_
        filter_upwards [hdr, hse, hg2n] with ω hd hs hn
        by_cases hJω : ω ∈ J
        · simp only [Set.indicator_of_mem hJω, G1, G2, Pi.mul_apply]
          have := mul_le_mul_of_nonneg_left (hs hJω) (hn hJω)
          linarith [hd hJω]
        · simp [Set.indicator_of_notMem hJω, G1, G2]

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


-- ===== Solutions.G26.RunCE =====

/-! ### Conditional moments of the loss estimates given the pre-action σ-algebra -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G26R

variable {d : ℕ}

/-- the statistic `(p_t, θ_t, φ)` -/
abbrev Zsp (d : ℕ) := Measure (Fin d → ℝ) × (Fin d → ℝ) × ℝ

/-- the conditional law kernel of the latent action on the augmented statistic -/
noncomputable def kφ : Kernel (Zsp d) (Fin d → ℝ) := G2M.kmk.comap Prod.fst measurable_fst

instance : IsMarkovKernel (kφ (d := d)) := by unfold kφ; infer_instance

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- the augmented statistic -/
noncomputable def Zφ (R : GRun d Ω) (t : ℕ) (φ : Ω → ℝ) (ω : Ω) : Zsp d :=
  (R.p t ω, R.θs t ω, φ ω)

lemma meas_Zφ (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) {φ : Ω → ℝ}
    (hφ : Measurable[R.G t] φ) : Measurable[R.G t] (Zφ R t φ) := by
  have hhG := G2R.hist_le_G hR ht
  have hp : Measurable[R.G t] (R.p t) := ((hR t ht).2.1.1).mono hhG le_rfl
  have hθ : Measurable[R.G t] (R.θs t) := (hR t ht).1.2.2.2.2.2.2.1
  exact hp.prodMk (hθ.prodMk hφ)

lemma kφ_Zφ (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (φ : Ω → ℝ) (ω : Ω) :
    kφ (Zφ R t φ ω) = R.p t ω := by
  haveI := G2R.p_prob hR ht ω
  simp [kφ, Zφ, G2M.kmk, G2M.mk_eq]

lemma int_law_φ (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) {φ : Ω → ℝ}
    (hφ : Measurable[R.G t] φ) {F : Zsp d × (Fin d → ℝ) → ℝ} (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F (Zφ R t φ ω, R.X t ω)) P) :
    ∫ ω, F (Zφ R t φ ω, R.X t ω) ∂P = ∫ ω, ∫ x, F (Zφ R t φ ω, x) ∂(R.p t ω) ∂P := by
  have hlaw : ∀ s, MeasurableSet s → P[(R.X t ⁻¹' s).indicator (fun _ => (1 : ℝ)) | R.G t] =ᵐ[P]
      fun ω => (kφ (Zφ R t φ ω) s).toReal := by
    intro s hs
    simp_rw [kφ_Zφ hR ht]
    exact (hR t ht).2.2.1 s hs
  rw [G2W.integral_law P (G2R.G_le hR ht) (meas_Zφ hR ht hφ) (hR t ht).1.1 kφ hlaw hF hFi]
  simp_rw [kφ_Zφ hR ht]

/-- **unbiasedness against a history-measurable test function** -/
lemma unbiased_φ (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    (w : Fin d → ℝ) {cw : ℝ} (hw : ∀ᵐ ω ∂P, |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ cw)
    {φ : Ω → ℝ} (hφ : Measurable[R.G t] φ) (hφb : ∀ ω, |φ ω| ≤ 1) :
    Integrable (fun ω => φ ω * (w ⬝ᵥ R.thetaHat t ω)) P ∧
    ∫ ω, φ ω * (w ⬝ᵥ R.thetaHat t ω) ∂P = ∫ ω, φ ω * (w ⬝ᵥ R.θs t ω) ∂P := by
  obtain ⟨⟨hX, hA, hY, hθ, hGle, -, hθG, -⟩, -, -, ⟨hAB, hAc⟩, ⟨hYb, hYc⟩, hθn⟩ := hR t ht
  have hKc := G2R.Kset_compact hℬ
  have hZ : Measurable[R.G t] (Zφ R t φ) := meas_Zφ hR ht hφ
  -- the scalar coefficient `c₁ = φ wᵀ v_X(p)`
  set F1 : Zsp d × (Fin d → ℝ) → ℝ := fun z => z.1.2.2 * (w ⬝ᵥ G2M.V z.1.1 z.2) with hF1
  have hF1m : Measurable F1 :=
    (measurable_snd.comp (measurable_snd.comp measurable_fst)).mul
      (G2R.meas_dot' measurable_const
        (G2M.measurable_V_comp (measurable_fst.comp measurable_fst) measurable_snd))
  set c1 : Ω → ℝ := fun ω => F1 (Zφ R t φ ω, R.X t ω) with hc1
  have hc1eq : ∀ ω, c1 ω = φ ω * (w ⬝ᵥ gv (R.p t ω) (R.X t ω)) := fun ω => by
    haveI := G2R.p_prob hR ht ω
    simp only [hc1, hF1, Zφ, G2M.V_eq]
  have hc1b : ∀ᵐ ω ∂P, |c1 ω| ≤ max cw 0 := by
    filter_upwards [hw] with ω hω
    rw [hc1eq, abs_mul]
    calc |φ ω| * |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ 1 * max cw 0 :=
          mul_le_mul (hφb ω) (hω.trans (le_max_left _ _)) (abs_nonneg _) zero_le_one
      _ = max cw 0 := one_mul _
  set cb := max cw 0 with hcb
  have hcb0 : 0 ≤ cb := le_max_right _ _
  -- measurability of `c₁` for the enlarged σ-algebras
  have hXmX : Measurable[G2E.mX R t] (R.X t) := Measurable.of_comap_le le_sup_right
  have hZmX : Measurable[G2E.mX R t] (Zφ R t φ) := hZ.mono le_sup_left le_rfl
  have hc1mX : Measurable[G2E.mX R t] c1 := hF1m.comp (hZmX.prodMk hXmX)
  have hXAm : Measurable[G2E.mXA R t] (fun ω => (R.X t ω, R.A t ω)) :=
    Measurable.of_comap_le le_sup_right
  have hc1mXA : Measurable[G2E.mXA R t] c1 :=
    hF1m.comp ((hZ.mono le_sup_left le_rfl).prodMk (measurable_fst.comp hXAm))
  have hmX : G2E.mX R t ≤ mΩ := sup_le hGle hX.comap_le
  have hmXA : G2E.mXA R t ≤ mΩ := sup_le hGle (hX.prodMk hA).comap_le
  have hc1m : Measurable c1 := hc1mX.mono hmX le_rfl
  -- integrability
  have hYi : Integrable (R.Y t) P := Integrable.of_bound hY.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa using hYb ω)
  have hc1Y : Integrable (c1 * R.Y t) P := by
    refine Integrable.of_bound (hc1m.mul hY).aestronglyMeasurable cb ?_
    filter_upwards [hc1b] with ω hω
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    nlinarith [hYb ω, abs_nonneg (c1 ω), abs_nonneg (R.Y t ω)]
  have hAθ : ∀ ω, |R.A t ω ⬝ᵥ R.θs t ω| ≤ 1 := fun ω =>
    G2R.abs_dot_le_one h𝒜 hgen (hθn ω) (subset_convexHull ℝ ℬ (hAB ω))
  have hc1A : Integrable (fun ω => G2E.dotL (c1 ω • R.θs t ω) (R.A t ω)) P := by
    refine Integrable.of_bound ?_ cb ?_
    · simp only [G2E.dotL_apply, smul_dotProduct, smul_eq_mul]
      exact (hc1m.mul (G2R.meas_dot' hθ hA)).aestronglyMeasurable
    · filter_upwards [hc1b] with ω hω
      simp only [G2E.dotL_apply, smul_dotProduct, smul_eq_mul, Real.norm_eq_abs, abs_mul]
      rw [dotProduct_comm]
      nlinarith [hAθ ω, abs_nonneg (c1 ω), abs_nonneg (R.A t ω ⬝ᵥ R.θs t ω)]
  -- step a: replace the feedback by its conditional mean
  have hstepa : ∫ ω, c1 ω * R.Y t ω ∂P = ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P := by
    have h := condExp_mul_of_stronglyMeasurable_left hc1mXA.stronglyMeasurable hc1Y hYi
    calc ∫ ω, c1 ω * R.Y t ω ∂P = ∫ ω, (c1 * R.Y t) ω ∂P := rfl
      _ = ∫ ω, P[c1 * R.Y t | G2E.mXA R t] ω ∂P := (integral_condExp hmXA).symm
      _ = ∫ ω, (c1 * P[R.Y t | G2E.mXA R t]) ω ∂P := integral_congr_ae h
      _ = ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hYc] with ω hω
          rw [Pi.mul_apply, show P[R.Y t | G2E.mXA R t] ω = R.A t ω ⬝ᵥ R.θs t ω from hω]
  -- step b: replace the physical action by the latent one
  have hstepb : ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P =
      ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P := by
    have hf : StronglyMeasurable[G2E.mX R t] fun ω => c1 ω • R.θs t ω :=
      (hc1mX.smul (hθG.mono le_sup_left le_rfl)).stronglyMeasurable
    have h := condExp_bilin_of_stronglyMeasurable_left G2E.dotL hf hc1A
      (G2E.integrable_A hℬ hR ht)
    calc ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P = ∫ ω, G2E.dotL (c1 ω • R.θs t ω) (R.A t ω) ∂P := by
          simp [smul_dotProduct, dotProduct_comm]
      _ = ∫ ω, P[fun ω => G2E.dotL (c1 ω • R.θs t ω) (R.A t ω) | G2E.mX R t] ω ∂P :=
          (integral_condExp hmX).symm
      _ = ∫ ω, G2E.dotL (c1 ω • R.θs t ω) (P[R.A t | G2E.mX R t] ω) ∂P := integral_congr_ae h
      _ = ∫ ω, G2E.dotL (c1 ω • R.θs t ω) (R.X t ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hAc] with ω hω
          rw [show P[R.A t | G2E.mX R t] ω = R.X t ω from hω]
      _ = ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P := by
          simp [smul_dotProduct, dotProduct_comm]
  -- step c: the conditional law of the latent action
  set F2 : Zsp d × (Fin d → ℝ) → ℝ := fun z => F1 z * (z.2 ⬝ᵥ z.1.2.1) with hF2
  have hF2m : Measurable F2 :=
    hF1m.mul (G2R.meas_dot' measurable_snd
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hF2i : Integrable (fun ω => F2 (Zφ R t φ ω, R.X t ω)) P := by
    refine Integrable.of_bound (hF2m.comp ((hZ.mono hGle le_rfl).prodMk hX)).aestronglyMeasurable
      cb ?_
    filter_upwards [hc1b, G2R.X_mem_K hR hℬ ht] with ω hω hXK
    have hXθ := G2R.abs_dot_le_one h𝒜 hgen (hθn ω) hXK
    simp only [hF2, Real.norm_eq_abs, abs_mul]
    have : |F1 (Zφ R t φ ω, R.X t ω)| ≤ cb := hω
    simp only [Zφ] at this ⊢
    nlinarith [abs_nonneg (F1 ((R.p t ω, R.θs t ω, φ ω), R.X t ω)),
      abs_nonneg (R.X t ω ⬝ᵥ R.θs t ω)]
  have hstepc := int_law_φ hR ht hφ hF2m.stronglyMeasurable hF2i
  -- step d: the reconstruction identity
  have hstepd : ∀ ω, ∫ x, F2 (Zφ R t φ ω, x) ∂(R.p t ω) = φ ω * (w ⬝ᵥ R.θs t ω) := by
    intro ω
    haveI := G2R.p_prob hR ht ω
    have hPD := (G2R.feas hR ht ω).2.2.2.1
    have : (fun x => F2 (Zφ R t φ ω, x)) =
        fun x => φ ω * ((w ⬝ᵥ gv (R.p t ω) x) * (x ⬝ᵥ R.θs t ω)) := by
      funext x; simp only [hF2, hF1, Zφ, G2M.V_eq]; ring
    rw [this, integral_const_mul, G2E.recon hKc (G2R.p_supp hR ht ω) hPD]
  -- assemble
  have hθhat : ∀ ω, φ ω * (w ⬝ᵥ R.thetaHat t ω) = c1 ω * R.Y t ω := fun ω => by
    rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, hc1eq]; ring
  refine ⟨?_, ?_⟩
  · simp_rw [hθhat]; exact hc1Y
  · simp_rw [hθhat]
    rw [hstepa, hstepb]
    have : ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P = ∫ ω, F2 (Zφ R t φ ω, R.X t ω) ∂P := rfl
    rw [this, hstepc]
    exact integral_congr_ae (ae_of_all _ hstepd)

end G26R

namespace G26R

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- characterization of a conditional expectation by its set integrals -/
lemma condExp_eq_of_setIntegral {G : ℕ → MeasurableSpace Ω} {t : ℕ} (hG : G t ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hgm : StronglyMeasurable[G t] g)
    (heq : ∀ s, MeasurableSet[G t] s → ∫ ω in s, f ω ∂μ = ∫ ω in s, g ω ∂μ) :
    μ[f | G t] =ᵐ[μ] g := by
  have := isFiniteMeasure_trim (μ := μ) hG
  exact (ae_eq_condExp_of_forall_setIntegral_eq hG hf (fun s _ _ => hg.integrableOn)
    (fun s hs _ => (heq s hs).symm) hgm.aestronglyMeasurable).symm

end G26R

namespace G26R

variable {d : ℕ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- **conditional unbiasedness**: `E[wᵀθ̂_t | G_t] = wᵀθ_t` -/
lemma cond_mean (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    (w : Fin d → ℝ) {cw : ℝ} (hw : ∀ᵐ ω ∂P, |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ cw)
    {cθ : ℝ} (hwθ : ∀ ω, |w ⬝ᵥ R.θs t ω| ≤ cθ) :
    P[fun ω => w ⬝ᵥ R.thetaHat t ω | R.G t] =ᵐ[P] fun ω => w ⬝ᵥ R.θs t ω := by
  have hGle := G2R.G_le hR ht
  have hθG : Measurable[R.G t] (R.θs t) := (hR t ht).1.2.2.2.2.2.2.1
  have hgm : StronglyMeasurable[R.G t] (fun ω => w ⬝ᵥ R.θs t ω) :=
    (G2R.meas_dot' measurable_const hθG).stronglyMeasurable
  have hgi : Integrable (fun ω => w ⬝ᵥ R.θs t ω) P :=
    Integrable.of_bound (hgm.mono hGle).aestronglyMeasurable cθ
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hwθ ω)
  have hfi : Integrable (fun ω => w ⬝ᵥ R.thetaHat t ω) P := by
    have := (unbiased_φ hd h𝒜 hℬ hgen hspan hR ht w hw (φ := fun _ => 1) measurable_const
      (fun _ => by simp)).1
    simpa using this
  refine condExp_eq_of_setIntegral (G := R.G) hGle hfi hgi hgm fun s hs => ?_
  have hsm : MeasurableSet s := hGle _ hs
  have hφm : Measurable[R.G t] (s.indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator hs
  have h := (unbiased_φ hd h𝒜 hℬ hgen hspan hR ht w hw hφm (fun ω => by
    simp only [Set.indicator]; split_ifs <;> simp)).2
  rw [← integral_indicator hsm, ← integral_indicator hsm]
  convert h using 2 <;> (funext ω; simp only [Set.indicator]; split_ifs <;> simp)

end G26R

namespace G26R

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- conditional moments of a predictably shifted variable -/
lemma condExp_shift {G : ℕ → MeasurableSpace Ω} {t : ℕ} (hG : G t ≤ mΩ) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) (hgm : StronglyMeasurable[G t] g)
    {cg : ℝ} (hgb : ∀ ω, |g ω| ≤ cg) :
    (μ[fun ω => f ω + g ω | G t] =ᵐ[μ] fun ω => μ[f | G t] ω + g ω) ∧
    (μ[fun ω => (f ω + g ω) ^ 2 | G t] =ᵐ[μ]
      fun ω => μ[fun ω => f ω ^ 2 | G t] ω + 2 * g ω * μ[f | G t] ω + g ω ^ 2) := by
  have hgi : Integrable g μ := Integrable.of_bound (hgm.mono hG).aestronglyMeasurable cg
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hgbd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ cg := ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb ω
  have hg2m : StronglyMeasurable[G t] fun ω => g ω ^ 2 := hgm.pow 2
  have hg2i : Integrable (fun ω => g ω ^ 2) μ :=
    Integrable.of_bound ((hgm.pow 2).mono hG).aestronglyMeasurable (cg ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb ω) 2)
  have hfg : Integrable (fun ω => 2 * g ω * f ω) μ := by
    have := hf.bdd_mul ((hgm.mono hG).aestronglyMeasurable) hgbd
    simpa [mul_assoc] using this.const_mul 2
  constructor
  · have h1 := condExp_add hf hgi (G t) (μ := μ)
    have h2 : μ[g | G t] = g := condExp_of_stronglyMeasurable hG hgm hgi
    filter_upwards [h1] with ω hω
    simp only [Pi.add_apply] at hω
    have e : (fun ω => f ω + g ω) = f + g := rfl
    rw [e, hω, h2]
  · have e : (fun ω => (f ω + g ω) ^ 2) =
        (fun ω => f ω ^ 2) + ((fun ω => 2 * g ω * f ω) + fun ω => g ω ^ 2) := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [e]
    have h1 := condExp_add hf2 (hfg.add hg2i) (G t) (μ := μ)
    have h2 := condExp_add hfg hg2i (G t) (μ := μ)
    have h3 : μ[fun ω => g ω ^ 2 | G t] = fun ω => g ω ^ 2 := condExp_of_stronglyMeasurable hG hg2m hg2i
    have h4 : μ[fun ω => 2 * g ω * f ω | G t] =ᵐ[μ] fun ω => 2 * g ω * μ[f | G t] ω := by
      have hm : StronglyMeasurable[G t] fun ω => 2 * g ω := hgm.const_mul 2
      have e0 : (fun ω => 2 * g ω * f ω) = (fun ω => 2 * g ω) * f := rfl
      rw [e0]
      have := condExp_mul_of_stronglyMeasurable_left hm (by rw [← e0]; exact hfg) hf
      filter_upwards [this] with ω hω
      rw [hω]; rfl
    filter_upwards [h1, h2, h4] with ω e1 e2 e4
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2, e4, h3]
    ring

end G26R


-- ===== Solutions.G26.RunK =====

/-! ### The loss-difference field on `K` satisfies the field interface (Lemma G.10) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

/-- the negative maximum of `X(u) = (u − a*)ᵀS` on `K` -/
noncomputable def NK (ℬ : Set (Fin d → ℝ)) (astar S : Fin d → ℝ) : ℝ :=
  negMax (Kset ℬ) S (-(astar ⬝ᵥ S))

lemma fzK (u astar S : Fin d → ℝ) : u ⬝ᵥ S + -(astar ⬝ᵥ S) = (u - astar) ⬝ᵥ S := by
  rw [sub_dotProduct]; ring

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

lemma NK_facts {astar : Fin d → ℝ} (haK : astar ∈ Kset ℬ) (S : Fin d → ℝ) {u : Fin d → ℝ}
    (hu : u ∈ Kset ℬ) :
    0 ≤ NK ℬ astar S ∧ 0 ≤ (u - astar) ⬝ᵥ S + NK ℬ astar S := by
  have hKc := G2R.Kset_compact hℬ
  have h1 := negMax_ge hKc haK S (-(astar ⬝ᵥ S))
  have h2 := negMax_ge hKc hu S (-(astar ⬝ᵥ S))
  rw [fzK] at h1 h2
  simp only [sub_self, zero_dotProduct, neg_zero] at h1
  unfold NK
  constructor <;> linarith

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

lemma Fx_mono (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n < T) : Fx R T n ≤ Fx R T (n + 1) := by
  rw [Fx_lt hn]
  unfold Fx; split_ifs with h
  · exact (hR n hn).1.2.2.2.2.2.2.2.1
  · exact G2R.G_le hR hn

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

lemma abs_dot_le_setNorm {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hgen : IsGenerator 𝒜 ℬ)
    (w : Fin d → ℝ) {x : Fin d → ℝ} (hx : x ∈ Kset ℬ) : |x ⬝ᵥ w| ≤ setNorm 𝒜 w := by
  rw [← G2R.conv_eq hgen] at hx
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} := by
    have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ w) :=
      ⟨fun x y => add_dotProduct x y w, fun c x => smul_dotProduct c x w⟩
    have : {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} =
        {v | v ⬝ᵥ w ≤ setNorm 𝒜 w} ∩ {v | -setNorm 𝒜 w ≤ v ⬝ᵥ w} := by
      ext x; simp [abs_le, and_comm]
    rw [this]
    exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
  exact convexHull_min (fun a ha => le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩) hcvx hx

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

lemma negMax_add_const {D : Set (Fin d → ℝ)} (V : Fin d → ℝ) (c k : ℝ) :
    negMax D V (c + k) = negMax D V c - k := by
  unfold negMax; ring

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

lemma setNorm_sub_le (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (x y : Fin d → ℝ) :
    setNorm 𝒜 (x - y) ≤ setNorm 𝒜 x + setNorm 𝒜 y := by
  have hc : ∀ w : Fin d → ℝ, Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := fun w => by
    simp only [dotProduct]; fun_prop
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨a, ha, rfl⟩
  show |a ⬝ᵥ (x - y)| ≤ _
  rw [dotProduct_sub]
  have h1 : |a ⬝ᵥ x| ≤ setNorm 𝒜 x := le_csSup (h𝒜.image (hc x)).bddAbove ⟨a, ha, rfl⟩
  have h2 : |a ⬝ᵥ y| ≤ setNorm 𝒜 y := le_csSup (h𝒜.image (hc y)).bddAbove ⟨a, ha, rfl⟩
  exact (abs_sub _ _).trans (add_le_add h1 h2)

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma negMaxW (astar θ : Fin d → ℝ) (C : ℝ) (n : ℕ) (ω : Ω) :
    negMax (Kset ℬ) (R.cumEst n ω) (cW 𝒜 R θ astar C n ω) =
      NK ℬ astar (R.cumEst n ω) + 2 * (C - Acum 𝒜 R θ n ω) := by
  unfold cW NK
  rw [show -(astar ⬝ᵥ R.cumEst n ω) - 2 * (C - Acum 𝒜 R θ n ω) =
    -(astar ⬝ᵥ R.cumEst n ω) + -(2 * (C - Acum 𝒜 R θ n ω)) by ring, negMax_add_const]
  ring

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

lemma norm_le (x : Fin d → ℝ) : ‖x‖ ≤ sNorm ℬ x := by
  rw [← G1L.sNorm_gen H.hgen]; exact T31.norm_le_sNorm H.ne𝒜 H.hspan H.hball x

lemma gap_pos {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (hne : a ≠ astar) : 0 < gap θ astar a := by
  have h1 : 0 < ‖a - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h2 := H.norm_le (a - astar)
  exact lt_of_lt_of_le (mul_pos H.sig_pos (lt_of_lt_of_le h1 h2)) (H.sig_spec ha)

lemma gap_le_two {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) : gap θ astar a ≤ 2 := by
  unfold gap
  rw [sub_dotProduct]
  have h1 := G2R.abs_dot_le_one H.h𝒜 H.hgen H.hθ ha
  have h2 := G2R.abs_dot_le_one H.h𝒜 H.hgen H.hθ H.haK
  linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]

end Sharp

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

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

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma kappa_facts (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n < T) (ω : Ω) :
    0 ≤ setNorm 𝒜 (R.θs n ω - θ) ∧ setNorm 𝒜 (R.θs n ω - θ) ≤ 2 := by
  have hne𝒜 := H.ne𝒜
  have hθn := (hR n hn).2.2.2.2.2
  refine ⟨setNorm_nonneg H.h𝒜 hne𝒜 _, ?_⟩
  have := setNorm_sub_le H.h𝒜 hne𝒜 (R.θs n ω) θ
  linarith [hθn ω, H.hθ]

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

/-- the curvature remainder of the inverse Taylor step -/
lemma inv_curv (P : ℕ) (β B x y τ : ℝ) (hτ : 0 < τ) (hy : τ ≤ y) (hβ : 0 ≤ β) (hx : 1 ≤ x)
    (hB8 : 8 * ((P : ℝ) + 1) ≤ B) (hτβ : 40 * ((P : ℝ) + 1) * β * x ≤ τ ^ 2) :
    (P : ℝ) * (P + 1) * y⁻¹ ^ (P + 2) * (10 * β + 2 * y ^ 2 / (B * x)) ≤ P / (2 * x) * y⁻¹ ^ P := by
  have hy0 : 0 < y := lt_of_lt_of_le hτ hy
  have hB0 : 0 < B := by have : (0 : ℝ) ≤ P := Nat.cast_nonneg P; linarith
  have hx0 : 0 < x := by linarith
  set z := y⁻¹ ^ P with hz
  have hz0 : 0 ≤ z := by positivity
  have e1 : y⁻¹ ^ (P + 2) * (10 * β + 2 * y ^ 2 / (B * x)) = z * (10 * β / y ^ 2 + 2 / (B * x)) := by
    rw [hz, pow_add, inv_pow y 2]; field_simp
  have h1 : 10 * β / y ^ 2 ≤ 10 * β / τ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hτ.le hy 2)
  have h2 : ((P : ℝ) + 1) * (10 * β / τ ^ 2) ≤ 1 / (4 * x) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h3 : ((P : ℝ) + 1) * (2 / (B * x)) ≤ 1 / (4 * x) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h4 : ((P : ℝ) + 1) * (10 * β / y ^ 2 + 2 / (B * x)) ≤ 1 / (2 * x) := by
    have : 1 / (4 * x) + 1 / (4 * x) = 1 / (2 * x) := by field_simp; ring
    have h5 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (P : ℝ) + 1)
    nlinarith
  calc (P : ℝ) * (P + 1) * y⁻¹ ^ (P + 2) * (10 * β + 2 * y ^ 2 / (B * x))
      = (P : ℝ) * z * (((P : ℝ) + 1) * (10 * β / y ^ 2 + 2 / (B * x))) := by
        rw [mul_assoc, e1]; ring
    _ ≤ (P : ℝ) * z * (1 / (2 * x)) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = P / (2 * x) * z := by ring

/-- **one step of the killed inverse moment recursion (G.432)–(G.438)** -/
lemma SI.inv_step [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {P : ℕ} (hP : 2 ≤ P)
    (hPB : (P : ℝ) * (3 / B) ≤ 1 / 2) (hB8 : 8 * ((P : ℝ) + 1) ≤ B) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    {n : ℕ} (hmn : m ≤ n) (hnN : n < N)
    (hdr : ∀ᵐ ω ∂μ, ω ∈ I n → Δ ≤ μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω)
    (hτβ : 40 * ((P : ℝ) + 1) * β n * ((n : ℝ) + 1) ≤ τ n ^ 2) (hβ : 0 ≤ β n) :
    kinv μ Y I P (n + 1) ≤ (1 + P / (2 * ((n : ℝ) + 1))) * kinv μ Y I P n -
      P * Δ * kinv μ Y I (P + 1) n := by
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  have hτ := S.τpos n
  set x : ℝ := (n : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by simp only [x]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hFn := S.Fle n hnN.le
  have hJ := S.Im n hnN.le
  have hJm := S.Im' hnN.le
  have hYm := S.Ym n hnN.le
  have hYm' := S.Ym' hnN.le
  have hYm1' := S.Ym' (n := n + 1) hnN
  obtain ⟨r0, hr0⟩ := S.env n hnN.le
  obtain ⟨r1, hr1⟩ := S.env (n + 1) hnN
  let H : Ω → ℝ := (I n).indicator (fun ω => (Y (n + 1) ω)⁻¹ ^ P)
  let g0 : Ω → ℝ := (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P)
  let g1 : Ω → ℝ := (I n).indicator (fun ω => -(P : ℝ) * (Y n ω)⁻¹ ^ (P + 1))
  let g2 : Ω → ℝ := (I n).indicator (fun ω => (P : ℝ) * (P + 1) * (Y n ω)⁻¹ ^ (P + 2))
  let ξ : Ω → ℝ := fun ω => Y (n + 1) ω - Y n ω
  let b1 : Ω → ℝ := (I n).indicator (fun ω => -(P : ℝ) * Δ * (Y n ω)⁻¹ ^ (P + 1))
  let V : Ω → ℝ := fun ω => 10 * β n + 2 * Y n ω ^ 2 / (B * x)
  set cb : ℝ := (2 / τ n) ^ P + (τ n)⁻¹ ^ P + P * (τ n)⁻¹ ^ (P + 1) +
    P * (P + 1) * (τ n)⁻¹ ^ (P + 2) + (|r1| + |r0|) + P * Δ * (τ n)⁻¹ ^ (P + 1) +
    (10 * β n + 2 * r0 ^ 2 / (B * x)) with hcb
  -- pointwise facts on the alive set
  have hfacts : ∀ᵐ ω ∂μ, ω ∈ I n → τ n ≤ Y n ω ∧ |ξ ω| ≤ 3 / B * Y n ω ∧ Y n ω / 2 ≤ Y (n + 1) ω := by
    filter_upwards [S.low n hmn hnN.le, S.mag n hmn hnN] with ω h1 h2 hI
    have hy := h1 hI
    have hm := h2 hI
    refine ⟨hy, by simp only [ξ]; rw [show 3 / B * Y n ω = 3 * Y n ω / B by ring]; exact hm, ?_⟩
    have : 3 * Y n ω / B ≤ Y n ω / 2 := by
      rw [div_le_div_iff₀ hB0 (by norm_num)]; nlinarith
    have := (abs_le.1 hm).1
    linarith
  have hbd : ∀ᵐ ω ∂μ, |H ω| ≤ cb ∧ |g0 ω| ≤ cb ∧ |g1 ω| ≤ cb ∧ |g2 ω| ≤ cb ∧ |ξ ω| ≤ cb ∧
      |b1 ω| ≤ cb ∧ |V ω| ≤ cb := by
    filter_upwards [hfacts, hr0, hr1] with ω hf h0 h1
    have p1 : 0 ≤ (2 / τ n) ^ P := by positivity
    have p2 : 0 ≤ (τ n)⁻¹ ^ P := by positivity
    have p3 : 0 ≤ (P : ℝ) * (τ n)⁻¹ ^ (P + 1) := by positivity
    have p4 : 0 ≤ (P : ℝ) * (P + 1) * (τ n)⁻¹ ^ (P + 2) := by positivity
    have p5 : 0 ≤ |r1| + |r0| := by positivity
    have p6 : 0 ≤ (P : ℝ) * Δ * (τ n)⁻¹ ^ (P + 1) := by positivity
    have p7 : 0 ≤ 10 * β n + 2 * r0 ^ 2 / (B * x) := by positivity
    have tV : |V ω| ≤ 10 * β n + 2 * r0 ^ 2 / (B * x) := by
      simp only [V]
      rw [abs_of_nonneg (by positivity)]
      have : Y n ω ^ 2 ≤ r0 ^ 2 := by
        have := sq_le_sq' (abs_le.1 h0).1 (abs_le.1 h0).2; linarith
      gcongr
    have tξ : |ξ ω| ≤ |r1| + |r0| := by
      simp only [ξ]
      exact le_trans (abs_sub _ _) (add_le_add (h1.trans (le_abs_self _)) (h0.trans (le_abs_self _)))
    by_cases hI : ω ∈ I n
    · obtain ⟨hy, -, hy1⟩ := hf hI
      have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
      have hinv : (Y n ω)⁻¹ ≤ (τ n)⁻¹ := inv_anti₀ hτ hy
      have hinv1 : (Y (n + 1) ω)⁻¹ ≤ 2 / τ n := by
        rw [show 2 / τ n = (τ n / 2)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) (by linarith)
      have hY1 : 0 < Y (n + 1) ω := by linarith
      simp only [H, g0, g1, g2, b1, Set.indicator_of_mem hI]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [abs_of_nonneg (by positivity)]
        have := pow_le_pow_left₀ (by positivity) hinv1 P; simp only [cb]; linarith
      · rw [abs_of_nonneg (by positivity)]
        have := pow_le_pow_left₀ (by positivity) hinv P; simp only [cb]; linarith
      · rw [abs_mul, abs_neg, Nat.abs_cast, abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (P + 1))
          (Nat.cast_nonneg P)
        simp only [cb]; linarith
      · rw [abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (P + 2))
          (by positivity : (0 : ℝ) ≤ P * (P + 1))
        simp only [cb]; linarith
      · simp only [cb]; linarith
      · rw [abs_mul, abs_mul, abs_neg, Nat.abs_cast, abs_of_nonneg hΔ, abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (P + 1))
          (by positivity : (0 : ℝ) ≤ P * Δ)
        simp only [cb]; linarith
      · simp only [cb]; linarith
    · simp only [H, g0, g1, g2, b1, Set.indicator_of_notMem hI, abs_zero]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [cb] <;> linarith
  have hpt : ∀ᵐ ω ∂μ, ω ∈ I n → H ω ≤ g0 ω + g1 ω * ξ ω + g2 ω * ξ ω ^ 2 := by
    filter_upwards [hfacts] with ω hf hI
    obtain ⟨hy, hξ, -⟩ := hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
    have hT := C37.inv_pow_taylor (Y n ω) (ξ ω) (3 / B) P hP hY0 (by positivity) hξ hPB
    simp only [H, g0, g1, g2, Set.indicator_of_mem hI]
    have e1 : Y (n + 1) ω = Y n ω + ξ ω := by simp only [ξ]; ring
    rw [e1, inv_pow, inv_pow, inv_pow, inv_pow]
    rw [one_div, one_div] at hT
    have e2 : (P : ℝ) * ξ ω / Y n ω ^ (P + 1) = (P : ℝ) * (Y n ω ^ (P + 1))⁻¹ * ξ ω := by
      field_simp
    have e3 : (P : ℝ) * (P + 1) * ξ ω ^ 2 / Y n ω ^ (P + 2) =
        (P : ℝ) * (P + 1) * (Y n ω ^ (P + 2))⁻¹ * ξ ω ^ 2 := by field_simp
    rw [e2, e3] at hT
    linarith
  have hdr' : ∀ᵐ ω ∂μ, ω ∈ I n → g1 ω * μ[ξ | F n] ω ≤ b1 ω := by
    filter_upwards [hdr, hfacts] with ω h hf hI
    obtain ⟨hy, -, -⟩ := hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
    simp only [g1, b1, Set.indicator_of_mem hI]
    have hd := h hI
    have hc : 0 ≤ (P : ℝ) * (Y n ω)⁻¹ ^ (P + 1) := by positivity
    have : (P : ℝ) * (Y n ω)⁻¹ ^ (P + 1) * Δ ≤ (P : ℝ) * (Y n ω)⁻¹ ^ (P + 1) * μ[ξ | F n] ω :=
      mul_le_mul_of_nonneg_left hd hc
    linarith
  have hse : ∀ᵐ ω ∂μ, ω ∈ I n → μ[fun ω => ξ ω ^ 2 | F n] ω ≤ V ω := by
    filter_upwards [S.sec n hmn hnN] with ω h hI
    exact h hI
  have hg2n : ∀ᵐ ω ∂μ, ω ∈ I n → 0 ≤ g2 ω := by
    filter_upwards [hfacts] with ω hf hI
    obtain ⟨hy, -, -⟩ := hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
    simp only [g2, Set.indicator_of_mem hI]; positivity
  have hst := pstep (μ := μ) (F := F) (n := n) hFn hJ (H := H) (g0 := g0) (g1 := g1) (g2 := g2)
    (ξ := ξ) (b1 := b1) (V := V)
    (((hYm1'.inv.pow_const P).indicator hJm).aestronglyMeasurable)
    (((hYm'.inv.pow_const P).indicator hJm).aestronglyMeasurable)
    (((hYm.inv.pow_const _).const_mul _).indicator hJ).stronglyMeasurable
    (((hYm.inv.pow_const _).const_mul _).indicator hJ).stronglyMeasurable
    ((hYm1'.sub hYm').aestronglyMeasurable)
    ((((hYm'.inv.pow_const _).const_mul _).indicator hJm).aestronglyMeasurable)
    ((measurable_const.add ((measurable_const.mul (hYm'.pow_const 2)).div_const _)).aestronglyMeasurable)
    hbd hpt hdr' hse hg2n
  -- compare both sides with the killed moments
  have hL : kinv μ Y I P (n + 1) ≤ ∫ ω, (I n).indicator H ω ∂μ := by
    have hLi := S.kinv_int (n := n + 1) (by omega) hnN P
    have hHi : Integrable ((I n).indicator H) μ :=
      (Integrable.of_bound (((hYm1'.inv.pow_const P).indicator hJm).aestronglyMeasurable) cb
        (by filter_upwards [hbd] with ω h; rw [Real.norm_eq_abs]; exact h.1)).indicator hJm
    refine integral_mono_ae hLi hHi ?_
    filter_upwards [hfacts] with ω hf
    by_cases h1 : ω ∈ I (n + 1)
    · have hI := S.Imono n h1
      simp only [H, Set.indicator_of_mem h1, Set.indicator_of_mem hI, le_refl]
    · rw [Set.indicator_of_notMem h1]
      by_cases hI : ω ∈ I n
      · obtain ⟨hy, -, hy1⟩ := hf hI
        have : 0 < Y (n + 1) ω := by linarith
        simp only [H, Set.indicator_of_mem hI]; positivity
      · simp [H, Set.indicator_of_notMem hI]
  have hR : ∫ ω, (I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ ≤
      (1 + P / (2 * x)) * kinv μ Y I P n - P * Δ * kinv μ Y I (P + 1) n := by
    have i1 := S.kinv_int hmn hnN.le P
    have i2 := S.kinv_int hmn hnN.le (P + 1)
    have hRi : Integrable ((I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω)) μ := by
      refine Integrable.of_bound ?_ (cb + cb + cb * cb) ?_
      · exact (((((hYm'.inv.pow_const P).indicator hJm).add
          (((hYm'.inv.pow_const _).const_mul _).indicator hJm)).add
          ((((hYm'.inv.pow_const _).const_mul _).indicator hJm).mul
            (measurable_const.add ((measurable_const.mul (hYm'.pow_const 2)).div_const _)))).indicator
              hJm).aestronglyMeasurable
      · filter_upwards [hbd] with ω h
        obtain ⟨-, h0, -, h2, -, hb, hV⟩ := h
        rw [Real.norm_eq_abs]
        by_cases hI : ω ∈ I n
        · rw [Set.indicator_of_mem hI]
          calc |g0 ω + b1 ω + g2 ω * V ω| ≤ |g0 ω| + |b1 ω| + |g2 ω| * |V ω| := by
                rw [← abs_mul]
                exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
            _ ≤ cb + cb + cb * cb := by
                have hc0 := le_trans (abs_nonneg _) h0
                have := mul_le_mul h2 hV (abs_nonneg _) hc0
                linarith
        · rw [Set.indicator_of_notMem hI, abs_zero]
          have := le_trans (abs_nonneg _) h0
          positivity
    have hRi2 : Integrable (fun ω => (1 + P / (2 * x)) * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P) ω -
        P * Δ * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ (P + 1)) ω) μ :=
      (i1.const_mul _).sub (i2.const_mul _)
    calc ∫ ω, (I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ
        ≤ ∫ ω, ((1 + P / (2 * x)) * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P) ω -
            P * Δ * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ (P + 1)) ω) ∂μ := by
          refine integral_mono_ae hRi hRi2 ?_
          filter_upwards [hfacts] with ω hf
          by_cases hI : ω ∈ I n
          · obtain ⟨hy, -, -⟩ := hf hI
            have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
            simp only [g0, b1, g2, V, Set.indicator_of_mem hI]
            have hc := inv_curv P (β n) B x (Y n ω) (τ n) hτ hy hβ hx1 hB8 hτβ
            have e : (1 + P / (2 * x)) * (Y n ω)⁻¹ ^ P = (Y n ω)⁻¹ ^ P + P / (2 * x) * (Y n ω)⁻¹ ^ P := by
              ring
            rw [e]
            have e2 : -(P : ℝ) * Δ * (Y n ω)⁻¹ ^ (P + 1) = -(P * Δ * (Y n ω)⁻¹ ^ (P + 1)) := by ring
            rw [e2]
            linarith only [hc]
          · simp [g0, b1, g2, Set.indicator_of_notMem hI]
      _ = (1 + P / (2 * x)) * kinv μ Y I P n - P * Δ * kinv μ Y I (P + 1) n := by
          rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
          rfl
  have hHH : ∫ ω, (I n).indicator H ω ∂μ ≤
      ∫ ω, (I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ := hst
  linarith

end G26


-- ===== Solutions.G26.SIFreeze =====

/-! ### Freezing a scalar interface at a predictable success rule (Lemma G.29, (G.653)–(G.659)) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

/-- a common freezing time for two processes: the current time, or the first failure of the rule -/
lemma frz_two {E1 E2 : Type*} (X1 : ℕ → Ω → E1) (X2 : ℕ → Ω → E2) (A : ℕ → Set Ω) (n : ℕ)
    (ω : Ω) : ∃ i ≤ n, (i = n ∨ ω ∉ A i) ∧ frz X1 A n ω = X1 i ω ∧ frz X2 A n ω = X2 i ω := by
  classical
  by_cases hs : n = 0 ∨ ω ∈ survS A (n - 1)
  · exact ⟨n, le_rfl, Or.inl rfl, frz_eq X1 A n ω hs, frz_eq X2 A n ω hs⟩
  · push Not at hs
    obtain ⟨hn0, hns⟩ := hs
    have hex : ∃ j, ω ∉ A j := by
      by_contra h
      push Not at h
      exact hns (by simp only [survS, Set.mem_iInter]; exact fun i _ => h i)
    set i := Nat.find hex
    have hfail : ω ∉ A i := Nat.find_spec hex
    have hin : i ≤ n - 1 := by
      by_contra hlt
      push Not at hlt
      apply hns
      simp only [survS, Set.mem_iInter, Finset.mem_range]
      intro j hj
      by_contra hj'
      exact absurd (Nat.find_min' hex hj') (by omega)
    have hsurv : i = 0 ∨ ω ∈ survS A (i - 1) := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj
        by_contra hj'
        exact absurd (Nat.find_min' hex hj') (by omega)
    exact ⟨i, by omega, Or.inr hfail, frz_stop X1 A hsurv hfail n (by omega),
      frz_stop X2 A hsurv hfail n (by omega)⟩

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

/-- the alive sets of the frozen process: alive at the freezing time -/
def frzI (I : ℕ → Set Ω) (A : ℕ → Set Ω) (n : ℕ) : Set Ω :=
  {ω | frz (fun j ω => (I j).indicator (fun _ => (1 : ℝ)) ω) A n ω = 1}

lemma frzI_before {I A : ℕ → Set Ω} {u : ℕ} (hA : ∀ n < u, A n = univ) : frzI I A u = I u := by
  ext ω
  simp only [frzI, mem_setOf_eq, frz_before _ hA]
  by_cases h : ω ∈ I u
  · simp [Set.indicator_of_mem h, h]
  · simp [Set.indicator_of_notMem h, h]

lemma ind_eq_one {S : Set Ω} {ω : Ω} : S.indicator (fun _ => (1 : ℝ)) ω = 1 ↔ ω ∈ S := by
  by_cases h : ω ∈ S
  · simp [Set.indicator_of_mem h, h]
  · simp [Set.indicator_of_notMem h, h]

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

lemma Fmono_chain (hFm : ∀ n < N, F n ≤ F (n + 1)) {i n : ℕ} (hin : i ≤ n) (hn : n ≤ N) :
    F i ≤ F n := by
  induction n, hin using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih => exact (ih (by omega)).trans (hFm n (by omega))

lemma frz_measR {E : Type*} [MeasurableSpace E] (hFm : ∀ n < N, F n ≤ F (n + 1)) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ N, MeasurableSet[F n] (A n)) {X : ℕ → Ω → E} (hX : ∀ n ≤ N, Measurable[F n] (X n)) :
    ∀ n ≤ N, Measurable[F n] (frz X A n) := by
  intro n hn
  induction n with
  | zero => exact hX 0 hn
  | succ n ih =>
    have hmono := hFm n (by omega)
    have hS : MeasurableSet[F n] (survS A n) := by
      unfold survS
      refine Finset.measurableSet_biInter _ fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact Fmono_chain hFm (by omega : i ≤ n) (by omega) _ (hA i (by omega))
    classical
    show Measurable[F (n + 1)] fun ω => if ω ∈ survS A n then X (n + 1) ω else frz X A n ω
    exact Measurable.ite (hmono _ hS) (hX (n + 1) hn) ((ih (by omega)).mono hmono le_rfl)

lemma tau_chain (hτ : ∀ n, m ≤ n → n < N → τ n ≤ τ (n + 1)) {i : ℕ} (hmi : m ≤ i) (hiN : i ≤ N) :
    τ m ≤ τ i := by
  induction i, hmi using Nat.le_induction with
  | base => exact le_rfl
  | succ i hmi ih => exact (ih (by omega)).trans (hτ i hmi (by omega))

lemma SI.frz_low (S : SI μ F Y I m N τ β B) {A : ℕ → Set Ω} (hAm : ∀ n < m, A n = univ)
    (hτ : ∀ n, m ≤ n → n < N → τ n ≤ τ (n + 1)) {n : ℕ} (hmn : m ≤ n) (hnN : n ≤ N) :
    ∀ᵐ ω ∂μ, ω ∈ frzI I A n → τ m ≤ frz Y A n ω := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1), m ≤ (i : ℕ) → ω ∈ I i → τ i ≤ Y i ω :=
    ae_all_iff.2 fun i => by
      by_cases hmi : m ≤ (i : ℕ)
      · filter_upwards [S.low i hmi (by have := i.2; omega)] with ω h _ hI using h hI
      · exact ae_of_all _ fun ω h => absurd h hmi
  filter_upwards [hall] with ω hω hI
  obtain ⟨i, hi, hor, h1, h2⟩ := frz_two Y (fun j ω => (I j).indicator (fun _ => (1 : ℝ)) ω) A n ω
  have hIi : ω ∈ I i := by
    have : frz (fun j ω => (I j).indicator (fun _ => (1 : ℝ)) ω) A n ω = 1 := hI
    rw [h2] at this; exact ind_eq_one.1 this
  have hmi : m ≤ i := by
    rcases hor with h | h
    · omega
    · by_contra hlt; push Not at hlt; exact h (by rw [hAm i hlt]; trivial)
  rw [h1]
  exact (tau_chain hτ hmi (by omega)).trans (hω ⟨i, by omega⟩ hmi hIi)

/-- the increment of the frozen process is the original increment on the surviving set -/
lemma frz_incr (Y : ℕ → Ω → ℝ) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    frz Y A (n + 1) ω - frz Y A n ω = (survS A n).indicator (fun ω => Y (n + 1) ω - Y n ω) ω := by
  classical
  by_cases h : ω ∈ survS A n
  · rw [Set.indicator_of_mem h, frz_eq_of_mem Y A h]
    simp only [frz, if_pos h]
  · rw [Set.indicator_of_notMem h, frz_succ_of_notMem Y A h, sub_self]

lemma frzI_survS {I A : ℕ → Set Ω} {n : ℕ} {ω : Ω} (hω : ω ∈ frzI I A n) (hs : ω ∈ survS A n) :
    ω ∈ I n := by
  have : frz (fun j ω => (I j).indicator (fun _ => (1 : ℝ)) ω) A n ω = 1 := hω
  rw [frz_eq_of_mem _ A hs] at this
  exact ind_eq_one.1 this

/-- **freezing a scalar interface**: freezing at a predictable success rule (with no success before
`m`) and killing only before success preserves the interface with the constant level `τ_m` -/
theorem SI.freeze [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B)
    (hFm : ∀ n < N, F n ≤ F (n + 1)) {A : ℕ → Set Ω} (hA : ∀ n ≤ N, MeasurableSet[F n] (A n))
    (hAm : ∀ n < m, A n = univ) (hτ : ∀ n, m ≤ n → n < N → τ n ≤ τ (n + 1)) (hB : 0 < B)
    (hβ : ∀ n, 0 ≤ β n) :
    SI μ F (frz Y A) (frzI I A) m N (fun _ => τ m) β B where
  Fle := S.Fle
  Ym := frz_measR hFm hA S.Ym
  Im := fun n hn => by
    have hX : ∀ j ≤ N, Measurable[F j] (fun ω => (I j).indicator (fun _ => (1 : ℝ)) ω) :=
      fun j hj => measurable_const.indicator (S.Im j hj)
    exact frz_measR hFm hA hX n hn (measurableSet_singleton 1)
  Imono := by
    classical
    intro n ω hω
    have h1 : frz (fun j ω => (I j).indicator (fun _ => (1 : ℝ)) ω) A (n + 1) ω = 1 := hω
    show frz (fun j ω => (I j).indicator (fun _ => (1 : ℝ)) ω) A n ω = 1
    by_cases h : ω ∈ survS A n
    · simp only [frz, if_pos h] at h1
      rw [frz_eq_of_mem _ A h]
      exact ind_eq_one.2 (S.Imono n (ind_eq_one.1 h1))
    · rw [frz_succ_of_notMem _ A h] at h1; exact h1
  τpos := fun _ => S.τpos m
  low := fun n hmn hnN => S.frz_low hAm hτ hmn hnN
  env := by
    intro n hn
    have hb : ∀ i : Fin (n + 1), ∃ r : ℝ, ∀ᵐ ω ∂μ, |Y i ω| ≤ r := fun i =>
      S.env i (by have := i.2; omega)
    choose r hr using hb
    refine ⟨∑ i, |r i|, ?_⟩
    filter_upwards [ae_all_iff.2 hr] with ω hω
    obtain ⟨i, hi, -, h1, -⟩ := frz_two Y Y A n ω
    rw [h1]
    calc |Y i ω| ≤ r ⟨i, by omega⟩ := hω ⟨i, by omega⟩
      _ ≤ |r ⟨i, by omega⟩| := le_abs_self _
      _ ≤ ∑ i, |r i| := Finset.single_le_sum (f := fun i => |r i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _)
  mag := by
    intro n hmn hnN
    filter_upwards [S.mag n hmn hnN, S.frz_low hAm hτ hmn hnN.le] with ω hmag hlow hω
    rw [frz_incr]
    by_cases h : ω ∈ survS A n
    · rw [Set.indicator_of_mem h, frz_eq_of_mem Y A h]
      exact hmag (frzI_survS hω h)
    · rw [Set.indicator_of_notMem h, abs_zero]
      have h1 := S.τpos m
      have h2 := hlow hω
      exact div_nonneg (by linarith) hB.le
  sec := by
    intro n hmn hnN
    have hS : MeasurableSet[F n] (survS A n) := by
      unfold survS
      refine Finset.measurableSet_biInter _ fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact Fmono_chain hFm (by omega : i ≤ n) hnN.le _ (hA i (by omega))
    obtain ⟨r0, hr0⟩ := S.env n hnN.le
    obtain ⟨r1, hr1⟩ := S.env (n + 1) hnN
    have hint : Integrable (fun ω => (Y (n + 1) ω - Y n ω) ^ 2) μ := by
      refine Integrable.of_bound (((S.Ym' hnN).sub (S.Ym' hnN.le)).pow_const 2).aestronglyMeasurable
        ((r1 + r0) ^ 2) ?_
      filter_upwards [hr0, hr1] with ω h0 h1
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add h1 h0)) 2
    have e1 : (fun ω => (frz Y A (n + 1) ω - frz Y A n ω) ^ 2) =
        (survS A n).indicator (fun ω => (Y (n + 1) ω - Y n ω) ^ 2) := by
      funext ω; rw [frz_incr]
      by_cases h : ω ∈ survS A n
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [e1]
    have hce := condExp_indicator (m := F n) (μ := μ) hint hS
    filter_upwards [hce, S.sec n hmn hnN, S.frz_low hAm hτ hmn hnN.le] with ω h1 h2 hlow hω
    rw [h1]
    by_cases h : ω ∈ survS A n
    · rw [Set.indicator_of_mem h, frz_eq_of_mem Y A h]
      exact h2 (frzI_survS hω h)
    · rw [Set.indicator_of_notMem h]
      have := hβ n
      have hB' : 0 < B * ((n : ℝ) + 1) := mul_pos hB (by positivity)
      have : 0 ≤ 2 * frz Y A n ω ^ 2 / (B * ((n : ℝ) + 1)) := div_nonneg (by positivity) hB'.le
      linarith

/-- the frozen process has nonnegative drift where the original drift is nonnegative -/
lemma SI.frz_drift [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B)
    (hFm : ∀ n < N, F n ≤ F (n + 1)) {A : ℕ → Set Ω} (hA : ∀ n ≤ N, MeasurableSet[F n] (A n))
    {n : ℕ} (hnN : n < N)
    (hdr : ∀ᵐ ω ∂μ, ω ∈ I n → 0 ≤ μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω) :
    ∀ᵐ ω ∂μ, ω ∈ frzI I A n → 0 ≤ μ[fun ω => frz Y A (n + 1) ω - frz Y A n ω | F n] ω := by
  have hS : MeasurableSet[F n] (survS A n) := by
    unfold survS
    refine Finset.measurableSet_biInter _ fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    exact Fmono_chain hFm (by omega : i ≤ n) hnN.le _ (hA i (by omega))
  obtain ⟨r0, hr0⟩ := S.env n hnN.le
  obtain ⟨r1, hr1⟩ := S.env (n + 1) hnN
  have hint : Integrable (fun ω => Y (n + 1) ω - Y n ω) μ := by
    refine Integrable.of_bound ((S.Ym' hnN).sub (S.Ym' hnN.le)).aestronglyMeasurable (r1 + r0) ?_
    filter_upwards [hr0, hr1] with ω h0 h1
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add h1 h0)
  have e1 : (fun ω => frz Y A (n + 1) ω - frz Y A n ω) =
      (survS A n).indicator (fun ω => Y (n + 1) ω - Y n ω) := funext fun ω => frz_incr Y A n ω
  rw [e1]
  have hce := condExp_indicator (m := F n) (μ := μ) hint hS
  filter_upwards [hce, hdr] with ω h1 h2 hω
  rw [h1]
  by_cases h : ω ∈ survS A n
  · rw [Set.indicator_of_mem h]; exact h2 (frzI_survS hω h)
  · rw [Set.indicator_of_notMem h]

end G26

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

/-- **the frozen inverse moment grows at most like `((v+1)/(u+1))^P` (G.655)–(G.659)** -/
theorem SI.frz_kinv [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B)
    (hFm : ∀ n < N, F n ≤ F (n + 1)) {A : ℕ → Set Ω} (hA : ∀ n ≤ N, MeasurableSet[F n] (A n))
    (hAm : ∀ n < m, A n = univ) (hτ : ∀ n, m ≤ n → n < N → τ n ≤ τ (n + 1)) (hB : 0 < B)
    (hβ : ∀ n, 0 ≤ β n) {P : ℕ} (hP : 2 ≤ P) (hPB : (P : ℝ) * (3 / B) ≤ 1 / 2)
    (hB8 : 8 * ((P : ℝ) + 1) ≤ B) {u v : ℕ} (hmu : m ≤ u) (hAu : ∀ n < u, A n = univ)
    (huv : u ≤ v) (hvN : v ≤ N)
    (hdr0 : ∀ n, u ≤ n → n < v → ∀ᵐ ω ∂μ, ω ∈ I n →
      0 ≤ μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω)
    (hτβ : ∀ n, u ≤ n → n < v → 40 * ((P : ℝ) + 1) * β n * ((n : ℝ) + 1) ≤ τ m ^ 2) :
    kinv μ (frz Y A) (frzI I A) P v ≤ (((v : ℝ) + 1) / ((u : ℝ) + 1)) ^ P * kinv μ Y I P u := by
  have S' := S.freeze hFm hA hAm hτ hB hβ
  have hu0 : kinv μ (frz Y A) (frzI I A) P u = kinv μ Y I P u := by
    unfold kinv; rw [frz_before Y hAu, frzI_before hAu]
  have hk0 : ∀ n, m ≤ n → n ≤ N → 0 ≤ kinv μ (frz Y A) (frzI I A) P n := by
    intro n hmn hnN
    unfold kinv
    refine integral_nonneg_of_ae ?_
    filter_upwards [S'.low n hmn hnN] with ω h
    by_cases hI : ω ∈ frzI I A n
    · rw [Set.indicator_of_mem hI]
      have := h hI
      have := S.τpos m
      exact pow_nonneg (inv_nonneg.2 (by linarith)) _
    · rw [Set.indicator_of_notMem hI]; simp
  suffices key : ∀ j, u + j ≤ v →
      kinv μ (frz Y A) (frzI I A) P (u + j) ≤
        ((((u + j : ℕ) : ℝ) + 1) / ((u : ℝ) + 1)) ^ P * kinv μ Y I P u by
    have := key (v - u) (by omega)
    rwa [show u + (v - u) = v by omega] at this
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.add_zero]
    rw [hu0, div_self (by positivity), one_pow, one_mul]
  | succ j ih =>
    intro hj
    have hn : u + j < v := by omega
    have hstep := S'.inv_step hP hPB hB8 (Δ := 0) le_rfl (n := u + j) (by omega) (by omega)
      (S.frz_drift hFm hA (by omega) (hdr0 (u + j) (by omega) hn)) (hτβ (u + j) (by omega) hn)
      (hβ _)
    simp only [mul_zero, zero_mul, sub_zero] at hstep
    have ih' := ih (by omega)
    have hk := hk0 (u + j) (by omega) (by omega)
    have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
    set x : ℝ := ((u + j : ℕ) : ℝ) + 1 with hx
    have hx1 : 1 ≤ x := by simp only [hx]; linarith [(Nat.cast_nonneg (u + j) : (0:ℝ) ≤ _)]
    have hbern : 1 + (P : ℝ) / (2 * x) ≤ ((x + 1) / x) ^ P := by
      have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / x by
        have : 0 ≤ 1 / x := by positivity
        linarith) P
      have e : (x + 1) / x = 1 + 1 / x := by field_simp
      rw [e]
      have : (P : ℝ) / (2 * x) ≤ P * (1 / x) := by
        rw [div_le_iff₀ (by positivity)]; field_simp; nlinarith [(Nat.cast_nonneg P : (0:ℝ) ≤ P)]
      linarith
    have hkv : 0 ≤ kinv μ Y I P u := by rw [← hu0]; exact hk0 u hmu (by omega)
    calc kinv μ (frz Y A) (frzI I A) P (u + (j + 1))
        ≤ (1 + P / (2 * x)) * kinv μ (frz Y A) (frzI I A) P (u + j) := by
          rw [show u + (j + 1) = u + j + 1 by omega]; exact hstep
      _ ≤ (1 + P / (2 * x)) * ((x / ((u : ℝ) + 1)) ^ P * kinv μ Y I P u) :=
          mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ ((x + 1) / x) ^ P * ((x / ((u : ℝ) + 1)) ^ P * kinv μ Y I P u) :=
          mul_le_mul_of_nonneg_right hbern (by positivity)
      _ = ((((u + (j + 1) : ℕ) : ℝ) + 1) / ((u : ℝ) + 1)) ^ P * kinv μ Y I P u := by
          have e : (((u + (j + 1) : ℕ) : ℝ) + 1) = x + 1 := by simp only [hx]; push_cast; ring
          rw [e, ← mul_assoc, ← mul_pow]
          congr 2
          field_simp

end G26


-- ===== Solutions.G26.RunSI =====

/-! ### Compensated per-action scalar processes (Lemma G.29, (G.635)–(G.641)) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Ecor_succ (θ w : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    Ecor R θ w (n + 1) ω = Ecor R θ w n ω + w ⬝ᵥ (R.θs n ω - θ) := by
  unfold Ecor; rw [Finset.sum_range_succ]

lemma YF_succ (θ astar : Fin d → ℝ) (C : ℝ) (τ : ℕ → ℝ) (a : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    YF R θ astar C τ a (n + 1) ω - YF R θ astar C τ a n ω =
      (a - astar) ⬝ᵥ R.thetaHat n ω - (a - astar) ⬝ᵥ (R.θs n ω - θ) + 2 * (τ (n + 1) - τ n) := by
  simp only [YF, cumEst_succ, Ecor_succ, dotProduct_add]; ring

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma abs_dot_two {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (w : Fin d → ℝ) :
    |(a - astar) ⬝ᵥ w| ≤ 2 * setNorm 𝒜 w := by
  rw [sub_dotProduct]
  have h1 := abs_dot_le_setNorm H.h𝒜 H.hgen w ha
  have h2 := abs_dot_le_setNorm H.h𝒜 H.hgen w H.haK
  linarith [abs_sub (a ⬝ᵥ w) (astar ⬝ᵥ w)]

lemma Ecor_le {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (n : ℕ) (ω : Ω) :
    |Ecor R θ (a - astar) n ω| ≤ 2 * Acum 𝒜 R θ n ω := by
  unfold Ecor Acum
  rw [Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => H.abs_dot_two ha _)

lemma YF_low {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) {C : ℝ} {τ : ℕ → ℝ} {n : ℕ} {ω : Ω}
    (hA0 : 0 ≤ Acum 𝒜 R θ n ω) (hAC : Acum 𝒜 R θ n ω ≤ C)
    (hQ : negMax (Kset ℬ) (R.cumEst n ω) (cW 𝒜 R θ astar C n ω) ≤ τ n) :
    τ n ≤ YF R θ astar C τ a n ω ∧
      (a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω) ≤ YF R θ astar C τ a n ω ∧
      0 ≤ (a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω) := by
  rw [negMaxW] at hQ
  obtain ⟨hN0, hNu⟩ := NK_facts H.hd H.hℬ H.hgen H.hspan H.haK (R.cumEst n ω) ha
  have hE := H.Ecor_le (R := R) ha n ω
  unfold YF
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.1 hE).2]
  · linarith [(abs_le.1 hE).2]
  · linarith

/-- the drift of the compensated per-action variable is at least the gap -/
lemma runF_drift (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} {a : Fin d → ℝ} (ha : a ∈ Kset ℬ)
    {τ : ℕ → ℝ} (hτmono : ∀ n, τ n ≤ τ (n + 1)) (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {n : ℕ}
    (hnT : n < T) :
    ∀ᵐ ω ∂P, gap θ astar a ≤
      P[fun ω => YF R θ astar C τ a (n + 1) ω - YF R θ astar C τ a n ω | Fx R T n] ω := by
  have hGle := G2R.G_le hR hnT
  have hθn := (hR n hnT).2.2.2.2.2
  have hcw : ∀ᵐ ω ∂P, |(a - astar) ⬝ᵥ gv (R.p n ω) (R.X n ω)| ≤
      2 * (gbeta d (n + 1) + G2R.rho d n / gB d) := by
    filter_upwards [G2R.v_bound_ae H.hd H.hℬ H.hgen H.hspan hR hnT] with ω h
    exact h.2 a ha astar H.haK
  have hcm := cond_mean H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR hnT (a - astar) hcw (cθ := 2)
    (fun ω => by
      rw [sub_dotProduct]
      have h1 := G2R.abs_dot_le_one H.h𝒜 H.hgen (hθn ω) ha
      have h2 := G2R.abs_dot_le_one H.h𝒜 H.hgen (hθn ω) H.haK
      exact (abs_sub _ _).trans (by linarith))
  set g : Ω → ℝ := fun ω => -((a - astar) ⬝ᵥ (R.θs n ω - θ)) + 2 * (τ (n + 1) - τ n) with hg
  have hgm : StronglyMeasurable[R.G n] g :=
    (((G2R.meas_dot' measurable_const (((hR n hnT).1.2.2.2.2.2.2.1).sub measurable_const)).neg).add
      measurable_const).stronglyMeasurable
  have hgb : ∀ ω, |g ω| ≤ 6 := fun ω => by
    have h1 : |(a - astar) ⬝ᵥ (R.θs n ω - θ)| ≤ 4 := by
      refine (H.abs_dot_two ha _).trans ?_
      obtain ⟨-, h2⟩ := H.kappa_facts hR hnT ω
      linarith
    have h2 : |2 * (τ (n + 1) - τ n)| ≤ 2 := by
      rw [abs_mul, abs_two, abs_of_nonneg (by linarith [hτmono n])]; linarith [hδ n]
    simp only [hg]
    have := abs_add_le (-((a - astar) ⬝ᵥ (R.θs n ω - θ))) (2 * (τ (n + 1) - τ n))
    rw [abs_neg] at this
    linarith
  have hfi : Integrable (fun ω => (a - astar) ⬝ᵥ R.thetaHat n ω) P := by
    have := (unbiased_φ H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR hnT (a - astar) hcw (φ := fun _ => 1)
      measurable_const (fun _ => by simp)).1
    simpa using this
  have hf2 : Integrable (fun ω => ((a - astar) ⬝ᵥ R.thetaHat n ω) ^ 2) P := by
    refine Integrable.of_bound (hfi.aestronglyMeasurable.pow 2)
      ((2 * (gbeta d (n + 1) + G2R.rho d n / gB d)) ^ 2) ?_
    filter_upwards [hcw] with ω h
    rw [Real.norm_eq_abs, abs_pow, GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
    have hY := (hR n hnT).2.2.2.2.1.1 ω
    exact pow_le_pow_left₀ (by positivity) ((mul_le_of_le_one_left (abs_nonneg _) hY).trans h) 2
  have hsh := (condExp_shift (G := R.G) hGle hfi hf2 hgm hgb).1
  have e1 : (fun ω => YF R θ astar C τ a (n + 1) ω - YF R θ astar C τ a n ω) =
      fun ω => (a - astar) ⬝ᵥ R.thetaHat n ω + g ω :=
    funext fun ω => by rw [YF_succ]; simp only [hg]; ring
  rw [e1, Fx_lt hnT]
  filter_upwards [hsh, hcm] with ω h1 h2
  rw [h1, h2]
  simp only [hg, gap]
  have : (a - astar) ⬝ᵥ R.θs n ω - (a - astar) ⬝ᵥ (R.θs n ω - θ) = (a - astar) ⬝ᵥ θ := by
    rw [dotProduct_sub]; ring
  linarith [hτmono n]

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


-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the absolute maximum of the loss-difference field on `K` -/
noncomputable def RX (ℬ : Set (Fin d → ℝ)) (astar : Fin d → ℝ) (S : Fin d → ℝ) : ℝ :=
  absMax (Kset ℬ) S (-(astar ⬝ᵥ S))

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

lemma Dfar_compact (ε : ℝ) : IsCompact (Dfar ℬ θ astar ε) := by
  have : Dfar ℬ θ astar ε = Kset ℬ ∩ {a | ε ≤ (a - astar) ⬝ᵥ θ} := rfl
  rw [this]
  exact H.Kc.inter_right (isClosed_le continuous_const (by simp only [dotProduct]; fun_prop))

lemma Dfar_convex (ε : ℝ) : Convex ℝ (Dfar ℬ θ astar ε) := by
  have : Dfar ℬ θ astar ε = Kset ℬ ∩ {a | ε ≤ (a - astar) ⬝ᵥ θ} := rfl
  rw [this]
  refine Kconv.inter ?_
  have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ θ) :=
    ⟨fun x y => add_dotProduct x y θ, fun c x => smul_dotProduct c x θ⟩
  have : {a : Fin d → ℝ | ε ≤ (a - astar) ⬝ᵥ θ} = {a | ε + astar ⬝ᵥ θ ≤ a ⬝ᵥ θ} := by
    ext a; simp only [mem_setOf_eq, sub_dotProduct]; constructor <;> intro h <;> linarith
  rw [this]
  exact convex_halfSpace_ge hl _

variable (he : Function.Surjective e)
include he

end Sharp

end G26G


-- ===== Solutions.G26.RefFar =====

/-! ### Far-region reference errors: success freezing and contraction (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the success rule: frozen at the first round `≥ u` of the alive window with a small far value -/
def succA (𝒜 ℬ : Set (Fin d → ℝ)) (R : GRun d Ω) (θ astar : Fin d → ℝ) (C : ℝ) (τ : ℕ → ℝ)
    (m0 u : ℕ) (Df : Set (Fin d → ℝ)) (hb : ℝ) (n : ℕ) : Set Ω :=
  if n < u then univ else
    (IW 𝒜 ℬ R θ astar C τ m0 n ∩
      {ω | -hb ≤ negMax Df (R.cumEst n ω) (-(astar ⬝ᵥ R.cumEst n ω))})ᶜ

/-- the vector part of the compensated variable -/
noncomputable def Vg (R : GRun d Ω) (θ : Fin d → ℝ) (n : ℕ) (ω : Ω) : Fin d → ℝ :=
  R.cumEst n ω - ∑ j ∈ Finset.range n, (R.θs j ω - θ)

/-- the scalar part of the compensated variable -/
noncomputable def cg (R : GRun d Ω) (θ astar : Fin d → ℝ) (C : ℝ) (τ : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  -(astar ⬝ᵥ Vg R θ n ω) + 2 * C + 2 * τ n

lemma YF_aff (θ astar : Fin d → ℝ) (C : ℝ) (τ : ℕ → ℝ) (a : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    YF R θ astar C τ a n ω = a ⬝ᵥ Vg R θ n ω + cg R θ astar C τ n ω := by
  unfold YF cg Vg Ecor
  rw [← dotProduct_sum, dotProduct_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
  ring

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma succA_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hcor : IsCorruptedG P 𝒜 θ C T R)
    {τ : ℕ → ℝ} (hτpos : ∀ n, 0 < τ n) (hτmono : ∀ n, τ n ≤ τ (n + 1))
    (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {m0 u N : ℕ} (hN : N ≤ T)
    (hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ τ n) {Df : Set (Fin d → ℝ)}
    (hDc : IsCompact Df) (hDne : Df.Nonempty) (hb : ℝ) :
    ∀ n ≤ N, MeasurableSet[Fx R T n] (succA 𝒜 ℬ R θ astar C τ m0 u Df hb n) := by
  intro n hn
  unfold succA
  split_ifs with h
  · exact MeasurableSet.univ
  · refine MeasurableSet.compl ?_
    have S := H.runF_SI hR hcor H.haK hτpos hτmono hδ hN hτB
    refine (S.Im n hn).inter ?_
    have hS := cumEst_Fx hR (hn.trans hN)
    exact measurableSet_le measurable_const
      (G26.negMax_meas hDc hDne hS (G2R.meas_dot' measurable_const hS).neg)

lemma Vg_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n ≤ T) :
    Measurable[Fx R T n] (Vg R θ n) := by
  unfold Vg
  refine (cumEst_Fx hR hn).sub (Finset.measurable_sum _ fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  have hθj : Measurable[R.G j] (R.θs j) := (hR j (by omega)).1.2.2.2.2.2.2.1
  have hle : R.G j ≤ Fx R T n := by
    have := Fx_mono' hR (le_of_lt hj') hn
    rwa [Fx_lt (by omega : j < T)] at this
  exact (hθj.mono hle le_rfl).sub measurable_const

/-- the per-action frozen inverse moment at the end of the block (G.659) -/
lemma kinv_far (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hcor : IsCorruptedG P 𝒜 θ C T R)
    {τ : ℕ → ℝ} (hτpos : ∀ n, 0 < τ n) (hτmono : ∀ n, τ n ≤ τ (n + 1))
    (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {m0 u : ℕ} (h2uT : 2 * u ≤ T) (hm0u : m0 ≤ u)
    (hhalf : 2 * ((m0 : ℝ) + 1) ≤ (u : ℝ) + 1)
    (hmP : ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((m0 : ℝ) + 1))
    (hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ τ n)
    (hτm : 2 * (((4 * kk d : ℕ) : ℝ) + 1) ≤ τ m0)
    (hτβ : ∀ n, m0 ≤ n → n < 2 * u →
      40 * (((4 * kk d : ℕ) : ℝ) + 1) * gbeta d (n + 1) * ((n : ℝ) + 1) ≤ τ m0 ^ 2)
    {A : ℕ → Set Ω} (hA : ∀ n ≤ 2 * u, MeasurableSet[Fx R T n] (A n)) (hAu : ∀ n < u, A n = univ)
    {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) {ε : ℝ} (hε : 0 < ε) (haε : ε ≤ gap θ astar a) :
    kinv P (frz (YF R θ astar C τ a) A) (frzI (IW 𝒜 ℬ R θ astar C τ m0) A) (4 * kk d) (2 * u) ≤
      2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d) := by
  obtain ⟨hk2, hP4, hev, hdP, hB⟩ := kk_facts d
  have hB0 := G2R.gB_pos (d := d)
  have hβ0 : ∀ n, 0 ≤ gbeta d (n + 1) := fun n => (G2R.gbeta_pos H.hd (n + 1)).le
  have S := H.runF_SI hR hcor ha hτpos hτmono hδ (m0 := m0) (N := 2 * u) h2uT hτB
  have hg := H.gap_pos ha (by
    intro h; rw [h] at haε; unfold gap at haε; simp at haε; linarith)
  have hg2 := H.gap_le_two ha
  have hP2 : 2 ≤ 4 * kk d := by omega
  have hPB : ((4 * kk d : ℕ) : ℝ) * (3 / gB d) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hB0 (by norm_num)]
    have : 2 ^ 20 * ((4 * kk d : ℕ) : ℝ) ≤ gB d := hB
    nlinarith
  have hB8 : 8 * (((4 * kk d : ℕ) : ℝ) + 1) ≤ gB d := by
    have : 2 ^ 20 * ((4 * kk d : ℕ) : ℝ) ≤ gB d := hB
    have : (1 : ℝ) ≤ ((4 * kk d : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 4 * kk d)
    nlinarith
  have hτmono' : Monotone τ := monotone_nat_of_le_succ hτmono
  have hinv := S.inv_moment hP2 hPB hB8 (Δ := gap θ astar a) hg (t := u) hm0u (by omega) hhalf
    (by nlinarith) hmP
    (fun n _ hn => by
      filter_upwards [H.runF_drift hR (C := C) ha hτmono hδ (n := n) (by omega)] with ω h _
      exact h)
    (fun n hmn hn => by
      have h1 := hτβ n hmn (by omega)
      have h2 : τ m0 ≤ τ n := hτmono' hmn
      have h3 : 0 < τ m0 := hτpos m0
      nlinarith)
    hβ0
  have hFm : ∀ n < 2 * u, Fx R T n ≤ Fx R T (n + 1) := fun n hn => Fx_mono hR (by omega)
  have hfr := S.frz_kinv hFm hA (fun n hn => hAu n (by omega)) (fun n _ _ => hτmono n) hB0 hβ0
    hP2 hPB hB8 (u := u) (v := 2 * u) hm0u hAu (by omega) le_rfl
    (fun n _ hn => by
      filter_upwards [H.runF_drift hR (C := C) ha hτmono hδ (n := n) (by omega)] with ω h _
      exact le_trans hg.le h)
    (fun n hun hn => hτβ n (le_trans hm0u hun) hn)
  have hkv : 0 ≤ kinv P (YF R θ astar C τ a) (IW 𝒜 ℬ R θ astar C τ m0) (4 * kk d) u := by
    unfold kinv
    refine integral_nonneg_of_ae ?_
    filter_upwards [S.low u hm0u (by omega)] with ω h
    by_cases hI : ω ∈ IW 𝒜 ℬ R θ astar C τ m0 u
    · rw [Set.indicator_of_mem hI]
      have := h hI; have := hτpos u
      exact pow_nonneg (inv_nonneg.2 (by linarith)) _
    · rw [Set.indicator_of_notMem hI]; simp
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hr : ((((2 * u : ℕ) : ℝ) + 1) / ((u : ℝ) + 1)) ≤ 2 := by
    rw [div_le_iff₀ hu1]; push_cast; linarith
  have hr0 : 0 ≤ ((((2 * u : ℕ) : ℝ) + 1) / ((u : ℝ) + 1)) := by positivity
  have h4 : (4 / (((u : ℝ) + 1) * gap θ astar a)) ^ (4 * kk d) ≤
      (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d) := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left haε hu1.le
  calc _ ≤ ((((2 * u : ℕ) : ℝ) + 1) / ((u : ℝ) + 1)) ^ (4 * kk d) *
        kinv P (YF R θ astar C τ a) (IW 𝒜 ℬ R θ astar C τ m0) (4 * kk d) u := hfr
    _ ≤ 2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * gap θ astar a)) ^ (4 * kk d) :=
        mul_le_mul (pow_le_pow_left₀ hr0 hr _) hinv hkv (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **far-region reference errors in a block (G.653)–(G.666)** -/
theorem far_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R)
    {τ : ℕ → ℝ} (hτpos : ∀ n, 0 < τ n) (hτmono : ∀ n, τ n ≤ τ (n + 1))
    (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {m0 u : ℕ} (h2uT : 2 * u ≤ T) (hm0u : m0 ≤ u)
    (hhalf : 2 * ((m0 : ℝ) + 1) ≤ (u : ℝ) + 1)
    (hmP : ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((m0 : ℝ) + 1))
    (hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ τ n)
    (hτm : 2 * (((4 * kk d : ℕ) : ℝ) + 1) ≤ τ m0)
    (hτβ : ∀ n, m0 ≤ n → n < 2 * u →
      40 * (((4 * kk d : ℕ) : ℝ) + 1) * gbeta d (n + 1) * ((n : ℝ) + 1) ≤ τ m0 ^ 2)
    {ε : ℝ} (hε : 0 < ε) {hbv : ℝ} (hbC : hbv + 4 * C ≤ 2 * τ (2 * u))
    {ρ : ℝ} (hρa : 4 * τ (2 * u) ≤ ρ) (hρb : 2 * (4 * C + 2 * τ (2 * u)) ≤ ρ) :
    P.real {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ∃ a ∈ Dfar ℬ θ astar ε,
        (a - astar) ⬝ᵥ R.cumEst s ω ≤ hbv} ≤
      P.real (IW 𝒜 ℬ R θ astar C τ m0 (2 * u))ᶜ +
        2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) +
        (2 * (4 * τ (2 * u))) ^ (4 * kk d) * (ρ / (4 * τ (2 * u))) ^ d *
          (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d)) := by
  classical
  obtain ⟨hk2, hP4, hev, hdP, hB⟩ := kk_facts d
  have hB0 := G2R.gB_pos (d := d)
  have hτ2 := hτpos (2 * u)
  have hρ0 : 0 < ρ := by linarith
  have hratio : 1 ≤ ρ / (4 * τ (2 * u)) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hT0 : 0 ≤ 2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) :=
    div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (cK_nonneg d))
      (pow_nonneg (by positivity) _)) (pow_nonneg hρ0.le _)
  have hT1 : 0 ≤ (2 * (4 * τ (2 * u))) ^ (4 * kk d) * (ρ / (4 * τ (2 * u))) ^ d *
      (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (div_nonneg (by norm_num)
        (mul_nonneg (by positivity) hε.le)) _))
  by_cases hDne : (Dfar ℬ θ astar ε).Nonempty
  swap
  · have : {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ∃ a ∈ Dfar ℬ θ astar ε,
        (a - astar) ⬝ᵥ R.cumEst s ω ≤ hbv} = ∅ := by
      ext ω; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨s, -, -, a, ha, -⟩; exact hDne ⟨a, ha⟩
    rw [this, measureReal_empty]
    have := measureReal_nonneg (μ := P) (s := (IW 𝒜 ℬ R θ astar C τ m0 (2 * u))ᶜ)
    linarith
  set Df := Dfar ℬ θ astar ε with hDfdef
  have hDc := H.Dfar_compact ε
  have hDv := H.Dfar_convex ε
  set A := succA 𝒜 ℬ R θ astar C τ m0 u Df hbv with hAdef
  have hAT := H.succA_meas hR hcor hτpos hτmono hδ (u := u) (N := T) le_rfl hτB hDc hDne hbv
  have hA : ∀ n ≤ 2 * u, MeasurableSet[Fx R T n] (A n) := fun n hn => hAT n (hn.trans h2uT)
  have hAu : ∀ n < u, A n = univ := fun n hn => by simp only [hAdef, succA, if_pos hn]
  have hFm : ∀ n < 2 * u, Fx R T n ≤ Fx R T (n + 1) := fun n hn => Fx_mono hR (by omega)
  have hτmono' : Monotone τ := monotone_nat_of_le_succ hτmono
  -- the frozen affine field
  set V : Ω → Fin d → ℝ := frz (Vg R θ) A (2 * u) with hV
  set c : Ω → ℝ := frz (cg R θ astar C τ) A (2 * u) with hc
  have hVm : Measurable V := ((frz_measR hFm hA (fun n hn => H.Vg_meas hR (hn.trans h2uT)))
    (2 * u) le_rfl).mono (Fx_le hR h2uT) le_rfl
  have hcm : Measurable c := by
    have hcg : ∀ n ≤ 2 * u, Measurable[Fx R T n] (cg R θ astar C τ n) := fun n hn =>
      ((G2R.meas_dot' measurable_const (H.Vg_meas hR (hn.trans h2uT))).neg.add
        measurable_const).add measurable_const
    exact ((frz_measR hFm hA hcg) (2 * u) le_rfl).mono (Fx_le hR h2uT) le_rfl
  have hfield : ∀ x ω, frz (YF R θ astar C τ x) A (2 * u) ω = x ⬝ᵥ V ω + c ω := by
    intro x ω
    obtain ⟨e1, -, -, -⟩ := frz_fidx (YF R θ astar C τ x) A (2 * u) ω
    obtain ⟨e2, -, -, -⟩ := frz_fidx (Vg R θ) A (2 * u) ω
    obtain ⟨e3, -, -, -⟩ := frz_fidx (cg R θ astar C τ) A (2 * u) ω
    rw [e1, hV, hc, e2, e3, YF_aff]
  -- good corruption histories
  set G0 : Set Ω := {ω | ∀ n ≤ T, 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C} with hG0
  have hG0m : MeasurableSet G0 := by
    have : G0 = ⋂ n : ℕ, {ω | n ≤ T → 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C} := by
      ext ω; simp [hG0]
    rw [this]
    refine MeasurableSet.iInter fun n => ?_
    by_cases hn : n ≤ T
    · have hAm := (Acum_Fx H.h𝒜 H.ne𝒜 hR θ hn).mono (Fx_le hR hn) le_rfl
      have e1 : {ω | n ≤ T → 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C} =
          {ω | 0 ≤ Acum 𝒜 R θ n ω} ∩ {ω | Acum 𝒜 R θ n ω ≤ C} := by
        ext ω; simp [hn]
      rw [e1]
      exact (measurableSet_le measurable_const hAm).inter (measurableSet_le hAm measurable_const)
    · have e1 : {ω | n ≤ T → 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C} = univ := by
        ext ω; simp [hn]
      rw [e1]; exact MeasurableSet.univ
  have hG0ae : ∀ᵐ ω ∂P, ω ∈ G0 := Acum_le H.h𝒜 H.ne𝒜 hcor
  -- the success event
  have hSm : MeasurableSet (survS A (2 * u)) := by
    unfold survS
    refine Finset.measurableSet_biInter _ fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    exact Fx_le hR (by omega : i ≤ T) _ (hA i (by omega))
  set E := (survS A (2 * u))ᶜ ∩ G0 with hE
  have hEm : MeasurableSet E := hSm.compl.inter hG0m
  -- the stopping facts on `E`
  have hstop : ∀ ω ∈ E, u ≤ fidx A (2 * u) ω ∧ fidx A (2 * u) ω ≤ 2 * u ∧
      ω ∈ IW 𝒜 ℬ R θ astar C τ m0 (fidx A (2 * u) ω) ∧
      -hbv ≤ negMax Df (R.cumEst (fidx A (2 * u) ω) ω)
        (-(astar ⬝ᵥ R.cumEst (fidx A (2 * u) ω) ω)) := by
    intro ω hω
    obtain ⟨-, hi, hor, hbefore⟩ := frz_fidx (Vg R θ) A (2 * u) ω
    set i := fidx A (2 * u) ω
    have hfail : ω ∉ A i := by
      rcases hor with h | h
      · rw [h]
        intro hA2
        apply hω.1
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj
        rcases Nat.lt_or_ge j (2 * u) with hj' | hj'
        · exact hbefore j (by omega)
        · rw [show j = 2 * u by omega]; exact hA2
      · exact h
    have hui : u ≤ i := by
      by_contra hlt; push Not at hlt
      exact hfail (by rw [hAu i hlt]; trivial)
    have hnot : ¬ i < u := by omega
    simp only [hAdef, succA, if_neg hnot, mem_compl_iff, not_not] at hfail
    exact ⟨hui, hi, hfail.1, hfail.2⟩
  -- positivity, minimum and maximum on `E`
  have hpos : ∀ ω ∈ E, ∀ x ∈ Df, 0 < x ⬝ᵥ V ω + c ω := by
    intro ω hω x hx
    obtain ⟨hui, hi, hIW, -⟩ := hstop ω hω
    rw [← hfield, (frz_fidx _ A (2 * u) ω).1]
    obtain ⟨hA0, hAC⟩ := hω.2 _ (hi.trans h2uT)
    have := (H.YF_low hx.1 hA0 hAC (hIW _ (le_trans hm0u hui) le_rfl)).1
    linarith [hτpos (fidx A (2 * u) ω)]
  have hmin : ∀ ω ∈ E, ∃ x0 ∈ Df, x0 ⬝ᵥ V ω + c ω ≤ 4 * τ (2 * u) := by
    intro ω hω
    obtain ⟨hui, hi, hIW, hneg⟩ := hstop ω hω
    set i := fidx A (2 * u) ω
    obtain ⟨x0, hx0, hx0e⟩ := negMax_mem hDc hDne (R.cumEst i ω) (-(astar ⬝ᵥ R.cumEst i ω))
    refine ⟨x0, hx0, ?_⟩
    rw [← hfield, (frz_fidx _ A (2 * u) ω).1]
    obtain ⟨hA0, hAC⟩ := hω.2 _ (hi.trans h2uT)
    have hE := H.Ecor_le (R := R) hx0.1 i ω
    have hX : (x0 - astar) ⬝ᵥ R.cumEst i ω ≤ hbv := by
      rw [fzK] at hx0e; linarith
    have hτi : τ i ≤ τ (2 * u) := hτmono' hi
    unfold YF
    linarith [(abs_le.1 hE).1]
  set b : Ω → ℝ := fun ω => RX ℬ astar (frz R.cumEst A (2 * u) ω) + 4 * C + 2 * τ (2 * u) with hbdef
  have hmax : ∀ ω ∈ E, ∀ x ∈ Df, x ⬝ᵥ V ω + c ω ≤ b ω := by
    intro ω hω x hx
    obtain ⟨hui, hi, hIW, -⟩ := hstop ω hω
    set i := fidx A (2 * u) ω
    rw [← hfield, (frz_fidx _ A (2 * u) ω).1]
    obtain ⟨hA0, hAC⟩ := hω.2 _ (hi.trans h2uT)
    have hE := H.Ecor_le (R := R) hx.1 i ω
    have hτi : τ i ≤ τ (2 * u) := hτmono' hi
    have hR1 : (x - astar) ⬝ᵥ R.cumEst i ω ≤ RX ℬ astar (frz R.cumEst A (2 * u) ω) := by
      rw [(frz_fidx R.cumEst A (2 * u) ω).1]
      have := abs_le_absMax H.Kc hx.1 (R.cumEst i ω) (-(astar ⬝ᵥ R.cumEst i ω))
      rw [fzK] at this
      exact (le_abs_self _).trans this
    simp only [hbdef]
    unfold YF
    linarith [(abs_le.1 hE).1]
  have hbm : Measurable b := by
    have hS := ((frz_measR hFm hA (fun n hn => cumEst_Fx hR (hn.trans h2uT))) (2 * u)
      le_rfl).mono (Fx_le hR h2uT) le_rfl
    exact ((G26.absMax_meas H.Kc ⟨astar, H.haK⟩ hS
      (G2R.meas_dot' measurable_const hS).neg).add measurable_const).add measurable_const
  -- the inverse moments on `E`
  have hinv : ∀ x ∈ Df, ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal
      ((|x ⬝ᵥ V ω + c ω| ^ (4 * kk d))⁻¹)) ω ∂P ≤
      ENNReal.ofReal (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d)) := by
    intro x hx
    have hK := H.kinv_far hR hcor hτpos hτmono hδ h2uT hm0u hhalf hmP hτB hτm hτβ hA hAu hx.1 hε hx.2
    have S := H.runF_SI hR hcor hx.1 hτpos hτmono hδ (m0 := m0) (N := 2 * u) h2uT hτB
    have S' := S.freeze hFm hA (fun n hn => hAu n (by omega)) (fun n _ _ => hτmono n) hB0
      (fun n => (G2R.gbeta_pos H.hd (n + 1)).le)
    have hint := S'.kinv_int (n := 2 * u) (by omega) le_rfl (4 * kk d)
    have hlow := S'.low (2 * u) (by omega) le_rfl
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal hK)
    unfold kinv
    rw [ofReal_integral_eq_lintegral_ofReal hint (by
      filter_upwards [hlow] with ω h
      by_cases hI : ω ∈ frzI (IW 𝒜 ℬ R θ astar C τ m0) A (2 * u)
      · rw [Set.indicator_of_mem hI]; have := h hI; have := hτpos m0
        exact pow_nonneg (inv_nonneg.2 (by linarith)) _
      · rw [Set.indicator_of_notMem hI]; simp)]
    refine lintegral_mono_ae ?_
    filter_upwards [hlow] with ω h
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      obtain ⟨hui, hi, hIW, -⟩ := hstop ω hω
      have hIfr : ω ∈ frzI (IW 𝒜 ℬ R θ astar C τ m0) A (2 * u) := by
        show frz (fun j ω => (IW 𝒜 ℬ R θ astar C τ m0 j).indicator (fun _ => (1 : ℝ)) ω) A
          (2 * u) ω = 1
        rw [(frz_fidx _ A (2 * u) ω).1]
        exact ind_eq_one.2 hIW
      rw [Set.indicator_of_mem hIfr, ← hfield]
      have hy := h hIfr
      have hy0 : 0 < frz (YF R θ astar C τ x) A (2 * u) ω := by linarith [hτpos m0]
      rw [abs_of_pos hy0, inv_pow]
    · rw [Set.indicator_of_notMem hω]; positivity
  have hcs := contr_split hDc hDv hDne hVm hcm hEm (a := 4 * τ (2 * u)) (by linarith) hbm
    (4 * kk d) hpos hmin hmax hρa (K := 2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d))
    (by positivity) hinv
  -- the tail of `b`
  have hbt : P.real {ω | ρ < b ω} ≤
      2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) := by
    have hAll : ∀ n ≤ T, MeasurableSet[Fx R T n] (A n) := hAT
    have hKe := H.absK_env hR hAll h2uT
    have IK := (runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK).freeze hAll (by norm_num)
      (by norm_num) (fun n => (G2R.gbeta_pos H.hd (n + 1)).le) hB0 (J' := fun _ => univ)
      (fun _ _ => MeasurableSet.univ) (fun _ => subset_rfl) (fun _ => subset_univ _)
    have hint := IK.absMax_int h2uT (4 * kk d)
    have h0 : ∀ᵐ ω ∂P, 0 ≤ absMax (Kset ℬ) (frz R.cumEst A (2 * u) ω)
        (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A (2 * u) ω) ^ (4 * kk d) := by
      filter_upwards [IK.N0 (2 * u) h2uT] with ω h
      exact pow_nonneg (h.trans (negMax_le_absMax _ _)) _
    have hc2 : (0 : ℝ) < (ρ / 2) ^ (4 * kk d) := pow_pos (by linarith) _
    have hm := markov' h0 hint (c := (ρ / 2) ^ (4 * kk d)) hc2
    have hsub : {ω | ρ < b ω} ⊆ {ω | (ρ / 2) ^ (4 * kk d) ≤ absMax (Kset ℬ)
        (frz R.cumEst A (2 * u) ω) (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A (2 * u) ω) ^
          (4 * kk d)} := by
      intro ω hω
      have hω' : ρ < b ω := hω
      simp only [hbdef] at hω'
      have e1 : RX ℬ astar (frz R.cumEst A (2 * u) ω) = absMax (Kset ℬ)
          (frz R.cumEst A (2 * u) ω) (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A (2 * u) ω) := by
        unfold RX
        rw [(frz_fidx R.cumEst A (2 * u) ω).1,
          (frz_fidx (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A (2 * u) ω).1]
      show (ρ / 2) ^ (4 * kk d) ≤ _
      rw [← e1]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    refine (measureReal_mono hsub).trans (hm.trans ?_)
    have e : (ρ / 2) ^ (4 * kk d) = ρ ^ (4 * kk d) / 2 ^ (4 * kk d) := div_pow ρ 2 _
    rw [e, div_div_eq_mul_div]
    have h2p : (0 : ℝ) < 2 ^ (4 * kk d) := pow_pos (by norm_num) _
    have : (0 : ℝ) < ρ ^ (4 * kk d) := pow_pos hρ0 _
    refine div_le_div_of_nonneg_right ?_ this.le
    calc (∫ ω, absMax (Kset ℬ) (frz R.cumEst A (2 * u) ω)
          (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A (2 * u) ω) ^ (4 * kk d) ∂P) *
          2 ^ (4 * kk d)
        = 2 ^ (4 * kk d) * ∫ ω, absMax (Kset ℬ) (frz R.cumEst A (2 * u) ω)
          (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A (2 * u) ω) ^ (4 * kk d) ∂P := mul_comm _ _
      _ ≤ 2 ^ (4 * kk d) * (cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d)) :=
          mul_le_mul_of_nonneg_left hKe h2p.le
      _ = 2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) := (mul_assoc _ _ _).symm
  -- the inclusion of the far event
  have hincl : ∀ᵐ ω ∂P, ω ∈ {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ∃ a ∈ Df,
      (a - astar) ⬝ᵥ R.cumEst s ω ≤ hbv} → ω ∈ (IW 𝒜 ℬ R θ astar C τ m0 (2 * u))ᶜ ∪ E := by
    filter_upwards [hG0ae] with ω hG hω
    obtain ⟨s, hus, hs2, a, ha, hX⟩ := hω
    by_cases hIW : ω ∈ IW 𝒜 ℬ R θ astar C τ m0 (2 * u)
    · right
      refine ⟨fun hsurv => ?_, hG⟩
      have hAs : ω ∈ A s := by
        simp only [survS, Set.mem_iInter, Finset.mem_range] at hsurv
        exact hsurv s (by omega)
      have hnot : ¬ s < u := by omega
      simp only [hAdef, succA, if_neg hnot, mem_compl_iff] at hAs
      apply hAs
      refine ⟨fun j hj1 hj2 => hIW j hj1 (by omega), ?_⟩
      have := negMax_ge hDc ha (R.cumEst s ω) (-(astar ⬝ᵥ R.cumEst s ω))
      rw [fzK] at this
      show -hbv ≤ negMax Df (R.cumEst s ω) (-(astar ⬝ᵥ R.cumEst s ω))
      linarith
    · exact Or.inl hIW
  have hrd : (ρ / (4 * τ (2 * u))) ^ rdim Df ≤ (ρ / (4 * τ (2 * u))) ^ d :=
    pow_le_pow_right₀ hratio (rdim_le _)
  have hbt' : P.real {ω | ρ < b ω} + (2 * (4 * τ (2 * u))) ^ (4 * kk d) *
      (ρ / (4 * τ (2 * u))) ^ rdim Df * (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d)) ≤
      2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) +
        (2 * (4 * τ (2 * u))) ^ (4 * kk d) * (ρ / (4 * τ (2 * u))) ^ d *
          (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d)) := by
    gcongr
  calc _ ≤ P.real ((IW 𝒜 ℬ R θ astar C τ m0 (2 * u))ᶜ ∪ E) := measureReal_le_of_ae hincl
    _ ≤ P.real (IW 𝒜 ℬ R θ astar C τ m0 (2 * u))ᶜ + P.real E := measureReal_union_le _ _
    _ ≤ _ := by linarith

end Sharp

end G26G


theorem _root_.solution : type_of% @G26G.Sharp.far_prob := @G26G.Sharp.far_prob
