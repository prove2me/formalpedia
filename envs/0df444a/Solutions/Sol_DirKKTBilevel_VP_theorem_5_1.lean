-- Prove2me | solution 1 for DirKKTBilevel.VP.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:37:47.133697+00:00
-- url     : https://prove2.me/submissions/d7dd9abc-5684-4d55-bdb9-0cabcd8a9317

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Theorems.Thm_DirKKTBilevel_VP_theorem_3_1
import Theorems.Thm_DirKKTBilevel_VP_dir_sum_rule
import Theorems.Thm_DirKKTBilevel_VP_dirSubdiff_nonempty

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional
open scoped InnerProductSpace

namespace DirKKT51Aux

open DirKKTBilevel.VP

/-- Points `t • y` with `t ≥ 0` small and `y` near `u` lie in the directional neighbourhood. -/
lemma cone_key {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] (u : X) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η > 0, ∀ (t : ℝ) (y : X), 0 ≤ t → t < η → ‖y - u‖ < η →
      t • y ∈ DirKKTBilevel.VP.dirNbhd ε δ u := by
  by_cases hu : u = 0
  · subst hu
    refine ⟨min 1 ε, lt_min one_pos hε, fun t y ht htη hy => ?_⟩
    simp only [sub_zero] at hy
    refine ⟨?_, by simp⟩
    rw [norm_smul, Real.norm_of_nonneg ht]
    have h1 : ‖y‖ ≤ 1 := le_trans hy.le (min_le_left _ _)
    have h2 : t < ε := lt_of_lt_of_le htη (min_le_right _ _)
    calc t * ‖y‖ ≤ t * 1 := mul_le_mul_of_nonneg_left h1 ht
      _ < ε := by linarith
  · have hN : 0 < ‖u‖ := norm_pos_iff.mpr hu
    set N := ‖u‖ with hNdef
    refine ⟨min (min 1 (ε / (N + 1))) (δ * N / (2 + δ)), ?_, fun t y ht htη hy => ?_⟩
    · refine lt_min (lt_min one_pos (div_pos hε (by linarith))) (div_pos (by positivity) (by linarith))
    have hη1 : ‖y - u‖ < 1 := lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_left _ _))
    have hη2 : t < ε / (N + 1) := lt_of_lt_of_le htη (le_trans (min_le_left _ _) (min_le_right _ _))
    have hη3 : ‖y - u‖ < δ * N / (2 + δ) := lt_of_lt_of_le hy (min_le_right _ _)
    have hyle : ‖y‖ ≤ N + ‖y - u‖ := by
      have := norm_add_le (y - u) u
      simp only [sub_add_cancel] at this
      linarith
    have hyge : N - ‖y - u‖ ≤ ‖y‖ := by
      have := norm_sub_norm_le u (u - y)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg ht]
      have : t * ‖y‖ ≤ t * (N + 1) := mul_le_mul_of_nonneg_left (by linarith) ht
      have h3 : t * (N + 1) < ε := by
        rw [lt_div_iff₀ (by linarith)] at hη2; linarith
      linarith
    · have key : ‖N • y - ‖y‖ • u‖ ≤ δ * ‖y‖ * N := by
        have e : N • y - ‖y‖ • u = N • (y - u) + (N - ‖y‖) • u := by
          rw [smul_sub, sub_smul]; abel
        rw [e]
        have h4 : ‖N • (y - u) + (N - ‖y‖) • u‖ ≤ N * ‖y - u‖ + |N - ‖y‖| * N := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hN.le, Real.norm_eq_abs]
        have h5 : |N - ‖y‖| ≤ ‖y - u‖ := by
          rw [abs_le]; constructor <;> linarith
        have h6 : (2 + δ) * ‖y - u‖ ≤ δ * N := by
          rw [lt_div_iff₀ (by linarith)] at hη3; linarith
        have h7 : |N - ‖y‖| * N ≤ ‖y - u‖ * N := mul_le_mul_of_nonneg_right h5 hN.le
        have h8 : δ * (N - ‖y - u‖) * N ≤ δ * ‖y‖ * N := by
          apply mul_le_mul_of_nonneg_right _ hN.le
          exact mul_le_mul_of_nonneg_left hyge hδ.le
        have h9 : 2 * ‖y - u‖ * N ≤ δ * (N - ‖y - u‖) * N := by
          apply mul_le_mul_of_nonneg_right _ hN.le
          linarith
        linarith
      have e2 : ‖u‖ • (t • y) - ‖t • y‖ • u = t • (N • y - ‖y‖ • u) := by
        rw [norm_smul, Real.norm_of_nonneg ht, smul_sub, smul_comm t N y, mul_smul]
      rw [e2, norm_smul, Real.norm_of_nonneg ht, norm_smul, Real.norm_of_nonneg ht]
      calc t * ‖N • y - ‖y‖ • u‖ ≤ t * (δ * ‖y‖ * N) := mul_le_mul_of_nonneg_left key ht
        _ = δ * (t * ‖y‖) * ‖u‖ := by rw [hNdef]; ring

/-- Transfer of a Fréchet subgradient through `r = a·φ + H` with `H` differentiable, `a > 0`. -/
lemma reg_transfer {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (φ : X → EReal) (r H : X → ℝ) (a : ℝ) (ha : 0 < a) (p ξ H' : X)
    (hH : HasGradientAt H H' p) (hφ : ∀ᶠ w in 𝓝 p, φ w = (((r w - H w) / a : ℝ) : EReal))
    (hreg : IsRegularSubgrad (fun w => ((r w : ℝ) : EReal)) p ξ) :
    IsRegularSubgrad φ p (a⁻¹ • (ξ - H')) := by
  have hφp := hφ.self_of_nhds
  refine ⟨by rw [hφp]; exact EReal.coe_ne_top _, fun ε hε => ?_⟩
  have h1 := hreg.2 (ε * a / 2) (by positivity)
  have h2 := (hasGradientAt_iff_hasFDerivAt.mp hH).isLittleO.def (c := ε * a / 2) (by positivity)
  filter_upwards [h1, h2, hφ] with w h1w h2w hφw
  rw [hφw, hφp, ← EReal.coe_add, EReal.coe_le_coe_iff]
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1w
  rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs, abs_le] at h2w
  rw [inner_smul_left, inner_sub_left]
  simp only [RCLike.conj_to_real]
  set S := ⟪ξ, w - p⟫_ℝ
  set T := ⟪H', w - p⟫_ℝ
  have e : (r p - H p) / a + (a⁻¹ * (S - T) - ε * ‖w - p‖) =
      ((r p - H p) + (S - T) - ε * a * ‖w - p‖) / a := by
    field_simp; ring
  rw [e, div_le_div_iff_of_pos_right ha]
  nlinarith [h2w.1, h2w.2, norm_nonneg (w - p)]

lemma reg_const_zero {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (p e : X) (h : IsRegularSubgrad (fun _ : X => (0 : EReal)) p e) : e = 0 := by
  by_contra he
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have h1 := h.2 (‖e‖ / 2) (by positivity)
  have ht : Tendsto (fun s : ℝ => p + s • e) (𝓝[>] 0) (𝓝 p) := by
    have : Tendsto (fun s : ℝ => p + s • e) (𝓝 0) (𝓝 (p + (0:ℝ) • e)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := (ht.eventually h1).and self_mem_nhdsWithin
  obtain ⟨s, hs, hs0⟩ := h2.exists
  simp only [add_sub_cancel_left, zero_add] at hs
  rw [← EReal.coe_zero, EReal.coe_le_coe_iff, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_of_nonneg (le_of_lt hs0)] at hs
  have hs0' : (0:ℝ) < s := hs0
  nlinarith [mul_pos hs0' (mul_pos hn hn)]

lemma reg_smooth_unique {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X]
    (H : X → ℝ) (p ξ H' : X) (hH : HasGradientAt H H' p)
    (hreg : IsRegularSubgrad (fun w => ((H w : ℝ) : EReal)) p ξ) : ξ = H' := by
  have := reg_transfer (fun _ => (0 : EReal)) H H 1 one_pos p ξ H' hH
    (Eventually.of_forall fun w => by simp) hreg
  have := reg_const_zero p _ this
  rw [inv_one, one_smul, sub_eq_zero] at this
  exact this

lemma euc_norm_le_sum {k : ℕ} (v : E k) : ‖v‖ ≤ ∑ j, |v j| := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ j, ‖v j‖ ^ 2) ≤ Real.sqrt ((∑ j, |v j|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simpa [Real.norm_eq_abs] using
          Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun j => |v j|)
            (fun j _ => abs_nonneg (v j))
    _ = ∑ j, |v j| := Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg _)

lemma proj_dir {n m : ℕ} (u : E n) (v : E m) {εV δV : ℝ} (hε : 0 < εV) (hδ : 0 < δV) :
    ∃ ε1 > 0, ∃ δ1 > 0, ∀ w : Z n m, w ∈ DirKKTBilevel.VP.dirNbhd ε1 δ1 (WithLp.toLp 2 (u, v)) →
      (WithLp.ofLp w).1 ∈ DirKKTBilevel.VP.dirNbhd εV δV u := by
  obtain ⟨η, hη, hkey⟩ := cone_key u hε hδ
  by_cases hu : u = 0
  · subst hu
    refine ⟨εV, hε, 1, one_pos, fun w hw => ⟨lt_of_le_of_lt (WithLp.norm_fst_le (x := w)) hw.1, by simp⟩⟩
  · set d : Z n m := WithLp.toLp 2 (u, v) with hd
    have hud : ‖u‖ ≤ ‖d‖ := WithLp.norm_fst_le (x := d)
    have hD : 0 < ‖d‖ := lt_of_lt_of_le (norm_pos_iff.mpr hu) hud
    refine ⟨η * ‖d‖, by positivity, η / (2 * ‖d‖), by positivity, fun w hw => ?_⟩
    by_cases hw0 : w = 0
    · subst hw0
      have := hkey 0 u le_rfl hη (by simpa using hη)
      simpa using this
    · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      set s := ‖w‖ / ‖d‖ with hs_def
      have hs : 0 < s := div_pos hwn hD
      have e : (WithLp.ofLp w).1 = s • (s⁻¹ • (WithLp.ofLp w).1) := by
        rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
      rw [e]
      apply hkey s _ hs.le
      · rw [hs_def, div_lt_iff₀ hD]; exact hw.1
      · have hfst : (WithLp.ofLp (w - s • d)).1 = (WithLp.ofLp w).1 - s • u := by simp [d]
        have h1 : ‖(WithLp.ofLp w).1 - s • u‖ ≤ ‖w - s • d‖ := by
          rw [← hfst]; exact WithLp.norm_fst_le (x := w - s • d)
        have h2 : ‖d‖ • (w - s • d) = ‖d‖ • w - ‖w‖ • d := by
          rw [smul_sub, smul_smul, hs_def, mul_div_cancel₀ _ hD.ne']
        have h3 : ‖d‖ * ‖w - s • d‖ ≤ η / (2 * ‖d‖) * ‖w‖ * ‖d‖ := by
          rw [← Real.norm_of_nonneg hD.le, ← norm_smul, h2, Real.norm_of_nonneg hD.le]; exact hw.2
        have h4 : ‖w - s • d‖ ≤ η / (2 * ‖d‖) * ‖w‖ := by
          have := h3; rw [mul_comm _ ‖d‖] at this
          exact le_of_mul_le_mul_left this hD
        have e2 : s⁻¹ • (WithLp.ofLp w).1 - u = s⁻¹ • ((WithLp.ofLp w).1 - s • u) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
        rw [e2, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hs).le]
        calc s⁻¹ * ‖(WithLp.ofLp w).1 - s • u‖ ≤ s⁻¹ * (η / (2 * ‖d‖) * ‖w‖) :=
              mul_le_mul_of_nonneg_left (h1.trans h4) (inv_pos.mpr hs).le
          _ = η / 2 := by rw [hs_def]; field_simp
          _ < η := by linarith

lemma near_dir {n m : ℕ} (x u : E n) (y : E m) (v : E m) {εV δV : ℝ} (hε : 0 < εV)
    (hδ : 0 < δV) (ts : ℕ → ℝ) (ds : ℕ → Z n m) (hts0 : ∀ k, 0 < ts k)
    (hts : Tendsto ts atTop (𝓝 0)) (hds : Tendsto ds atTop (𝓝 (WithLp.toLp 2 (u, v)))) :
    ∀ᶠ k in atTop, ∀ᶠ w in 𝓝 (WithLp.toLp 2 (x, y) + ts k • ds k),
      (WithLp.ofLp w).1 - x ∈ DirKKTBilevel.VP.dirNbhd εV δV u := by
  obtain ⟨η, hη, hkey⟩ := cone_key u hε hδ
  have h1 : ∀ᶠ k in atTop, ts k < η := hts (Iio_mem_nhds hη)
  have hfst : Tendsto (fun k => (WithLp.ofLp (ds k)).1) atTop (𝓝 u) := by
    have := ((WithLp.continuous_fst 2 (E n) (E m)).tendsto _).comp hds
    simpa [Function.comp_def] using this
  have h2 : ∀ᶠ k in atTop, ‖(WithLp.ofLp (ds k)).1 - u‖ < η := by
    have := (Metric.tendsto_nhds.1 hfst) η hη
    simpa [dist_eq_norm] using this
  filter_upwards [h1, h2] with k hk1 hk2
  set t := ts k
  have ht : 0 < t := hts0 k
  have hcont : Continuous fun w : Z n m => ‖t⁻¹ • ((WithLp.ofLp w).1 - x) - u‖ :=
    ((((WithLp.prod_continuous_ofLp 2 (E n) (E m)).fst.sub continuous_const).const_smul
      t⁻¹).sub continuous_const).norm
  have hU : IsOpen {w : Z n m | ‖t⁻¹ • ((WithLp.ofLp w).1 - x) - u‖ < η} :=
    isOpen_lt hcont continuous_const
  have hmem : WithLp.toLp 2 (x, y) + t • ds k ∈
      {w : Z n m | ‖t⁻¹ • ((WithLp.ofLp w).1 - x) - u‖ < η} := by
    show ‖t⁻¹ • ((WithLp.ofLp (WithLp.toLp 2 (x, y) + t • ds k)).1 - x) - u‖ < η
    have : (WithLp.ofLp (WithLp.toLp 2 (x, y) + t • ds k)).1 - x = t • (WithLp.ofLp (ds k)).1 := by
      simp
    rw [this, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    exact hk2
  filter_upwards [hU.mem_nhds hmem] with w hw
  have e : (WithLp.ofLp w).1 - x = t • (t⁻¹ • ((WithLp.ofLp w).1 - x)) := by
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  rw [e]
  exact hkey t _ ht.le hk1 hw

lemma dirNbhd_mono {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {ε ε' δ δ' : ℝ}
    (hε : ε ≤ ε') (hδ : δ ≤ δ') {d z : X} (h : z ∈ DirKKTBilevel.VP.dirNbhd ε δ d) :
    z ∈ DirKKTBilevel.VP.dirNbhd ε' δ' d := by
  refine ⟨lt_of_lt_of_le h.1 hε, le_trans h.2 ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right hδ (norm_nonneg _)

lemma slope_lim {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (h : X → ℝ) (z d : X)
    (hd : DifferentiableAt ℝ h z) :
    Tendsto (fun t : ℝ => t⁻¹ * (h (z + t • d) - h z)) (𝓝[>] 0) (𝓝 (fderiv ℝ h z d)) := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add z
  have hD : HasDerivAt (fun t : ℝ => h (z + t • d)) (fderiv ℝ h z d) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) h1 (by simp)
  have := hD.tendsto_slope_zero_right
  simpa [smul_eq_mul] using this

/-- Block vectors of `ℝ^{1+p+q}`. -/
def blk {p q : ℕ} (a : ℝ) (b : Fin p → ℝ) (c : Fin q → ℝ) : Fin (1 + p + q) → ℝ :=
  Fin.addCases (Fin.addCases (fun _ => a) b) c

def i0 {p q : ℕ} : Fin (1 + p + q) := Fin.castAdd q (Fin.castAdd p (0 : Fin 1))
def ig {p q : ℕ} (i : Fin p) : Fin (1 + p + q) := Fin.castAdd q (Fin.natAdd 1 i)
def iG {p q : ℕ} (j : Fin q) : Fin (1 + p + q) := Fin.natAdd (1 + p) j

@[simp] lemma blk_i0 {p q : ℕ} (a : ℝ) (b : Fin p → ℝ) (c : Fin q → ℝ) :
    blk a b c i0 = a := by simp [blk, i0]
@[simp] lemma blk_ig {p q : ℕ} (a : ℝ) (b : Fin p → ℝ) (c : Fin q → ℝ) (i : Fin p) :
    blk a b c (ig i) = b i := by simp [blk, ig]
@[simp] lemma blk_iG {p q : ℕ} (a : ℝ) (b : Fin p → ℝ) (c : Fin q → ℝ) (j : Fin q) :
    blk a b c (iG j) = c j := by simp [blk, iG]

lemma sum_split {p q : ℕ} (h : Fin (1 + p + q) → ℝ) :
    ∑ j, h j = h i0 + ∑ i, h (ig i) + ∑ j, h (iG j) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]; rfl

lemma fin_split {p q : ℕ} (P : Fin (1 + p + q) → Prop) (h0 : P i0) (hg : ∀ i, P (ig i))
    (hG : ∀ j, P (iG j)) : ∀ j, P j := by
  intro j
  refine Fin.addCases (motive := P) (fun k => Fin.addCases
    (motive := fun k => P (Fin.castAdd q k)) (fun k0 => ?_) (fun i => hg i) k) (fun j => hG j) j
  rw [Fin.fin_one_eq_zero k0]; exact h0

variable {n m p q : ℕ}

/-- The first constraint `f(z) − V(z_x)` of (VP), made real-valued (`1` where `V = −∞`). -/
noncomputable def c0 (f : Z n m → ℝ) (g : Z n m → E p) (w : Z n m) : ℝ :=
  if valueFn f g (WithLp.ofLp w).1 = ⊥ then 1 else f w - (valueFn f g (WithLp.ofLp w).1).toReal

/-- The constraint map of (VP): `(f − V, g, G)`. -/
noncomputable def con (f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (w : Z n m) : E (1 + p + q) :=
  WithLp.toLp 2 (blk (c0 f g w) (fun i => g w i) (fun j => G w j))

lemma con_apply (f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (w : Z n m)
    (j : Fin (1 + p + q)) :
    con f g G w j = blk (c0 f g w) (fun i => g w i) (fun j => G w j) j := rfl

end DirKKT51Aux

open DirKKTBilevel.VP DirKKT51Aux

lemma hasGrad_comb {n m p q : ℕ} (g : Z n m → E p) (G : Z n m → E q)
    (hgi : ∀ i, ContDiff ℝ 1 (fun z => g z i)) (hGj : ∀ j, ContDiff ℝ 1 (fun z => G z j))
    (lg : E p) (lG : E q) (w : Z n m) :
    HasGradientAt (fun w => ∑ i, lg i * g w i + ∑ j, lG j * G w j)
      (∑ i, lg i • gradient (fun z => g z i) w + ∑ j, lG j • gradient (fun z => G z j) w) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun w => ∑ i, lg i * g w i)
      (∑ i, lg i • InnerProductSpace.toDual ℝ (Z n m) (gradient (fun z => g z i) w)) w :=
    HasFDerivAt.fun_sum (fun i _ => (hasGradientAt_iff_hasFDerivAt.mp
      ((hgi i).differentiable one_ne_zero w).hasGradientAt).const_mul (lg i))
  have h2 : HasFDerivAt (fun w => ∑ j, lG j * G w j)
      (∑ j, lG j • InnerProductSpace.toDual ℝ (Z n m) (gradient (fun z => G z j) w)) w :=
    HasFDerivAt.fun_sum (fun j _ => (hasGradientAt_iff_hasFDerivAt.mp
      ((hGj j).differentiable one_ne_zero w).hasGradientAt).const_mul (lG j))
  refine (h1.add h2).congr_fderiv ?_
  simp only [map_add, map_sum, map_smul]

lemma grad_cont {n m : ℕ} (h : Z n m → ℝ) (hh : ContDiff ℝ 1 h) : Continuous (gradient h) := by
  have := hh.continuous_fderiv one_ne_zero
  exact (InnerProductSpace.toDual ℝ (Z n m)).symm.continuous.comp this

lemma finish {n m p q : ℕ} (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (hf : ContDiff ℝ 1 f) (hgi : ∀ i, ContDiff ℝ 1 (fun z => g z i))
    (hGj : ∀ j, ContDiff ℝ 1 (fun z => G z j))
    (x : E n) (y : E m) (u : E n) (v : E m) (dV : ℝ) (z0 d : Z n m)
    (hz0 : z0 = WithLp.toLp 2 (x, y)) (hd : d = WithLp.toLp 2 (u, v))
    (LV εV δV : ℝ) (hLV : 0 < LV) (hεV : 0 < εV) (hδV : 0 < δV)
    (hfin : ∀ z, z - x ∈ DirKKTBilevel.VP.dirNbhd εV δV u →
      valueFn f g z ≠ ⊥ ∧ valueFn f g z ≠ ⊤)
    (hLipV : ∀ z z', z - x ∈ DirKKTBilevel.VP.dirNbhd εV δV u →
      z' - x ∈ DirKKTBilevel.VP.dirNbhd εV δV u →
      |(valueFn f g z).toReal - (valueFn f g z').toReal| ≤ LV * ‖z - z'‖)
    (hVxB : valueFn f g x ≠ ⊥) (hVxT : valueFn f g x ≠ ⊤)
    (hφz0 : ((f z0 : ℝ) : EReal) - valueFn f g (WithLp.ofLp z0).1 = ((0 : ℝ) : EReal))
    (hc0z : c0 f g z0 = 0)
    (hc0E : ∀ w : Z n m, valueFn f g (WithLp.ofLp w).1 ≠ ⊥ →
      valueFn f g (WithLp.ofLp w).1 ≠ ⊤ →
      ((f w : EReal) - valueFn f g (WithLp.ofLp w).1) = ((c0 f g w : ℝ) : EReal))
    (hgz : ∀ i, g z0 i ≤ 0) (hGz : ∀ j, G z0 j ≤ 0)
    (hc1 : fderiv ℝ f z0 d ≤ dV)
    (hc2 : ∀ i, g z0 i = 0 → fderiv ℝ (fun z => g z i) z0 d ≤ 0)
    (hc3 : ∀ j, G z0 j = 0 → fderiv ℝ (fun z => G z j) z0 d ≤ 0)
    (l : E (1 + p + q)) (hl0 : ∀ j, 0 ≤ l j)
    (hlc : ∑ j, l j * con f g G z0 j = 0)
    (hld : ∑ j, l j * blk (fderiv ℝ f z0 d - dV) (fun i => fderiv ℝ (fun z => g z i) z0 d)
      (fun j => fderiv ℝ (fun z => G z j) z0 d) j = 0)
    (ξ : Z n m) (hξ : ξ ∈ dirSubdiff (fun w => ((∑ j, l j * con f g G w j : ℝ) : EReal)) z0 d)
    (hgradeq : gradient F z0 + ξ = 0) :
    ∃ (lV : ℝ) (lg : E p) (lG : E q) (ξ : E n),
      ξ ∈ dirSubdiff (fun x' => -(valueFn f g x')) x u ∧
      gradient F z0 + lV • gradient f z0
          + lV • (WithLp.toLp 2 (ξ, 0) : Z n m)
          + ∑ i, lg i • gradient (fun z => g z i) z0
          + ∑ j, lG j • gradient (fun z => G z j) z0 = 0 ∧
      0 ≤ lV ∧
      (∀ i, 0 ≤ lg i) ∧ ∑ i, lg i * g z0 i = 0 ∧
      ∑ i, lg i * fderiv ℝ (fun z => g z i) z0 d = 0 ∧
      (∀ j, 0 ≤ lG j) ∧ ∑ j, lG j * G z0 j = 0 ∧
      ∑ j, lG j * fderiv ℝ (fun z => G z j) z0 d = 0 := by
  obtain ⟨lV, hlV⟩ : ∃ lV : ℝ, lV = l i0 := ⟨_, rfl⟩
  obtain ⟨lg, hlg⟩ : ∃ lg : E p, ∀ i, lg i = l (ig i) := ⟨WithLp.toLp 2 (fun i => l (ig i)), fun i => rfl⟩
  obtain ⟨lG, hlG⟩ : ∃ lG : E q, ∀ j, lG j = l (iG j) := ⟨WithLp.toLp 2 (fun j => l (iG j)), fun j => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Z n m → ℝ, H = fun w => ∑ i, lg i * g w i + ∑ j, lG j * G w j := ⟨_, rfl⟩
  obtain ⟨Hgrad, hHg⟩ : ∃ Hgrad : Z n m → Z n m, Hgrad = fun w =>
      ∑ i, lg i • gradient (fun z => g z i) w + ∑ j, lG j • gradient (fun z => G z j) w := ⟨_, rfl⟩
  have hψ : ∀ w, ∑ j, l j * con f g G w j = lV * c0 f g w + H w := by
    intro w
    rw [sum_split, hH]
    simp only [con_apply, blk_i0, blk_ig, blk_iG, hlg, hlG, hlV]
    ring
  have hHgrad : ∀ w, HasGradientAt H (Hgrad w) w := by
    intro w; rw [hH, hHg]; exact hasGrad_comb g G hgi hGj lg lG w
  have hHcont : Continuous Hgrad := by
    have hc1 : ∀ i, Continuous (fun w => lg i • gradient (fun z => g z i) w) := fun i =>
      (grad_cont (fun z => g z i) (hgi i)).const_smul (lg i)
    have hc2 : ∀ j, Continuous (fun w => lG j • gradient (fun z => G z j) w) := fun j =>
      (grad_cont (fun z => G z j) (hGj j)).const_smul (lG j)
    rw [hHg]
    exact (continuous_finsetSum Finset.univ fun i _ => hc1 i).add
      (continuous_finsetSum Finset.univ fun j _ => hc2 j)
  have hHc : Continuous H := by
    rw [hH]
    exact (continuous_finsetSum _ fun i _ => continuous_const.mul (hgi i).continuous).add
      (continuous_finsetSum _ fun j _ => continuous_const.mul (hGj j).continuous)
  obtain ⟨hψT, hψB, ts, ds, ξs, hts0, hts, hds, hξs, hψconv, hregs⟩ := hξ
  have hps : Tendsto (fun k => z0 + ts k • ds k) atTop (𝓝 z0) := by
    have := (tendsto_const_nhds (x := z0)).add (hts.smul hds)
    simpa using this
  -- complementarity
  have hlg0 : ∀ i, 0 ≤ lg i := fun i => by rw [hlg]; exact hl0 (ig i)
  have hlG0 : ∀ j, 0 ≤ lG j := fun j => by rw [hlG]; exact hl0 (iG j)
  have hlV0 : 0 ≤ lV := by rw [hlV]; exact hl0 i0
  have hlc' : lV * c0 f g z0 + ∑ i, lg i * g z0 i + ∑ j, lG j * G z0 j = 0 := by
    rw [← hlc, sum_split]
    simp only [con_apply, blk_i0, blk_ig, blk_iG, hlg, hlG, hlV]
  have hSg_np : ∀ i, lg i * g z0 i ≤ 0 := fun i => mul_nonpos_of_nonneg_of_nonpos (hlg0 i) (hgz i)
  have hSG_np : ∀ j, lG j * G z0 j ≤ 0 := fun j => mul_nonpos_of_nonneg_of_nonpos (hlG0 j) (hGz j)
  have a1 := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hSg_np i)
  have a2 := Finset.sum_nonpos (s := Finset.univ) (fun j _ => hSG_np j)
  rw [hc0z, mul_zero, zero_add] at hlc'
  have hSg : ∑ i, lg i * g z0 i = 0 := by linarith
  have hSG : ∑ j, lG j * G z0 j = 0 := by linarith
  have hcompg : ∀ i, lg i * g z0 i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hSg_np i)).1 hSg i (Finset.mem_univ i)
  have hcompG : ∀ j, lG j * G z0 j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hSG_np j)).1 hSG j (Finset.mem_univ j)
  have hdg_np : ∀ i, lg i * fderiv ℝ (fun z => g z i) z0 d ≤ 0 := by
    intro i
    by_cases hi : g z0 i = 0
    · exact mul_nonpos_of_nonneg_of_nonpos (hlg0 i) (hc2 i hi)
    · have : lg i = 0 := by
        rcases mul_eq_zero.1 (hcompg i) with h | h
        · exact h
        · exact absurd h hi
      rw [this, zero_mul]
  have hdG_np : ∀ j, lG j * fderiv ℝ (fun z => G z j) z0 d ≤ 0 := by
    intro j
    by_cases hj : G z0 j = 0
    · exact mul_nonpos_of_nonneg_of_nonpos (hlG0 j) (hc3 j hj)
    · have : lG j = 0 := by
        rcases mul_eq_zero.1 (hcompG j) with h | h
        · exact h
        · exact absurd h hj
      rw [this, zero_mul]
  have hld' : lV * (fderiv ℝ f z0 d - dV) + ∑ i, lg i * fderiv ℝ (fun z => g z i) z0 d +
      ∑ j, lG j * fderiv ℝ (fun z => G z j) z0 d = 0 := by
    rw [← hld, sum_split]
    simp only [blk_i0, blk_ig, blk_iG, hlg, hlG, hlV]
  have hd0 : lV * (fderiv ℝ f z0 d - dV) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlV0 (by linarith)
  have a3 := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hdg_np i)
  have a4 := Finset.sum_nonpos (s := Finset.univ) (fun j _ => hdG_np j)
  have hSgd : ∑ i, lg i * fderiv ℝ (fun z => g z i) z0 d = 0 := by linarith
  have hSGd : ∑ j, lG j * fderiv ℝ (fun z => G z j) z0 d = 0 := by linarith
  have hHz : Hgrad z0 = ∑ i, lg i • gradient (fun z => g z i) z0 +
      ∑ j, lG j • gradient (fun z => G z j) z0 := by rw [hHg]
  rcases hlV0.lt_or_eq with hpos | hzero
  · -- `λ_V > 0`: transfer the subgradient to `f − V` and apply the sum rule
    have hnd := near_dir x u y v hεV hδV ts ds hts0 hts (hd ▸ hds)
    rw [← hz0] at hnd
    obtain ⟨K, hK⟩ := eventually_atTop.1 hnd
    obtain ⟨φ, hφdef⟩ : ∃ φ : Z n m → EReal,
        φ = fun z => (f z : EReal) - valueFn f g (WithLp.ofLp z).1 := ⟨_, rfl⟩
    have hφeq : ∀ k ≥ K, ∀ᶠ w in 𝓝 (z0 + ts k • ds k),
        φ w = (((∑ j, l j * con f g G w j - H w) / lV : ℝ) : EReal) := by
      intro k hk
      filter_upwards [hK k hk] with w hw
      obtain ⟨hB, hT⟩ := hfin _ hw
      rw [hφdef]
      show ((f w : EReal) - valueFn f g (WithLp.ofLp w).1) = _
      rw [hc0E w hB hT, hψ w]
      congr 1
      field_simp
      ring
    have hφz : φ z0 = (((∑ j, l j * con f g G z0 j - H z0) / lV : ℝ) : EReal) := by
      rw [hψ z0, hc0z, hφdef]
      show ((f z0 : EReal) - valueFn f g (WithLp.ofLp z0).1) = _
      rw [hφz0]
      congr 1
      simp
    have hζ : lV⁻¹ • (ξ - Hgrad z0) ∈ dirSubdiff φ z0 d := by
      refine ⟨?_, ?_, fun k => ts (k + K), fun k => ds (k + K),
        fun k => lV⁻¹ • (ξs (k + K) - Hgrad (z0 + ts (k + K) • ds (k + K))),
        fun k => hts0 _, (tendsto_add_atTop_iff_nat K).2 hts, (tendsto_add_atTop_iff_nat K).2 hds,
        ?_, ?_, fun k => ?_⟩
      · rw [hφz]; exact EReal.coe_ne_top _
      · rw [hφz]; exact EReal.coe_ne_bot _
      · exact ((hξs.comp (tendsto_add_atTop_nat K)).sub ((hHcont.tendsto z0).comp
          (hps.comp (tendsto_add_atTop_nat K)))).const_smul lV⁻¹
      · rw [hφz]
        have hr : Tendsto (fun k => ∑ j, l j * con f g G (z0 + ts k • ds k) j) atTop
            (𝓝 (∑ j, l j * con f g G z0 j)) := EReal.tendsto_coe.1 hψconv
        have hr2 := (hr.sub ((hHc.tendsto z0).comp hps)).div_const lV
        have hr3 := EReal.tendsto_coe.2 (hr2.comp (tendsto_add_atTop_nat K))
        refine hr3.congr' (Eventually.of_forall fun k => ?_)
        exact ((hφeq (k + K) (by omega)).self_of_nhds).symm
      · exact reg_transfer φ (fun w => ∑ j, l j * con f g G w j) H lV hpos _ (ξs (k + K)) _
          (hHgrad _) (hφeq (k + K) (by omega)) (hregs (k + K))
    have hsr := dir_sum_rule f g hf x y u v hVxB hVxT
    rw [← hz0, ← hd] at hsr
    rw [hφdef, hsr] at hζ
    obtain ⟨ξ', hξ', hζeq⟩ := hζ
    have e : ξ - Hgrad z0 = lV • (lV⁻¹ • (ξ - Hgrad z0)) := by
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    have hξd : ξ = lV • gradient f z0 + lV • (WithLp.toLp 2 (ξ', 0) : Z n m) + Hgrad z0 := by
      calc ξ = (ξ - Hgrad z0) + Hgrad z0 := by abel
        _ = lV • (gradient f z0 + WithLp.toLp 2 (ξ', 0)) + Hgrad z0 := by rw [e, hζeq]
        _ = _ := by rw [smul_add]
    refine ⟨lV, lg, lG, ξ', hξ', ?_, hlV0, hlg0, hSg, hSgd, hlG0, hSG, hSGd⟩
    rw [hξd, hHz] at hgradeq
    rw [← hgradeq]
    abel
  · -- `λ_V = 0`: the multiplier function is smooth
    have hξk : ∀ k, ξs k = Hgrad (z0 + ts k • ds k) := fun k => by
      refine reg_smooth_unique H _ _ _ (hHgrad _) ?_
      have := hregs k
      have e : (fun w => ((∑ j, l j * con f g G w j : ℝ) : EReal)) =
          fun w => ((H w : ℝ) : EReal) := by
        funext w; rw [hψ w, ← hzero, zero_mul, zero_add]
      rw [e] at this; exact this
    have hξH : ξ = Hgrad z0 := by
      refine tendsto_nhds_unique hξs ?_
      have := (hHcont.tendsto z0).comp hps
      refine this.congr ?_
      intro k; exact (hξk k).symm
    have hLipNeg : DirLipschitzAtEReal (fun x' => -(valueFn f g x')) x u := by
      refine ⟨LV, εV, δV, hLV, hεV, hδV, fun z hz => ?_, fun z z' hz hz' => ?_⟩
      · obtain ⟨hB, hT⟩ := hfin z hz
        exact ⟨by simpa using hT, by simpa using hB⟩
      · simp only [EReal.toReal_neg_eq]
        rw [show -(valueFn f g z).toReal - -(valueFn f g z').toReal =
          -((valueFn f g z).toReal - (valueFn f g z').toReal) by ring, abs_neg]
        exact hLipV z z' hz hz'
    obtain ⟨ξ', hξ'⟩ := dirSubdiff_nonempty _ x u hLipNeg
    refine ⟨lV, lg, lG, ξ', hξ', ?_, hlV0, hlg0, hSg, hSgd, hlG0, hSG, hSGd⟩
    rw [← hzero, zero_smul, zero_smul, add_zero, add_zero, add_assoc]
    rw [hξH, hHz] at hgradeq
    exact hgradeq

theorem solution {n m p q : ℕ} (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (hF : ContDiff ℝ 1 F) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hG : ContDiff ℝ 1 G)
    (x : E n) (y : E m) (u : E n) (v : E m) (dV : ℝ)
    (hmin : IsLocalMinBP F f g G x y)
    (hLip : DirLipschitzAtEReal (valueFn f g) x u)
    (hdiff : HasDirDerivAt (fun x' => (valueFn f g x').toReal) x u dV)
    (hcrit : criticalConeVP F f g G x y dV (WithLp.toLp 2 (u, v)))
    (hcalm : IsCalmDirVP F f g G x y (WithLp.toLp 2 (u, v))) :
    ∃ (lV : ℝ) (lg : E p) (lG : E q) (ξ : E n),
      ξ ∈ dirSubdiff (fun x' => -(valueFn f g x')) x u ∧
      gradient F (WithLp.toLp 2 (x, y)) + lV • gradient f (WithLp.toLp 2 (x, y))
          + lV • (WithLp.toLp 2 (ξ, 0) : Z n m)
          + ∑ i, lg i • gradient (fun z => g z i) (WithLp.toLp 2 (x, y))
          + ∑ j, lG j • gradient (fun z => G z j) (WithLp.toLp 2 (x, y)) = 0 ∧
      0 ≤ lV ∧
      (∀ i, 0 ≤ lg i) ∧ ∑ i, lg i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
      ∑ i, lg i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 ∧
      (∀ j, 0 ≤ lG j) ∧ ∑ j, lG j * G (WithLp.toLp 2 (x, y)) j = 0 ∧
      ∑ j, lG j * fderiv ℝ (fun z => G z j) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 := by
  classical
  set z0 : Z n m := WithLp.toLp 2 (x, y) with hz0
  set d : Z n m := WithLp.toLp 2 (u, v) with hd
  have hyS : y ∈ solMap f g x := hmin.1.1
  have hGz : ∀ j, G z0 j ≤ 0 := hmin.1.2
  have hloc := hmin.2
  obtain ⟨LV, εV, δV, hLV, hεV, hδV, hfin, hLipV⟩ := hLip
  have hyF : y ∈ feasLL g x := hyS.1
  have hVx : valueFn f g x = ((f z0 : ℝ) : EReal) :=
    le_antisymm (iInf₂_le y hyF) (le_iInf₂ fun y' hy' => EReal.coe_le_coe_iff.2 (hyS.2 y' hy'))
  have hVxB : valueFn f g x ≠ ⊥ := by rw [hVx]; exact EReal.coe_ne_bot _
  have hVxT : valueFn f g x ≠ ⊤ := by rw [hVx]; exact EReal.coe_ne_top _
  have hc0 : ∀ w : Z n m, valueFn f g (WithLp.ofLp w).1 ≠ ⊥ →
      c0 f g w = f w - (valueFn f g (WithLp.ofLp w).1).toReal := by
    intro w hw; simp only [c0, if_neg hw]
  have hc0E : ∀ w : Z n m, valueFn f g (WithLp.ofLp w).1 ≠ ⊥ →
      valueFn f g (WithLp.ofLp w).1 ≠ ⊤ →
      ((f w : EReal) - valueFn f g (WithLp.ofLp w).1) = ((c0 f g w : ℝ) : EReal) := by
    intro w hB hT
    rw [hc0 w hB, EReal.coe_sub, EReal.coe_toReal hT hB]
  have hc0z : c0 f g z0 = 0 := by
    rw [hc0 z0 hVxB]
    show f z0 - (valueFn f g x).toReal = 0
    rw [hVx, EReal.toReal_coe, sub_self]
  obtain ⟨η, hη, hkey⟩ := cone_key u hεV hδV
  obtain ⟨ε1, hε1, δ1, hδ1, hproj⟩ := proj_dir u v hεV hδV
  have hprojw : ∀ w : Z n m, w - z0 ∈ DirKKTBilevel.VP.dirNbhd ε1 δ1 d →
      (WithLp.ofLp w).1 - x ∈ DirKKTBilevel.VP.dirNbhd εV δV u := by
    intro w hw
    have := hproj _ hw
    simpa [z0] using this
  have hgi : ∀ i, ContDiff ℝ 1 (fun z => g z i) := fun i => by
    have := (EuclideanSpace.proj i : E p →L[ℝ] ℝ).contDiff.comp hg
    simpa [Function.comp_def] using this
  have hGj : ∀ j, ContDiff ℝ 1 (fun z => G z j) := fun j => by
    have := (EuclideanSpace.proj j : E q →L[ℝ] ℝ).contDiff.comp hG
    simpa [Function.comp_def] using this
  -- feasibility of `z0` for the constraint map
  have hfeas : ∀ j, con f g G z0 j ≤ 0 := by
    refine fin_split _ ?_ (fun i => ?_) (fun j => ?_)
    · rw [con_apply, blk_i0, hc0z]
    · rw [con_apply, blk_ig]; exact hyF i
    · rw [con_apply, blk_iG]; exact hGz j
  -- local minimality on the (VP)-feasible set
  have hmin' : IsLocalMinOn F {w | ∀ j, con f g G w j ≤ 0} z0 := by
    have feas : ∀ w : Z n m, (∀ j, con f g G w j ≤ 0) → FeasBP f g G w := by
      intro w hw
      have hw0 : c0 f g w ≤ 0 := by have := hw i0; rwa [con_apply, blk_i0] at this
      have hwg : ∀ i, g w i ≤ 0 := fun i => by have := hw (ig i); rwa [con_apply, blk_ig] at this
      have hwG : ∀ j, G w j ≤ 0 := fun j => by have := hw (iG j); rwa [con_apply, blk_iG] at this
      have hww : WithLp.toLp 2 ((WithLp.ofLp w).1, (WithLp.ofLp w).2) = w := rfl
      have hB : valueFn f g (WithLp.ofLp w).1 ≠ ⊥ := by
        intro hB
        have : c0 f g w = 1 := by simp only [c0, if_pos hB]
        linarith
      have hF' : (WithLp.ofLp w).2 ∈ feasLL g (WithLp.ofLp w).1 := by
        intro i; rw [hww]; exact hwg i
      have hle : valueFn f g (WithLp.ofLp w).1 ≤ ((f w : ℝ) : EReal) := by
        have := iInf₂_le (f := fun y' (_ : y' ∈ feasLL g (WithLp.ofLp w).1) =>
          ((f (WithLp.toLp 2 ((WithLp.ofLp w).1, y')) : ℝ) : EReal)) _ hF'
        rw [hww] at this; exact this
      have hT : valueFn f g (WithLp.ofLp w).1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
      have hge : ((f w : ℝ) : EReal) ≤ valueFn f g (WithLp.ofLp w).1 := by
        rw [← EReal.coe_toReal hT hB, EReal.coe_le_coe_iff]
        rw [hc0 w hB] at hw0; linarith
      refine ⟨⟨hF', fun y'' hy'' => ?_⟩, hwG⟩
      have := le_trans hge (iInf₂_le (f := fun y' (_ : y' ∈ feasLL g (WithLp.ofLp w).1) =>
          ((f (WithLp.toLp 2 ((WithLp.ofLp w).1, y')) : ℝ) : EReal)) y'' hy'')
      exact EReal.coe_le_coe_iff.1 this
    exact eventually_nhdsWithin_iff.2 (hloc.mono fun w hw hws => hw (feas w hws))
  -- the directional derivative of the constraint map
  set dcon : E (1 + p + q) := WithLp.toLp 2 (blk (fderiv ℝ f z0 d - dV)
    (fun i => fderiv ℝ (fun z => g z i) z0 d) (fun j => fderiv ℝ (fun z => G z j) z0 d))
    with hdcon
  have hdir : HasDirDerivAt (con f g G) z0 d dcon := by
    have key : ∀ j, Tendsto (fun t : ℝ => t⁻¹ * (con f g G (z0 + t • d) j - con f g G z0 j))
        (𝓝[>] 0) (𝓝 (dcon j)) := by
      refine fin_split _ ?_ (fun i => ?_) (fun j => ?_)
      · simp only [con_apply, blk_i0, hdcon, PiLp.toLp_apply]
        have hev : (fun t : ℝ => t⁻¹ * (f (z0 + t • d) - f z0) -
            t⁻¹ • ((valueFn f g (x + t • u)).toReal - (valueFn f g x).toReal)) =ᶠ[𝓝[>] 0]
            (fun t : ℝ => t⁻¹ * (c0 f g (z0 + t • d) - c0 f g z0)) := by
          have h1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < η :=
            nhdsWithin_le_nhds (Iio_mem_nhds hη)
          filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
          have ht0' : (0:ℝ) < t := ht0
          have hx : (WithLp.ofLp (z0 + t • d)).1 = x + t • u := by simp [z0, d]
          have hreg : (WithLp.ofLp (z0 + t • d)).1 - x ∈ DirKKTBilevel.VP.dirNbhd εV δV u := by
            rw [hx, add_sub_cancel_left]; exact hkey t u ht0'.le ht (by simpa using hη)
          have hB := (hfin _ hreg).1
          rw [hc0 _ hB, hc0 z0 (by simpa [z0] using hVxB), hx, smul_eq_mul]
          show _ = t⁻¹ * (f (z0 + t • d) - (valueFn f g (x + t • u)).toReal -
            (f z0 - (valueFn f g x).toReal))
          ring
        refine Tendsto.congr' hev ?_
        exact (slope_lim f z0 d (hf.differentiable one_ne_zero z0)).sub hdiff
      · simp only [con_apply, blk_ig, hdcon, PiLp.toLp_apply]
        exact slope_lim _ z0 d ((hgi i).differentiable one_ne_zero z0)
      · simp only [con_apply, blk_iG, hdcon, PiLp.toLp_apply]
        exact slope_lim _ z0 d ((hGj j).differentiable one_ne_zero z0)
    have h2 := ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 key)
    unfold HasDirDerivAt
    convert h2 using 2 with t
    · ext j; simp [smul_eq_mul]
  have hcritc : criticalCone F (con f g G) z0 d dcon := by
    refine ⟨fun j hj => ?_, hcrit.2.2.2⟩
    revert hj
    refine fin_split (fun j => j ∈ activeSet (con f g G) z0 → dcon j ≤ 0) ?_ (fun i => ?_)
      (fun j => ?_) j
    · intro _
      simp only [hdcon, PiLp.toLp_apply, blk_i0]
      linarith [hcrit.1]
    · intro hi
      simp only [activeSet, Set.mem_ofPred_eq, con_apply, blk_ig] at hi
      simp only [hdcon, PiLp.toLp_apply, blk_ig]
      exact hcrit.2.1 i hi
    · intro hj
      simp only [activeSet, Set.mem_ofPred_eq, con_apply, blk_iG] at hj
      simp only [hdcon, PiLp.toLp_apply, blk_iG]
      exact hcrit.2.2.1 j hj
  have hcalmc : IsCalmDir F (con f g G) z0 d := by
    obtain ⟨ε, δ, ρ, hε, hδ, hρ, hc⟩ := hcalm
    refine ⟨min ε ε1, min δ δ1, ρ, lt_min hε hε1, lt_min hδ hδ1, hρ, ?_⟩
    intro α hα w hw hcon
    have hw1 : w - z0 ∈ DirKKTBilevel.VP.dirNbhd ε δ d :=
      dirNbhd_mono (min_le_left _ _) (min_le_left _ _) hw
    have hw2 := hprojw w (dirNbhd_mono (min_le_right _ _) (min_le_right _ _) hw)
    obtain ⟨hB, hT⟩ := hfin _ hw2
    set a := α i0 with ha
    set b : E p := WithLp.toLp 2 (fun i => α (ig i)) with hb
    set c : E q := WithLp.toLp 2 (fun j => α (iG j)) with hc'
    have hnorm : Real.sqrt (a ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) = ‖α‖ := by
      rw [EuclideanSpace.norm_eq α, EuclideanSpace.real_norm_sq_eq b,
        EuclideanSpace.real_norm_sq_eq c, sum_split (fun j => ‖α j‖ ^ 2)]
      simp [b, c, a, Real.norm_eq_abs, sq_abs]
    have := hc a b c (by rw [hnorm]; exact lt_of_lt_of_le hα (min_le_left _ _)) w hw1 ?_ ?_ ?_
    · rwa [hnorm] at this
    · rw [hc0E w hB hT, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff]
      have := hcon i0; rw [con_apply, blk_i0] at this; exact this
    · intro i; have := hcon (ig i); rw [con_apply, blk_ig] at this; exact this
    · intro j; have := hcon (iG j); rw [con_apply, blk_iG] at this; exact this
  have hlipc : DirLipschitzAt (con f g G) z0 d := by
    obtain ⟨Kf, tf, htf, hKf⟩ := (hf.contDiffAt (x := z0)).exists_lipschitzOnWith
    obtain ⟨Kg, tg, htg, hKg⟩ := (hg.contDiffAt (x := z0)).exists_lipschitzOnWith
    obtain ⟨KG, tG, htG, hKG⟩ := (hG.contDiffAt (x := z0)).exists_lipschitzOnWith
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem htf (inter_mem htg htG))
    refine ⟨Kf + LV + p * Kg + q * KG, min r ε1, δ1, by positivity, lt_min hr hε1, hδ1,
      fun w w' hw hw' => ?_⟩
    have hwb : w ∈ Metric.ball z0 r := by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hw.1 (min_le_left _ _)
    have hw'b : w' ∈ Metric.ball z0 r := by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hw'.1 (min_le_left _ _)
    have hr1 := hprojw w (dirNbhd_mono (min_le_right _ _) le_rfl hw)
    have hr1' := hprojw w' (dirNbhd_mono (min_le_right _ _) le_rfl hw')
    have hB := (hfin _ hr1).1
    have hB' := (hfin _ hr1').1
    have hfst : ‖(WithLp.ofLp w).1 - (WithLp.ofLp w').1‖ ≤ ‖w - w'‖ := by
      have := WithLp.norm_fst_le (x := w - w'); simpa using this
    have h0 : |c0 f g w - c0 f g w'| ≤ (Kf + LV) * ‖w - w'‖ := by
      rw [hc0 w hB, hc0 w' hB']
      have e1 : |f w - f w'| ≤ Kf * ‖w - w'‖ := by
        have := hKf.dist_le_mul w (hball hwb).1 w' (hball hw'b).1
        rwa [Real.dist_eq, dist_eq_norm] at this
      have e2 := hLipV _ _ hr1 hr1'
      have e3 : f w - (valueFn f g (WithLp.ofLp w).1).toReal -
          (f w' - (valueFn f g (WithLp.ofLp w').1).toReal) = (f w - f w') -
          ((valueFn f g (WithLp.ofLp w).1).toReal - (valueFn f g (WithLp.ofLp w').1).toReal) := by
        ring
      rw [e3]
      refine le_trans (abs_sub _ _) ?_
      have : LV * ‖(WithLp.ofLp w).1 - (WithLp.ofLp w').1‖ ≤ LV * ‖w - w'‖ :=
        mul_le_mul_of_nonneg_left hfst hLV.le
      nlinarith
    have hgc : ∀ i, |g w i - g w' i| ≤ Kg * ‖w - w'‖ := by
      intro i
      have h1 : |g w i - g w' i| ≤ ‖g w - g w'‖ := by
        have := PiLp.norm_apply_le (g w - g w') i; simpa [Real.norm_eq_abs] using this
      have h2 := hKg.dist_le_mul w (hball hwb).2.1 w' (hball hw'b).2.1
      rw [dist_eq_norm, dist_eq_norm] at h2
      linarith
    have hGc : ∀ j, |G w j - G w' j| ≤ KG * ‖w - w'‖ := by
      intro j
      have h1 : |G w j - G w' j| ≤ ‖G w - G w'‖ := by
        have := PiLp.norm_apply_le (G w - G w') j; simpa [Real.norm_eq_abs] using this
      have h2 := hKG.dist_le_mul w (hball hwb).2.2 w' (hball hw'b).2.2
      rw [dist_eq_norm, dist_eq_norm] at h2
      linarith
    calc ‖con f g G w - con f g G w'‖ ≤ ∑ j, |(con f g G w - con f g G w') j| :=
          euc_norm_le_sum _
      _ = |c0 f g w - c0 f g w'| + ∑ i, |g w i - g w' i| + ∑ j, |G w j - G w' j| := by
          rw [sum_split]; simp [con_apply]
      _ ≤ (Kf + LV) * ‖w - w'‖ + ∑ i : Fin p, Kg * ‖w - w'‖ + ∑ j : Fin q, KG * ‖w - w'‖ := by
          gcongr with i _ j _
          · exact hgc i
          · exact hGc j
      _ = (Kf + LV + p * Kg + q * KG) * ‖w - w'‖ := by
          simp [Finset.sum_const]; ring
  -- apply Theorem 3.1 to (VP)
  obtain ⟨l, hl0, hlc, hld, ξ, hξ, hgradeq⟩ := theorem_3_1 F (con f g G) z0 d dcon hfeas hmin'
    hF.contDiffAt hlipc hdir hcritc hcalmc
  have hφz0 : ((f z0 : ℝ) : EReal) - valueFn f g (WithLp.ofLp z0).1 = ((0 : ℝ) : EReal) := by
    show ((f z0 : ℝ) : EReal) - valueFn f g x = _
    rw [hVx, ← EReal.coe_sub, sub_self]
  exact finish F f g G hf hgi hGj x y u v dV z0 d hz0 hd LV εV δV hLV hεV hδV hfin hLipV
    hVxB hVxT hφz0 hc0z hc0E hyF hGz hcrit.1 hcrit.2.1 hcrit.2.2.1 l hl0 hlc hld ξ hξ hgradeq
