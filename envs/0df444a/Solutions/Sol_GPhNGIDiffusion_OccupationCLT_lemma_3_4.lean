-- Prove2me | solution 1 for GPhNGIDiffusion.OccupationCLT.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T17:51:28.437935+00:00
-- url     : https://prove2.me/submissions/61d92592-6f8a-4504-91cf-c5475f2574e4

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Diffusion
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Mollified

open MeasureTheory Filter Topology

namespace Occ34

/-- Integral Grönwall. -/
lemma gronwall_int {u α : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hu : Continuous u)
    (hα : MonotoneOn α (Set.Ici 0))
    (h : ∀ t, 0 ≤ t → u t ≤ α t + L * ∫ s in (0:ℝ)..t, u s)
    (T : ℝ) (hT : 0 ≤ T) : u T ≤ α T * Real.exp (L * T) := by
  set f : ℝ → ℝ := fun t => α T + L * ∫ s in (0:ℝ)..t, u s with hf
  have hderiv : ∀ t, HasDerivAt f (L * u t) t := by
    intro t
    have := intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable 0 t)
      (hu.stronglyMeasurableAtFilter _ _) hu.continuousAt
    exact (this.const_mul L).const_add _
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := f) (f' := fun t => L * u t)
    (δ := α T) (K := L) (ε := 0) (a := 0) (b := T) hfc.continuousOn
    (fun x _ r hr => (hderiv x).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [hf]) (by
      intro x hx
      have h1 := h x hx.1
      have h2 : α x ≤ α T := hα hx.1 hT hx.2.le
      simp only [hf, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left (show u x ≤ α T + L * ∫ s in (0:ℝ)..x, u s by linarith) hL])
    T ⟨hT, le_rfl⟩
  rw [sub_zero, gronwallBound_ε0] at key
  have := h T hT
  simp only [hf] at key
  linarith

/-- The elementary inequality behind the binomial expansion. -/
lemma mono_bound (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (p q : ℕ) :
    (2 * r * s + s ^ 2) ^ (q + 2) * r ^ (2 * p) ≤
      3 ^ (q + 2) * (r ^ (2 * (q + p) + 2) * s ^ 2 + s ^ (2 * (q + 2 + p))) := by
  rcases le_total s r with hsr | hrs
  · have h1 : 2 * r * s + s ^ 2 ≤ 3 * (r * s) := by nlinarith
    have h2 : (2 * r * s + s ^ 2) ^ (q + 2) ≤ (3 * (r * s)) ^ (q + 2) :=
      pow_le_pow_left₀ (by positivity) h1 _
    have h3 : s ^ q ≤ r ^ q := pow_le_pow_left₀ hs hsr _
    have h4 : (3 * (r * s)) ^ (q + 2) * r ^ (2 * p) ≤ 3 ^ (q + 2) * (r ^ (2 * (q + p) + 2) * s ^ 2) := by
      have : (3 * (r * s)) ^ (q + 2) * r ^ (2 * p) = 3 ^ (q + 2) * (r ^ (q + 2 + 2 * p) * s ^ 2 * s ^ q) := by
        ring
      rw [this]
      have : r ^ (2 * (q + p) + 2) * s ^ 2 = r ^ (q + 2 + 2 * p) * s ^ 2 * r ^ q := by ring
      rw [this]
      gcongr
    have : 0 ≤ s ^ (2 * (q + 2 + p)) := by positivity
    calc _ ≤ (3 * (r * s)) ^ (q + 2) * r ^ (2 * p) := by gcongr
      _ ≤ _ := by nlinarith [pow_nonneg (show (0:ℝ) ≤ 3 by norm_num) (q + 2)]
  · have h1 : 2 * r * s + s ^ 2 ≤ 3 * s ^ 2 := by nlinarith
    have h3 : r ^ (2 * p) ≤ s ^ (2 * p) := pow_le_pow_left₀ hr hrs _
    calc (2 * r * s + s ^ 2) ^ (q + 2) * r ^ (2 * p) ≤ (3 * s ^ 2) ^ (q + 2) * s ^ (2 * p) := by
          gcongr
      _ = 3 ^ (q + 2) * s ^ (2 * (q + 2 + p)) := by ring
      _ ≤ _ := by
          have : 0 ≤ r ^ (2 * (q + p) + 2) * s ^ 2 := by positivity
          nlinarith [pow_nonneg (show (0:ℝ) ≤ 3 by norm_num) (q + 2)]

end Occ34

open MeasureTheory Filter Topology

namespace Occ34

lemma sum_choose_tail (k : ℕ) :
    (∑ j ∈ Finset.range k, ((k + 1).choose (j + 2) : ℝ)) ≤ 2 ^ (k + 1) := by
  have h := Nat.sum_range_choose (k + 1)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
  have : (∑ j ∈ Finset.range k, (k + 1).choose (j + 2)) ≤ 2 ^ (k + 1) := by
    rw [← h]; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  exact_mod_cast this

lemma binom_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x w : V) (k : ℕ) :
    ‖x + w‖ ^ (2 * (k + 1)) ≤ ‖x‖ ^ (2 * (k + 1))
      + (k + 1) * ‖x‖ ^ (2 * k) * (2 * inner ℝ x w + ‖w‖ ^ 2)
      + 6 ^ (k + 1) * (‖x‖ ^ (2 * k) * ‖w‖ ^ 2 + ‖w‖ ^ (2 * (k + 1))) := by
  set r := ‖x‖ with hr
  set s := ‖w‖ with hs
  set u : ℝ := 2 * inner ℝ x w + s ^ 2 with hu
  have hr0 : 0 ≤ r := norm_nonneg _
  have hs0 : 0 ≤ s := norm_nonneg _
  have hxw : |inner ℝ x w| ≤ r * s := abs_real_inner_le_norm x w
  have hu_abs : |u| ≤ 2 * r * s + s ^ 2 := by
    have h := abs_add_le (2 * inner ℝ x w) (s ^ 2)
    rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg s)] at h
    rw [hu]; linarith
  have hnorm : ‖x + w‖ ^ (2 * (k + 1)) = (u + r ^ 2) ^ (k + 1) := by
    rw [pow_mul, norm_add_sq_real, hu, hr, hs]; ring_nf
  set Q := r ^ (2 * k) * s ^ 2 + s ^ (2 * (k + 1)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  rw [hnorm, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  have hterm : ∀ j ∈ Finset.range k,
      u ^ (j + 1 + 1) * (r ^ 2) ^ (k + 1 - (j + 1 + 1)) * ((k + 1).choose (j + 1 + 1) : ℝ)
        ≤ ((k + 1).choose (j + 2) : ℝ) * (3 ^ (k + 1) * Q) := by
    intro j hj
    rw [show j + 1 + 1 = j + 2 by ring]
    rw [Finset.mem_range] at hj
    obtain ⟨p, rfl⟩ : ∃ p, k = j + 1 + p := ⟨k - j - 1, by omega⟩
    have he : j + 1 + p + 1 - (j + 2) = p := by omega
    rw [he, ← pow_mul]
    have hc : (0 : ℝ) ≤ ((j + 1 + p + 1).choose (j + 2) : ℝ) := by positivity
    have h1 : u ^ (j + 2) ≤ (2 * r * s + s ^ 2) ^ (j + 2) := by
      calc u ^ (j + 2) ≤ |u| ^ (j + 2) := by
            rw [← abs_pow]; exact le_abs_self _
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hu_abs _
    have h2 := mono_bound r s hr0 hs0 p j
    have h3 : (3 : ℝ) ^ (j + 2) ≤ 3 ^ (j + 1 + p + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hQ' : Q = r ^ (2 * (j + p) + 2) * s ^ 2 + s ^ (2 * (j + 2 + p)) := by
      rw [hQ]; ring_nf
    rw [hQ'] at hQ0 ⊢
    have h4 : u ^ (j + 2) * r ^ (2 * p) ≤ 3 ^ (j + 1 + p + 1) *
        (r ^ (2 * (j + p) + 2) * s ^ 2 + s ^ (2 * (j + 2 + p))) := by
      calc u ^ (j + 2) * r ^ (2 * p) ≤ (2 * r * s + s ^ 2) ^ (j + 2) * r ^ (2 * p) := by
            gcongr
        _ ≤ _ := h2
        _ ≤ _ := by gcongr
    calc u ^ (j + 2) * r ^ (2 * p) * ((j + 1 + p + 1).choose (j + 2) : ℝ)
        ≤ 3 ^ (j + 1 + p + 1) * (r ^ (2 * (j + p) + 2) * s ^ 2 + s ^ (2 * (j + 2 + p)))
          * ((j + 1 + p + 1).choose (j + 2) : ℝ) := by gcongr
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hch := sum_choose_tail k
  have h6 : (∑ j ∈ Finset.range k, ((k + 1).choose (j + 2) : ℝ)) * (3 ^ (k + 1) * Q)
      ≤ 6 ^ (k + 1) * Q := by
    calc _ ≤ 2 ^ (k + 1) * (3 ^ (k + 1) * Q) := by gcongr
      _ = 6 ^ (k + 1) * Q := by rw [show (6:ℝ) = 2 * 3 by norm_num, mul_pow]; ring
  have h1 : u ^ (0 + 1) * (r ^ 2) ^ (k + 1 - (0 + 1)) * ((k + 1).choose (0 + 1) : ℝ)
      = (k + 1) * r ^ (2 * k) * u := by
    rw [Nat.zero_add, Nat.add_sub_cancel, Nat.choose_one_right, pow_one, ← pow_mul]; push_cast; ring
  have h0 : u ^ 0 * (r ^ 2) ^ (k + 1 - 0) * ((k + 1).choose 0 : ℝ) = r ^ (2 * (k + 1)) := by
    rw [pow_zero, Nat.sub_zero, Nat.choose_zero_right, ← pow_mul]; push_cast; ring
  rw [h1, h0]
  linarith [hsum, h6]

end Occ34

open MeasureTheory Filter Topology
open scoped NNReal

namespace Occ34

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma path_bound (b : V → V) (a L : ℝ) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hb : ∀ y, ‖b y‖ ≤ a + L * ‖y‖) (S : V →L[ℝ] V) (Bp : ℝ≥0 → V) (hBc : Continuous Bp)
    (Xp : ℝ≥0 → V) (hXc : Continuous Xp) (x : V)
    (hX : ∀ t : ℝ≥0, Xp t = x + (∫ s in (0:ℝ)..(t:ℝ), b (Xp s.toNNReal)) + S (Bp t))
    (t : ℝ≥0) :
    ‖Xp t - x - S (Bp t)‖ ≤ ((t:ℝ) * (a + L * ‖x‖)
      + L * ‖S‖ * ∫ s in (0:ℝ)..(t:ℝ), ‖Bp s.toNNReal‖) * Real.exp (L * t) := by
  set u : ℝ → ℝ := fun s => ‖Xp s.toNNReal - x - S (Bp s.toNNReal)‖ with hu
  set β : ℝ → ℝ := fun s => ‖Bp s.toNNReal‖ with hβ
  set α : ℝ → ℝ := fun s => s * (a + L * ‖x‖) + L * ‖S‖ * ∫ r in (0:ℝ)..s, β r with hα
  have hβc : Continuous β := (continuous_norm.comp (hBc.comp continuous_real_toNNReal))
  have huc : Continuous u := by
    have h1 := hXc.comp continuous_real_toNNReal
    have h2 := S.continuous.comp (hBc.comp continuous_real_toNNReal)
    exact continuous_norm.comp ((h1.sub continuous_const).sub h2)
  have hx0 : 0 ≤ a + L * ‖x‖ := by positivity
  have hαm : MonotoneOn α (Set.Ici 0) := by
    intro s1 hs1 s2 hs2 h12
    simp only [hα]
    have : (∫ r in (0:ℝ)..s1, β r) ≤ ∫ r in (0:ℝ)..s2, β r :=
      intervalIntegral.integral_mono_interval le_rfl hs1 h12
        (Eventually.of_forall fun r => norm_nonneg _) (hβc.intervalIntegrable _ _)
    have h3 : 0 ≤ L * ‖S‖ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h3]
  have hmain : ∀ s, 0 ≤ s → u s ≤ α s + L * ∫ r in (0:ℝ)..s, u r := by
    intro s hs
    have hXs := hX s.toNNReal
    rw [Real.coe_toNNReal _ hs] at hXs
    have heq : Xp s.toNNReal - x - S (Bp s.toNNReal) = ∫ r in (0:ℝ)..s, b (Xp r.toNNReal) := by
      rw [hXs]; abel
    have hg : Continuous (fun r => a + L * ‖x‖ + L * ‖S‖ * β r + L * u r) := by fun_prop
    have hle := intervalIntegral.norm_integral_le_of_norm_le (f := fun r => b (Xp r.toNNReal))
      (g := fun r => a + L * ‖x‖ + L * ‖S‖ * β r + L * u r) (μ := volume) hs
      (Eventually.of_forall fun r _ => by
        have h1 := hb (Xp r.toNNReal)
        have h2 : ‖Xp r.toNNReal‖ ≤ ‖x‖ + ‖S‖ * β r + u r := by
          have : Xp r.toNNReal = x + S (Bp r.toNNReal) + (Xp r.toNNReal - x - S (Bp r.toNNReal)) := by abel
          rw [this]
          calc _ ≤ ‖x + S (Bp r.toNNReal)‖ + u r := norm_add_le _ _
            _ ≤ ‖x‖ + ‖S (Bp r.toNNReal)‖ + u r := by gcongr; exact norm_add_le _ _
            _ ≤ _ := by gcongr; exact S.le_opNorm _
        nlinarith [mul_le_mul_of_nonneg_left h2 hL])
      (hg.intervalIntegrable _ _)
    have hcalc : (∫ r in (0:ℝ)..s, (a + L * ‖x‖ + L * ‖S‖ * β r + L * u r))
        = α s + L * ∫ r in (0:ℝ)..s, u r := by
      rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      · simp [hα]
      all_goals first
        | exact intervalIntegrable_const
        | exact ((continuous_const.mul hβc).intervalIntegrable _ _)
        | exact ((continuous_const.mul huc).intervalIntegrable _ _)
        | exact ((continuous_const.add (continuous_const.mul hβc)).intervalIntegrable _ _)
    calc u s = ‖∫ r in (0:ℝ)..s, b (Xp r.toNNReal)‖ := by simp only [hu]; rw [heq]
      _ ≤ _ := hle
      _ = _ := hcalc
  have := gronwall_int hL huc hαm hmain t t.2
  simpa [hu, hα, hβ] using this

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Occ34

noncomputable def G (i : ℕ) : ℝ := ∫ z, z ^ (2 * i) ∂(gaussianReal 0 1)

lemma G_nonneg (i : ℕ) : 0 ≤ G i :=
  integral_nonneg fun z => by rw [pow_mul]; positivity

lemma gauss_integrable (v : ℝ≥0) (i : ℕ) :
    Integrable (fun z : ℝ => z ^ (2 * i)) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((2 * i : ℕ) : ℝ≥0∞)
    (ENNReal.natCast_ne_top _)).integrable_norm_pow'
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp [Real.norm_eq_abs, pow_mul, sq_abs]

lemma gauss_moment (v : ℝ≥0) (i : ℕ) :
    ∫ z, z ^ (2 * i) ∂(gaussianReal 0 v) = (v : ℝ) ^ i * G i := by
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun z => √(v:ℝ) * z) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have h : ∀ z : ℝ, (√(v:ℝ) * z) ^ (2 * i) = (v:ℝ) ^ i * z ^ (2 * i) := by
    intro z; rw [mul_pow, pow_mul (√(v:ℝ)), Real.sq_sqrt (NNReal.coe_nonneg v)]
  simp only [h]
  rw [integral_const_mul]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma hasLaw_moment {Y : Ω → ℝ} {v : ℝ≥0} (hY : HasLaw Y (gaussianReal 0 v) P) (i : ℕ) :
    Integrable (fun ω => Y ω ^ (2 * i)) P ∧ ∫ ω, Y ω ^ (2 * i) ∂P = (v : ℝ) ^ i * G i := by
  constructor
  · have h := gauss_integrable v i
    rw [← hY.map_eq] at h
    exact (integrable_map_measure (continuous_pow _).aestronglyMeasurable hY.aemeasurable).mp h
  · have := hY.integral_comp (f := fun z : ℝ => z ^ (2 * i)) (continuous_pow _).aestronglyMeasurable
    simp only [Function.comp_def] at this
    rw [this, gauss_moment]

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

lemma pow_sum_le_card {d : ℕ} (f : Fin d → ℝ) (hf : ∀ l, 0 ≤ f l) (j : ℕ) :
    (∑ l, f l) ^ (j + 1) ≤ (d : ℝ) ^ j * ∑ l, f l ^ (j + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have h := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := f) (fun l _ => hf l) j
  rw [Finset.card_univ, Fintype.card_fin, div_le_iff₀ (by positivity)] at h
  linarith [h, mul_comm ((d:ℝ) ^ j) (∑ l, f l ^ (j + 1))]

lemma G_zero : G 0 = 1 := by simp [G]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

lemma bm_coord {B : ℝ≥0 → Ω → E d} (hB : EthierKurtz.IsStandardBrownian P B) (l : Fin d)
    (t : ℝ≥0) : HasLaw (fun ω => B t ω l) (gaussianReal 0 t) P :=
  (hB.2.2.1 l).toIsPreBrownianReal.hasLaw_eval t

lemma bm_moment [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (t : ℝ≥0) (i : ℕ) :
    Integrable (fun ω => ‖B t ω‖ ^ (2 * i)) P ∧
      ∫ ω, ‖B t ω‖ ^ (2 * i) ∂P ≤ (d : ℝ) ^ i * G i * (t : ℝ) ^ i := by
  rcases i with _ | j
  · simp [G_zero]
  have hmeas : Measurable (B t) := hB.1 t
  have hpt : ∀ ω, ‖B t ω‖ ^ (2 * (j + 1)) ≤ ∑ l, (d : ℝ) ^ j * (B t ω l) ^ (2 * (j + 1)) := by
    intro ω
    rw [pow_mul, EuclideanSpace.real_norm_sq_eq, ← Finset.mul_sum]
    simp_rw [pow_mul]
    exact pow_sum_le_card _ (fun l => sq_nonneg _) j
  have hint : ∀ l, Integrable (fun ω => (d : ℝ) ^ j * (B t ω l) ^ (2 * (j + 1))) P :=
    fun l => ((hasLaw_moment (bm_coord hB l t) (j + 1)).1).const_mul _
  have hg := integrable_finsetSum (Finset.univ) (fun l _ => hint l)
  have hf : Integrable (fun ω => ‖B t ω‖ ^ (2 * (j + 1))) P := by
    refine hg.mono' (by fun_prop) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simpa using hpt ω
  refine ⟨hf, ?_⟩
  calc ∫ ω, ‖B t ω‖ ^ (2 * (j + 1)) ∂P
      ≤ ∫ ω, ∑ l, (d : ℝ) ^ j * (B t ω l) ^ (2 * (j + 1)) ∂P :=
        integral_mono hf (by simpa using hg) hpt
    _ = ∑ l : Fin d, (d : ℝ) ^ j * ((t : ℝ) ^ (j + 1) * G (j + 1)) := by
        rw [integral_finsetSum _ (fun l _ => hint l)]
        congr 1; ext l
        rw [integral_const_mul, (hasLaw_moment (bm_coord hB l t) (j + 1)).2]
    _ = _ := by simp [Finset.sum_const]; ring

lemma clm_expand (ℓ : E d →L[ℝ] ℝ) (v : E d) :
    ℓ v = ∑ l, v l * ℓ (EuclideanSpace.single l 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [map_sum, map_smul]

lemma bm_inner_mean [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (y : E d) (S : E d →L[ℝ] E d) (t : ℝ≥0) :
    Integrable (fun ω => inner ℝ y (S (B t ω))) P ∧ ∫ ω, inner ℝ y (S (B t ω)) ∂P = 0 := by
  set ℓ : E d →L[ℝ] ℝ := (innerSL ℝ y).comp S
  have hfun : (fun ω => inner ℝ y (S (B t ω))) =
      fun ω => ∑ l, B t ω l * ℓ (EuclideanSpace.single l 1) := by
    ext ω; rw [← clm_expand ℓ]; rfl
  have hint : ∀ l, Integrable (fun ω => B t ω l * ℓ (EuclideanSpace.single l 1)) P :=
    fun l => ((hB.2.2.1 l).toIsPreBrownianReal.integrable_eval t).mul_const _
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun l _ => hint l), ?_⟩
  rw [integral_finsetSum _ (fun l _ => hint l)]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [integral_mul_const]
  have := (hB.2.2.1 l).toIsPreBrownianReal.integral_eval t
  simp only at this
  rw [this, zero_mul]

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

lemma tangent_pow (y m : ℝ) (hy : 0 ≤ y) (hm : 0 ≤ m) (n : ℕ) :
    m ^ (n + 1) + (n + 1) * m ^ n * (y - m) ≤ y ^ (n + 1) := by
  rcases hm.eq_or_lt with rfl | hm
  · rcases n with _ | n
    · simp
    · simp; positivity
  · have hym : 0 ≤ y / m := by positivity
    have h := one_add_mul_le_pow (a := y / m - 1) (by linarith) (n + 1)
    have e1 : 1 + (y / m - 1) = y / m := by ring
    rw [e1, div_pow, le_div_iff₀ (by positivity)] at h
    have e : (1 + ((n + 1 : ℕ) : ℝ) * (y / m - 1)) * m ^ (n + 1)
        = m ^ (n + 1) + (n + 1) * m ^ n * (y - m) := by
      push_cast
      field_simp
      ring
    linarith

lemma jensen_pow (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ s, 0 ≤ f s) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) : (∫ s in (0:ℝ)..T, f s) ^ (n + 1) ≤ T ^ n * ∫ s in (0:ℝ)..T, f s ^ (n + 1) := by
  rcases hT.eq_or_lt with rfl | hT
  · simp
  set A := ∫ s in (0:ℝ)..T, f s with hA
  set m := A / T with hm_def
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hT.le (fun s _ => hf0 s)
  have hm : 0 ≤ m := div_nonneg hA0 hT.le
  have h1 : ∫ s in (0:ℝ)..T, (m ^ (n + 1) + (n + 1) * m ^ n * (f s - m))
      ≤ ∫ s in (0:ℝ)..T, f s ^ (n + 1) :=
    intervalIntegral.integral_mono_on hT.le (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (fun s _ => tangent_pow _ _ (hf0 s) hm n)
  have h2 : ∫ s in (0:ℝ)..T, (m ^ (n + 1) + (n + 1) * m ^ n * (f s - m)) = T * m ^ (n + 1) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const, ← hA]
    simp only [sub_zero, smul_eq_mul]
    have : T * m = A := by rw [hm_def]; field_simp
    rw [this]; ring
  have h3 : A ^ (n + 1) = T ^ n * (T * m ^ (n + 1)) := by
    have : A = T * m := by rw [hm_def]; field_simp
    rw [this]; ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left (h2 ▸ h1) (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

noncomputable def Jf (B : ℝ≥0 → Ω → E d) (T : ℝ) (p : ℕ) (ω : Ω) : ℝ :=
  ∫ s in (0:ℝ)..T, ‖B s.toNNReal ω‖ ^ p

lemma bm_cont {B : ℝ≥0 → Ω → E d} (hB : EthierKurtz.IsStandardBrownian P B) (p : ℕ) (ω : Ω) :
    Continuous (fun s : ℝ => ‖B s.toNNReal ω‖ ^ p) :=
  (continuous_norm.comp ((hB.2.1 ω).comp continuous_real_toNNReal)).pow p

lemma meas_swap_gen (f : ℝ → Ω → ℝ) (hc : ∀ ω, Continuous fun s => f s ω)
    (hm : ∀ s, Measurable (f s)) : Measurable (fun q : Ω × ℝ => f q.2 q.1) := by
  have h : Measurable (Function.uncurry f) := measurable_uncurry_of_continuous_of_measurable hc hm
  have := h.comp (measurable_swap (α := Ω) (β := ℝ))
  exact this

lemma jointly_meas {B : ℝ≥0 → Ω → E d} (hB : EthierKurtz.IsStandardBrownian P B) (p : ℕ) :
    Measurable (fun q : Ω × ℝ => ‖B q.2.toNNReal q.1‖ ^ p) :=
  meas_swap_gen (fun s ω => ‖B s.toNNReal ω‖ ^ p) (fun ω => bm_cont hB p ω)
    (fun s => ((hB.1 s.toNNReal).norm).pow_const p)

lemma Jf_nonneg (B : ℝ≥0 → Ω → E d) (T : ℝ) (hT : 0 ≤ T) (p : ℕ) (ω : Ω) : 0 ≤ Jf B T p ω :=
  intervalIntegral.integral_nonneg hT (fun s _ => by positivity)

lemma Jf_meas {B : ℝ≥0 → Ω → E d} (hB : EthierKurtz.IsStandardBrownian P B) (T : ℝ) (hT : 0 ≤ T)
    (p : ℕ) : Measurable (Jf B T p) := by
  have h := (jointly_meas hB p).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc 0 T))
  have : Jf B T p = fun ω => ∫ s in Set.Ioc 0 T, ‖B s.toNNReal ω‖ ^ p := by
    ext ω; simp only [Jf]; rw [intervalIntegral.integral_of_le hT]
  rw [this]; exact h.measurable

lemma Jf_moment [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (T : ℝ) (hT : 0 ≤ T) (i : ℕ) :
    Integrable (Jf B T (2 * i)) P ∧
      ∫ ω, Jf B T (2 * i) ω ∂P ≤ (d : ℝ) ^ i * G i * T ^ (i + 1) := by
  set K := (d : ℝ) ^ i * G i with hK
  have hK0 : 0 ≤ K := by have := G_nonneg i; positivity
  have hofr : ∀ ω, ENNReal.ofReal (Jf B T (2 * i) ω)
      = ∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (‖B s.toNNReal ω‖ ^ (2 * i)) := by
    intro ω
    simp only [Jf]
    rw [intervalIntegral.integral_of_le hT, ofReal_integral_eq_lintegral_ofReal]
    · exact ((bm_cont hB (2 * i) ω).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact Eventually.of_forall fun s => by positivity
  have hlin : ∫⁻ ω, ENNReal.ofReal (Jf B T (2 * i) ω) ∂P ≤ ENNReal.ofReal (K * T ^ (i + 1)) := by
    simp_rw [hofr]
    rw [lintegral_lintegral_swap]
    · calc ∫⁻ s in Set.Ioc 0 T, ∫⁻ ω, ENNReal.ofReal (‖B s.toNNReal ω‖ ^ (2 * i)) ∂P
          ≤ ∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (K * T ^ i) := by
            refine setLIntegral_mono measurable_const fun s hs => ?_
            have hm := bm_moment hB s.toNNReal i
            rw [← ofReal_integral_eq_lintegral_ofReal hm.1
              (Eventually.of_forall fun ω => by positivity)]
            apply ENNReal.ofReal_le_ofReal
            calc _ ≤ _ := hm.2
              _ ≤ K * T ^ i := by
                rw [hK]
                have : (s.toNNReal : ℝ) ≤ T := by
                  rw [Real.coe_toNNReal _ hs.1.le]; exact hs.2
                gcongr
        _ = ENNReal.ofReal (K * T ^ (i + 1)) := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
              ← ENNReal.ofReal_mul (by positivity)]
            ring_nf
    · exact (ENNReal.measurable_ofReal.comp (jointly_meas hB (2 * i))).aemeasurable
  have hnn : 0 ≤ᵐ[P] Jf B T (2 * i) := Eventually.of_forall fun ω => Jf_nonneg B T hT _ ω
  have hint : Integrable (Jf B T (2 * i)) P :=
    ⟨(Jf_meas hB T hT _).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hint.1]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

lemma I_moment [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (Jf B T 1) P ∧ ∫ ω, Jf B T 1 ω ∂P ≤ T / 2 + d * G 1 * T ^ 2 / 2 := by
  have hpt : ∀ ω, Jf B T 1 ω ≤ T / 2 + Jf B T (2 * 1) ω / 2 := by
    intro ω
    simp only [Jf]
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (f := fun s => ‖B s.toNNReal ω‖ ^ 1)
      (g := fun s => 1 / 2 + ‖B s.toNNReal ω‖ ^ (2 * 1) / 2) hT
      ((bm_cont hB 1 ω).intervalIntegrable 0 T)
      ((continuous_const.add ((bm_cont hB (2 * 1) ω).div_const 2)).intervalIntegrable 0 T)
      (fun s _ => by
        have := sq_nonneg (‖B s.toNNReal ω‖ - 1)
        show ‖B s.toNNReal ω‖ ^ 1 ≤ 1 / 2 + ‖B s.toNNReal ω‖ ^ (2 * 1) / 2
        nlinarith)
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (((bm_cont hB (2 * 1) ω).div_const 2).intervalIntegrable 0 T),
      intervalIntegral.integral_const, intervalIntegral.integral_div] at h
    simp only [sub_zero, smul_eq_mul] at h
    linarith
  have hJ := Jf_moment hB T hT 1
  have hg : Integrable (fun ω => T / 2 + Jf B T (2 * 1) ω / 2) P :=
    (integrable_const _).add (hJ.1.div_const 2)
  have hint : Integrable (Jf B T 1) P :=
    hg.mono' (Jf_meas hB T hT 1).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (Jf_nonneg B T hT 1 ω)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, Jf B T 1 ω ∂P ≤ ∫ ω, (T / 2 + Jf B T (2 * 1) ω / 2) ∂P := integral_mono hint hg hpt
    _ = T / 2 + (∫ ω, Jf B T (2 * 1) ω ∂P) / 2 := by
        rw [integral_add (integrable_const _) (hJ.1.div_const 2), integral_const, integral_div]
        simp
    _ ≤ _ := by
        have := hJ.2
        simp only [pow_one, show (1:ℕ) + 1 = 2 from rfl] at this
        linarith

lemma I_pow_moment [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (T : ℝ) (hT : 0 ≤ T) (j : ℕ) :
    Integrable (fun ω => Jf B T 1 ω ^ (2 * (j + 1))) P ∧
      ∫ ω, Jf B T 1 ω ^ (2 * (j + 1)) ∂P
        ≤ (d : ℝ) ^ (j + 1) * G (j + 1) * T ^ (3 * (j + 1)) := by
  have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
  have hpt : ∀ ω, Jf B T 1 ω ^ (2 * (j + 1)) ≤ T ^ (2 * j + 1) * Jf B T (2 * (j + 1)) ω := by
    intro ω
    have h := jensen_pow (fun s => ‖B s.toNNReal ω‖ ^ 1) (bm_cont hB 1 ω)
      (fun s => by positivity) T hT (2 * j + 1)
    simp only [← pow_mul, one_mul] at h
    rw [e]
    exact h
  have hJ := Jf_moment hB T hT (j + 1)
  have hg : Integrable (fun ω => T ^ (2 * j + 1) * Jf B T (2 * (j + 1)) ω) P :=
    hJ.1.const_mul _
  have hint : Integrable (fun ω => Jf B T 1 ω ^ (2 * (j + 1))) P :=
    hg.mono' ((Jf_meas hB T hT 1).pow_const _).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (Jf_nonneg B T hT 1 ω) _)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ ω, T ^ (2 * j + 1) * Jf B T (2 * (j + 1)) ω ∂P := integral_mono hint hg hpt
    _ = T ^ (2 * j + 1) * ∫ ω, Jf B T (2 * (j + 1)) ω ∂P := integral_const_mul _ _
    _ ≤ T ^ (2 * j + 1) * ((d : ℝ) ^ (j + 1) * G (j + 1) * T ^ (j + 1 + 1)) := by
        gcongr; exact hJ.2
    _ = _ := by ring

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

lemma mono_W (Ex T : ℝ) (hEx : 1 ≤ Ex) (hT : 0 ≤ T) (k p q : ℕ) (hp : p ≤ 2 * (k + 1))
    (hq1 : 1 ≤ q) (hq : q ≤ 3 * (k + 1) + 1) :
    Ex ^ p * T ^ q ≤ T * (1 + T) ^ (3 * (k + 1)) * Ex ^ (2 * (k + 1)) := by
  have h1 : Ex ^ p ≤ Ex ^ (2 * (k + 1)) := pow_le_pow_right₀ hEx hp
  have h2 : T ^ q ≤ T * (1 + T) ^ (3 * (k + 1)) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [pow_succ, mul_comm]
    gcongr
    calc T ^ q' ≤ (1 + T) ^ q' := pow_le_pow_left₀ hT (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 : 0 ≤ T ^ q := by positivity
  have h4 : 0 ≤ Ex ^ (2 * (k + 1)) := by positivity
  calc Ex ^ p * T ^ q ≤ Ex ^ (2 * (k + 1)) * T ^ q := by gcongr
    _ ≤ Ex ^ (2 * (k + 1)) * (T * (1 + T) ^ (3 * (k + 1))) := by gcongr
    _ = _ := by ring

/-- The `x`-free constant. -/
noncomputable def Kc (A L c : ℝ) (d k : ℕ) : ℝ :=
  let n : ℝ := k + 1
  let m : ℝ := (k + 1 : ℝ) + 6 ^ (k + 1)
  let q : ℝ := 2 ^ (2 * (k + 1) - 1)
  2 * n * A + m * (4 * A ^ 2 + q * q * A ^ (2 * (k + 1)))
    + 2 * n * L * c * (1 / 2 + d * G 1 / 2)
    + m * 4 * (L * c) ^ 2 * (d * G 1)
    + m * q * q * (L * c) ^ (2 * (k + 1)) * ((d : ℝ) ^ (k + 1) * G (k + 1))
    + m * 2 * c ^ 2 * (d * G 1)
    + m * q * c ^ (2 * (k + 1)) * ((d : ℝ) ^ (k + 1) * G (k + 1))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

lemma integral_lin6 [IsProbabilityMeasure P] {f1 f2 f3 f4 f5 : Ω → ℝ}
    (h1 : Integrable f1 P) (h2 : Integrable f2 P) (h3 : Integrable f3 P) (h4 : Integrable f4 P)
    (h5 : Integrable f5 P) (c0 a1 a2 a3 a4 a5 : ℝ) :
    ∫ ω, (c0 + a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω + a5 * f5 ω) ∂P
      = c0 + a1 * ∫ ω, f1 ω ∂P + a2 * ∫ ω, f2 ω ∂P + a3 * ∫ ω, f3 ω ∂P
        + a4 * ∫ ω, f4 ω ∂P + a5 * ∫ ω, f5 ω ∂P := by
  have i1 : Integrable (fun ω => c0 + a1 * f1 ω) P := (integrable_const c0).add (h1.const_mul a1)
  have i2 : Integrable (fun ω => c0 + a1 * f1 ω + a2 * f2 ω) P := i1.add (h2.const_mul a2)
  have i3 : Integrable (fun ω => c0 + a1 * f1 ω + a2 * f2 ω + a3 * f3 ω) P :=
    i2.add (h3.const_mul a3)
  have i4 : Integrable (fun ω => c0 + a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω) P :=
    i3.add (h4.const_mul a4)
  rw [integral_add i4 (h5.const_mul a5), integral_add i3 (h4.const_mul a4),
    integral_add i2 (h3.const_mul a3), integral_add i1 (h2.const_mul a2),
    integral_add (integrable_const c0) (h1.const_mul a1), integral_const,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  simp

/-- The `x`-free random variable `Φ` and its expectation bound. -/
lemma Phi_bound [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (A L c : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hc : 0 ≤ c) (k : ℕ) (t : ℝ≥0) :
    let T : ℝ := t
    let Ex : ℝ := Real.exp (L * T)
    let Dl : Ω → ℝ := fun ω => Ex * (T * A + L * c * Jf B T 1 ω)
    let Zl : Ω → ℝ := fun ω => Dl ω + c * ‖B t ω‖
    let Phi : Ω → ℝ := fun ω => 2 * (k + 1) * Dl ω
      + ((k + 1 : ℝ) + 6 ^ (k + 1)) * (Zl ω ^ 2 + Zl ω ^ (2 * (k + 1)))
    Integrable Phi P ∧
      ∫ ω, Phi ω ∂P ≤ Kc A L c d k * (T * (1 + T) ^ (3 * (k + 1)) * Ex ^ (2 * (k + 1))) := by
  intro T Ex Dl Zl Phi
  have hT : 0 ≤ T := t.2
  have hEx : 1 ≤ Ex := Real.one_le_exp (by positivity)
  have w1 := mono_W Ex T hEx hT k 1 1 (by omega) le_rfl (by omega)
  have w2 := mono_W Ex T hEx hT k 1 2 (by omega) (by omega) (by omega)
  have w3 := mono_W Ex T hEx hT k 2 2 (by omega) (by omega) (by omega)
  have w4 := mono_W Ex T hEx hT k (2 * (k + 1)) (2 * (k + 1)) le_rfl (by omega) (by omega)
  have w5 := mono_W Ex T hEx hT k 2 3 (by omega) (by omega) (by omega)
  have w6 := mono_W Ex T hEx hT k (2 * (k + 1)) (3 * (k + 1)) le_rfl (by omega) (by omega)
  have w7 := mono_W Ex T hEx hT k 0 1 (by omega) le_rfl (by omega)
  have w8 := mono_W Ex T hEx hT k 0 (k + 1) (by omega) (by omega) (by omega)
  simp only [pow_one, pow_zero, one_mul] at w1 w2 w3 w4 w5 w6 w7 w8
  set n : ℝ := k + 1 with hn
  set m : ℝ := (k + 1 : ℝ) + 6 ^ (k + 1) with hm
  set q : ℝ := 2 ^ (2 * (k + 1) - 1) with hq
  have hm0 : 0 ≤ m := by positivity
  have hq0 : 0 ≤ q := by positivity
  set N := 2 * (k + 1) with hN
  -- atoms
  set I : Ω → ℝ := Jf B T 1
  have hI0 : ∀ ω, 0 ≤ I ω := fun ω => Jf_nonneg B T hT 1 ω
  set Psi : Ω → ℝ := fun ω =>
    (2 * n * Ex * T * A + m * (4 * Ex ^ 2 * T ^ 2 * A ^ 2 + q * q * Ex ^ N * T ^ N * A ^ N))
    + (2 * n * Ex * L * c) * I ω
    + (m * 4 * Ex ^ 2 * (L * c) ^ 2) * I ω ^ (2 * (0 + 1))
    + (m * q * q * Ex ^ N * (L * c) ^ N) * I ω ^ (2 * (k + 1))
    + (m * 2 * c ^ 2) * ‖B t ω‖ ^ (2 * 1)
    + (m * q * c ^ N) * ‖B t ω‖ ^ (2 * (k + 1)) with hPsi
  have hpt : ∀ ω, Phi ω ≤ Psi ω := by
    clear w1 w2 w3 w4 w5 w6 w7 w8
    intro ω
    have hD0 : 0 ≤ Dl ω := by have := hI0 ω; positivity
    have hb0 : 0 ≤ ‖B t ω‖ := norm_nonneg _
    have hZ2 : Zl ω ^ 2 ≤ 2 * Dl ω ^ 2 + 2 * c ^ 2 * ‖B t ω‖ ^ 2 := by
      simp only [Zl]; nlinarith [sq_nonneg (Dl ω - c * ‖B t ω‖)]
    have hD2 : Dl ω ^ 2 ≤ 2 * Ex ^ 2 * T ^ 2 * A ^ 2 + 2 * Ex ^ 2 * (L * c) ^ 2 * I ω ^ 2 := by
      simp only [Dl]
      nlinarith [sq_nonneg (T * A - L * c * I ω), sq_nonneg Ex]
    have hZn : Zl ω ^ N ≤ q * Dl ω ^ N + q * c ^ N * ‖B t ω‖ ^ N := by
      have := add_pow_le hD0 (mul_nonneg hc hb0) N
      rw [mul_pow c, ← hq] at this; simp only [Zl]; linarith
    have hDn : Dl ω ^ N ≤ q * Ex ^ N * T ^ N * A ^ N + q * Ex ^ N * (L * c) ^ N * I ω ^ N := by
      have h := add_pow_le (mul_nonneg hT hA) (mul_nonneg (mul_nonneg hL hc) (hI0 ω)) N
      have hE : 0 ≤ Ex ^ N := by positivity
      simp only [Dl]
      rw [mul_pow]
      change Ex ^ N * (T * A + L * c * I ω) ^ N ≤ _
      have := mul_le_mul_of_nonneg_left h hE
      rw [← hq, mul_pow T, mul_pow (L * c)] at this
      linarith [this]
    have e1 : I ω ^ (2 * (0 + 1)) = I ω ^ 2 := by norm_num
    have e2 : ‖B t ω‖ ^ (2 * 1) = ‖B t ω‖ ^ 2 := by norm_num
    simp only [Psi, Phi, e1, e2]
    rw [← hN] 
    have k1 := mul_le_mul_of_nonneg_left hZ2 hm0
    have k2 := mul_le_mul_of_nonneg_left hD2 (by positivity : (0:ℝ) ≤ m * 2)
    have k3 := mul_le_mul_of_nonneg_left hZn hm0
    have k4 := mul_le_mul_of_nonneg_left hDn (by positivity : (0:ℝ) ≤ m * q)
    have k5 : 2 * n * Dl ω = 2 * n * Ex * T * A + 2 * n * Ex * L * c * I ω := by
      simp only [Dl]; ring
    linarith [k1, k2, k3, k4, k5]
  have hIm := I_moment hB T hT
  have hI2 := I_pow_moment hB T hT 0
  have hIN := I_pow_moment hB T hT k
  have hb2 := bm_moment hB t 1
  have hbN := bm_moment hB t (k + 1)
  have hPsiEq := integral_lin6 hIm.1 hI2.1 hIN.1 hb2.1 hbN.1
    (2 * n * Ex * T * A + m * (4 * Ex ^ 2 * T ^ 2 * A ^ 2 + q * q * Ex ^ N * T ^ N * A ^ N))
    (2 * n * Ex * L * c) (m * 4 * Ex ^ 2 * (L * c) ^ 2) (m * q * q * Ex ^ N * (L * c) ^ N)
    (m * 2 * c ^ 2) (m * q * c ^ N)
  have hPsiInt : Integrable Psi P :=
    (((((integrable_const _).add (hIm.1.const_mul _)).add (hI2.1.const_mul _)).add
      (hIN.1.const_mul _)).add (hb2.1.const_mul _)).add (hbN.1.const_mul _)
  have hPhi0 : ∀ ω, 0 ≤ Phi ω := by
    intro ω
    have := hI0 ω
    have hD0 : 0 ≤ Dl ω := by positivity
    have hZ0 : 0 ≤ Zl ω := by simp only [Zl]; positivity
    simp only [Phi]; positivity
  have hPhim : Measurable Phi := by
    have hJm := Jf_meas hB T hT 1
    have hBm := hB.1 t
    simp only [Phi, Zl, Dl]
    fun_prop
  have hPhiInt : Integrable Phi P :=
    hPsiInt.mono' hPhim.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hPhi0 ω)]; exact hpt ω)
  refine ⟨hPhiInt, ?_⟩
  have hG1 := G_nonneg 1
  have hGk := G_nonneg (k + 1)
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : 0 ≤ n := by positivity
  have hKc : Kc A L c d k = 2 * n * A + m * (4 * A ^ 2 + q * q * A ^ N)
    + 2 * n * L * c * (1 / 2 + d * G 1 / 2)
    + m * 4 * (L * c) ^ 2 * (d * G 1)
    + m * q * q * (L * c) ^ N * ((d : ℝ) ^ (k + 1) * G (k + 1))
    + m * 2 * c ^ 2 * (d * G 1)
    + m * q * c ^ N * ((d : ℝ) ^ (k + 1) * G (k + 1)) := rfl
  have hEx0 : 0 ≤ Ex := by linarith
  calc ∫ ω, Phi ω ∂P ≤ ∫ ω, Psi ω ∂P := integral_mono hPhiInt hPsiInt hpt
    _ = _ := hPsiEq
    _ ≤ (2 * n * Ex * T * A + m * (4 * Ex ^ 2 * T ^ 2 * A ^ 2 + q * q * Ex ^ N * T ^ N * A ^ N))
        + (2 * n * Ex * L * c) * (T / 2 + d * G 1 * T ^ 2 / 2)
        + (m * 4 * Ex ^ 2 * (L * c) ^ 2) * ((d : ℝ) ^ (0 + 1) * G (0 + 1) * T ^ (3 * (0 + 1)))
        + (m * q * q * Ex ^ N * (L * c) ^ N) * ((d : ℝ) ^ (k + 1) * G (k + 1) * T ^ (3 * (k + 1)))
        + (m * 2 * c ^ 2) * ((d : ℝ) ^ 1 * G 1 * (t : ℝ) ^ 1)
        + (m * q * c ^ N) * ((d : ℝ) ^ (k + 1) * G (k + 1) * (t : ℝ) ^ (k + 1)) := by
        gcongr
        · exact hIm.2
        · exact hI2.2
        · exact hIN.2
        · exact hb2.2
        · exact hbN.2
    _ ≤ Kc A L c d k * (T * (1 + T) ^ (3 * (k + 1)) * Ex ^ (2 * (k + 1))) := by
        rw [hKc]
        simp only [pow_one, zero_add, mul_one]
        have e1 : (t : ℝ) = T := rfl
        rw [e1]
        have f1 := mul_le_mul_of_nonneg_left w1 (by positivity : 0 ≤ 2 * n * A)
        have f2 := mul_le_mul_of_nonneg_left w3 (by positivity : 0 ≤ m * 4 * A ^ 2)
        have f3 := mul_le_mul_of_nonneg_left w4 (by positivity : 0 ≤ m * q * q * A ^ N)
        have f4 := mul_le_mul_of_nonneg_left w1 (by positivity : 0 ≤ n * L * c)
        have f5 := mul_le_mul_of_nonneg_left w2 (by positivity : 0 ≤ n * L * c * d * G 1)
        have f6 := mul_le_mul_of_nonneg_left w5 (by positivity : 0 ≤ m * 4 * (L * c) ^ 2 * (d * G 1))
        have f7 := mul_le_mul_of_nonneg_left w6
          (by positivity : 0 ≤ m * q * q * (L * c) ^ N * ((d : ℝ) ^ (k + 1) * G (k + 1)))
        have f8 := mul_le_mul_of_nonneg_left w7 (by positivity : 0 ≤ m * 2 * c ^ 2 * (d * G 1))
        have f9 := mul_le_mul_of_nonneg_left w8
          (by positivity : 0 ≤ m * q * c ^ N * ((d : ℝ) ^ (k + 1) * G (k + 1)))
        linarith [f1, f2, f3, f4, f5, f6, f7, f8, f9]

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

lemma Kc_nonneg (A L c : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hc : 0 ≤ c) (d k : ℕ) :
    0 ≤ Kc A L c d k := by
  have h1 := G_nonneg 1
  have h2 := G_nonneg (k + 1)
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have e1 : 0 ≤ (d:ℝ) * G 1 := mul_nonneg hd h1
  have e2 : 0 ≤ (d:ℝ) ^ (k + 1) * G (k + 1) := mul_nonneg (by positivity) h2
  simp only [Kc]
  generalize (d:ℝ) * G 1 = u1 at e1 ⊢
  generalize (d:ℝ) ^ (k + 1) * G (k + 1) = u2 at e2 ⊢
  have : (0:ℝ) ≤ 1 / 2 + u1 / 2 := by linarith
  apply_rules [add_nonneg, mul_nonneg, pow_nonneg] <;> first | positivity | assumption

noncomputable def Cst (A L c : ℝ) (d k : ℕ) : ℝ :=
  2 ^ (2 * (k + 1) - 1) * Kc A L c d k + (3 * (k + 1) + 2 * (k + 1) * L)

lemma Cst_pos (A L c : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hc : 0 ≤ c) (d k : ℕ) :
    0 < Cst A L c d k := by
  have := Kc_nonneg A L c hA hL hc d k
  simp only [Cst]; positivity

/-- Final real inequality. -/
lemma final_real (r T K γ : ℝ) (hr : 0 ≤ r) (hT : 0 ≤ T) (hK : 0 ≤ K) (hγ : 0 ≤ γ) (N : ℕ) :
    r ^ N + K * T * Real.exp (γ * T) * (1 + r ^ N) ≤ Real.exp ((K + γ) * T) * (r ^ N + 1) := by
  have h1 : 1 ≤ Real.exp (γ * T) := Real.one_le_exp (by positivity)
  have h2 : 1 + K * T ≤ Real.exp (K * T) := by linarith [Real.add_one_le_exp (K * T)]
  have h3 : Real.exp ((K + γ) * T) = Real.exp (K * T) * Real.exp (γ * T) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  have hrN : 0 ≤ r ^ N := by positivity
  have h4 : (1 + K * T) * Real.exp (γ * T) ≤ Real.exp (K * T) * Real.exp (γ * T) := by gcongr
  have h5 : 0 ≤ K * T := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ 1 + r ^ N),
    mul_nonneg h5 (by positivity : (0:ℝ) ≤ Real.exp (γ * T))]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

theorem moment_even [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (b : E d → E d) (a L : ℝ) (ha : 0 ≤ a)
    (hL : 0 ≤ L) (hb : ∀ y, ‖b y‖ ≤ a + L * ‖y‖) (σ : Matrix (Fin d) (Fin d) ℝ)
    (X : E d → ℝ≥0 → Ω → E d) (hX : IsSolution b σ B X) (k : ℕ) (x : E d) (t : ℝ≥0) :
    ∫⁻ ω, ‖X x t ω‖ₑ ^ (2 * (k + 1)) ∂P ≤
      ENNReal.ofReal (Real.exp (Cst (a + L) L ‖mat σ‖ d k * t) * (‖x‖ ^ (2 * (k + 1)) + 1)) := by
  set S := mat σ with hS
  set c := ‖S‖ with hc_def
  set A := a + L with hA_def
  have hA : 0 ≤ A := by positivity
  have hc : 0 ≤ c := norm_nonneg _
  obtain ⟨hPhiInt, hPhiBd⟩ := Phi_bound hB A L c hA hL hc k t
  set T : ℝ := (t : ℝ) with hT_def
  have hT : 0 ≤ T := t.2
  set Ex := Real.exp (L * T) with hEx_def
  set N := 2 * (k + 1) with hN
  set r := ‖x‖ with hr_def
  have hr : 0 ≤ r := norm_nonneg _
  set R := 1 + r with hR_def
  have hR1 : 1 ≤ R := by linarith
  set Dl : Ω → ℝ := fun ω => Ex * (T * A + L * c * Jf B T 1 ω) with hDl
  set Zl : Ω → ℝ := fun ω => Dl ω + c * ‖B t ω‖ with hZl
  set Phi : Ω → ℝ := fun ω => 2 * (k + 1) * Dl ω
      + ((k + 1 : ℝ) + 6 ^ (k + 1)) * (Zl ω ^ 2 + Zl ω ^ N) with hPhi
  set F : Ω → ℝ := fun ω => r ^ N + (2 * (k + 1) * r ^ (2 * k)) * inner ℝ x (S (B t ω))
      + R ^ N * Phi ω with hF
  have hpt : ∀ ω, ‖X x t ω‖ ^ N ≤ F ω := by
    intro ω
    have hsol := hX x ω
    have hD := path_bound b a L ha hL hb S (fun s => B s ω) (hB.2.1 ω) (fun s => X x s ω)
      hsol.1 x hsol.2 t
    have hJ : Jf B T 1 ω = ∫ s in (0:ℝ)..T, ‖B s.toNNReal ω‖ := by simp [Jf, hT_def]
    have hI0 : 0 ≤ Jf B T 1 ω := Jf_nonneg B T hT 1 ω
    rw [← hJ] at hD
    set Dv := X x t ω - x - S (B t ω) with hDv
    set J := Jf B T 1 ω with hJdef
    have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
    have hDl0 : 0 ≤ Dl ω := by simp only [hDl]; positivity
    have hDlR : ‖Dv‖ ≤ R * Dl ω := by
      have e : T * (a + L * r) + L * c * J ≤ R * (T * A + L * c * J) := by
        simp only [hR_def, hA_def]
        nlinarith [mul_nonneg hT (mul_nonneg ha hr), mul_nonneg hT hL,
          mul_nonneg (mul_nonneg (mul_nonneg hL hc) hI0) hr]
      have := mul_le_mul_of_nonneg_right e hEx0
      calc ‖Dv‖ ≤ (T * (a + L * r) + L * c * J) * Ex := hD
        _ ≤ R * (T * A + L * c * J) * Ex := this
        _ = R * Dl ω := by simp only [hDl]; ring
    have hw : X x t ω = x + (Dv + S (B t ω)) := by simp only [hDv]; abel
    have hβ : ‖S (B t ω)‖ ≤ c * ‖B t ω‖ := S.le_opNorm _
    have hb0 : 0 ≤ ‖B t ω‖ := norm_nonneg _
    have hwn : ‖Dv + S (B t ω)‖ ≤ R * Zl ω := by
      calc ‖Dv + S (B t ω)‖ ≤ ‖Dv‖ + ‖S (B t ω)‖ := norm_add_le _ _
        _ ≤ R * Dl ω + c * ‖B t ω‖ := add_le_add hDlR hβ
        _ ≤ R * Dl ω + R * (c * ‖B t ω‖) := by
            have := le_mul_of_one_le_left (mul_nonneg hc hb0) hR1
            linarith
        _ = R * Zl ω := by simp only [hZl]; ring
    have hinn : inner ℝ x (Dv + S (B t ω)) ≤ r * (R * Dl ω) + inner ℝ x (S (B t ω)) := by
      rw [inner_add_right]
      have := real_inner_le_norm x Dv
      have := mul_le_mul_of_nonneg_left hDlR hr
      linarith
    have hbin := binom_bound x (Dv + S (B t ω)) k
    rw [← hw] at hbin
    set w := Dv + S (B t ω)
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    have hZ0 : 0 ≤ Zl ω := by simp only [hZl]; positivity
    have hR0 : 0 ≤ R := by linarith
    have hrR : r ≤ R := by linarith
    have hr2k : r ^ (2 * k) ≤ R ^ (2 * k) := pow_le_pow_left₀ hr hrR _
    have hRN : R ^ N = R ^ (2 * k) * R ^ 2 := by rw [hN, ← pow_add]; ring_nf
    have P1 : r ^ (2 * k) * ‖w‖ ^ 2 ≤ R ^ N * Zl ω ^ 2 := by
      have h2 : ‖w‖ ^ 2 ≤ R ^ 2 * Zl ω ^ 2 := by rw [← mul_pow]; gcongr
      rw [hRN, mul_assoc]
      exact mul_le_mul hr2k h2 (by positivity) (by positivity)
    have P2 : ‖w‖ ^ N ≤ R ^ N * Zl ω ^ N := by rw [← mul_pow]; gcongr
    have P3 : r ^ (2 * k) * (r * R) ≤ R ^ N := by
      rw [hRN, sq]
      exact mul_le_mul hr2k (mul_le_mul_of_nonneg_right hrR hR0) (by positivity) (by positivity)
    have hn0 : (0:ℝ) ≤ k + 1 := by positivity
    have hr2k0 : 0 ≤ r ^ (2 * k) := by positivity
    have Q1 := mul_le_mul_of_nonneg_left P1 (by positivity : (0:ℝ) ≤ (k + 1) + 6 ^ (k + 1))
    have Q2 := mul_le_mul_of_nonneg_left P2 (by positivity : (0:ℝ) ≤ 6 ^ (k + 1))
    have Q3 := mul_le_mul_of_nonneg_left P3 (by positivity : (0:ℝ) ≤ 2 * (k + 1) * Dl ω)
    have Q4 := mul_le_mul_of_nonneg_left hinn (by positivity : (0:ℝ) ≤ (k + 1) * r ^ (2 * k) * 2)
    simp only [hF, hPhi]
    rw [← hN] at hbin
    have Q5 : 0 ≤ ((k:ℝ) + 1) * (R ^ N * Zl ω ^ N) := by positivity
    linarith [hbin, Q1, Q2, Q3, Q4, Q5]
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => le_trans (by positivity) (hpt ω)
  have hinner := bm_inner_mean hB x S t
  have hi1 : Integrable (fun ω => r ^ N + (2 * (k + 1) * r ^ (2 * k)) * inner ℝ x (S (B t ω))) P :=
    (integrable_const _).add (hinner.1.const_mul _)
  have hFint : Integrable F P := hi1.add (hPhiInt.const_mul _)
  have hFeq : ∫ ω, F ω ∂P = r ^ N + R ^ N * ∫ ω, Phi ω ∂P := by
    simp only [hF]
    rw [integral_add hi1 (hPhiInt.const_mul _), integral_add (integrable_const _)
      (hinner.1.const_mul _), integral_const, integral_const_mul, integral_const_mul, hinner.2]
    simp
  set q : ℝ := 2 ^ (N - 1) with hq
  set γ : ℝ := 3 * (k + 1) + 2 * (k + 1) * L with hγ
  have hKc0 := Kc_nonneg A L c hA hL hc d k
  have hq0 : 0 ≤ q := by positivity
  have hγ0 : 0 ≤ γ := by positivity
  have hCst : Cst A L c d k = q * Kc A L c d k + γ := by simp only [Cst, hq, hγ, hN]
  have hRN : R ^ N ≤ q * (1 + r ^ N) := by
    have := add_pow_le zero_le_one hr N
    simpa [hR_def, hq] using this
  have hTexp : (1 + T) ^ (3 * (k + 1)) * Ex ^ N ≤ Real.exp (γ * T) := by
    have h1 : (1 + T) ^ (3 * (k + 1)) ≤ Real.exp T ^ (3 * (k + 1)) :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp T]) _
    have h2 : Real.exp T ^ (3 * (k + 1)) * Ex ^ N = Real.exp (γ * T) := by
      rw [hEx_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, hγ, hN]
      congr 1; push_cast; ring
    rw [← h2]; gcongr
  have hPhiBd' : R ^ N * ∫ ω, Phi ω ∂P ≤ q * Kc A L c d k * T * Real.exp (γ * T) * (1 + r ^ N) := by
    have hR00 : 0 ≤ R := by linarith
    have hR0 : 0 ≤ R ^ N := pow_nonneg hR00 N
    calc R ^ N * ∫ ω, Phi ω ∂P ≤ R ^ N * (Kc A L c d k * (T * (1 + T) ^ (3 * (k + 1)) * Ex ^ N)) :=
          mul_le_mul_of_nonneg_left hPhiBd hR0
      _ = R ^ N * (Kc A L c d k * T) * ((1 + T) ^ (3 * (k + 1)) * Ex ^ N) := by ring
      _ ≤ (q * (1 + r ^ N)) * (Kc A L c d k * T) * Real.exp (γ * T) := by
          gcongr
      _ = _ := by ring
  calc ∫⁻ ω, ‖X x t ω‖ₑ ^ N ∂P ≤ ∫⁻ ω, ENNReal.ofReal (F ω) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, F ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hFint (Eventually.of_forall hF0)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hFeq, hCst]
        have := final_real r T (q * Kc A L c d k) γ hr hT (by positivity) hγ0 N
        linarith

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

theorem moment_m [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E d}
    (hB : EthierKurtz.IsStandardBrownian P B) (b : E d → E d) (a L : ℝ) (ha : 0 ≤ a)
    (hL : 0 ≤ L) (hb : ∀ y, ‖b y‖ ≤ a + L * ‖y‖) (σ : Matrix (Fin d) (Fin d) ℝ)
    (X : E d → ℝ≥0 → Ω → E d) (hX : IsSolution b σ B X) (m : ℕ) (hm : 2 ≤ m) (x : E d)
    (t : ℝ≥0) :
    ∫⁻ ω, ‖X x t ω‖ₑ ^ m ∂P ≤
      ENNReal.ofReal (Real.exp (Cst (a + L) L ‖mat σ‖ d (m - 1) * t) * (‖x‖ ^ m + 1)) := by
  set C := Cst (a + L) L ‖mat σ‖ d (m - 1) with hC
  have hC0 : 0 < C := Cst_pos _ _ _ (by positivity) hL (norm_nonneg _) d _
  have h2m : 2 * (m - 1 + 1) = 2 * m := by omega
  have hev := moment_even hB b a L ha hL hb σ X hX (m - 1) x t
  rw [h2m, ← hC] at hev
  set Y := Real.exp (C * t) * (‖x‖ ^ (2 * m) + 1) with hY
  set Z := Real.exp (C * t) * (‖x‖ ^ m + 1) with hZ
  have hY0 : 0 ≤ Y := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  obtain ⟨g, hgm, hgf, hgeq⟩ := exists_measurable_le_lintegral_eq P (fun ω => ‖X x t ω‖ₑ ^ m)
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    hgm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at hhold
  have hg2 : ∫⁻ ω, g ω ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal Y := by
    calc ∫⁻ ω, g ω ^ (2 : ℝ) ∂P ≤ ∫⁻ ω, ‖X x t ω‖ₑ ^ (2 * m) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [pow_mul', ← ENNReal.rpow_two (‖X x t ω‖ₑ ^ m)]
          exact ENNReal.rpow_le_rpow (hgf ω) (by norm_num)
      _ ≤ _ := hev
  have hsq : Real.sqrt Y ≤ Z := by
    rw [Real.sqrt_le_left hZ0]
    have h1 : Real.exp (C * t) ≤ Real.exp (C * t) ^ 2 := by
      have := Real.one_le_exp (by positivity : 0 ≤ C * t)
      nlinarith
    have h2 : ‖x‖ ^ (2 * m) + 1 ≤ (‖x‖ ^ m + 1) ^ 2 := by
      have : 0 ≤ ‖x‖ ^ m := by positivity
      rw [pow_mul']; nlinarith
    calc Y ≤ Real.exp (C * t) ^ 2 * (‖x‖ ^ m + 1) ^ 2 := by
          rw [hY]; gcongr
      _ = Z ^ 2 := by rw [hZ]; ring
  calc ∫⁻ ω, ‖X x t ω‖ₑ ^ m ∂P = ∫⁻ ω, g ω ∂P := hgeq
    _ ≤ (∫⁻ ω, g ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by simpa using hhold
    _ ≤ (ENNReal.ofReal Y) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hg2 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt Y) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hY0 (by norm_num), Real.sqrt_eq_rpow]
    _ ≤ ENNReal.ofReal Z := ENNReal.ofReal_le_ofReal hsq

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

variable {d : ℕ}

lemma abs_eDot_le (x : E d) : |eDot x| ≤ d * ‖x‖ := by
  unfold eDot
  calc |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ := by
        gcongr with i
        exact (Real.norm_eq_abs (x i)).symm ▸ PiLp.norm_apply_le x i
    _ = d * ‖x‖ := by simp

lemma eDot_sub (x y : E d) : eDot (x - y) = eDot x - eDot y := by
  simp [eDot, Finset.sum_sub_distrib]

lemma rho_cont (ε : ℝ) (hε : 0 < ε) : Continuous (rho ε) := by
  set q : ℝ → ℝ := fun y => 3 * ε / 16 - y ^ 4 / (16 * ε ^ 3) + 3 * y ^ 2 / (8 * ε) + y / 2
    with hq
  have hinner : Continuous (fun y : ℝ => if y ≤ ε then q y else y) := by
    refine Continuous.if_le (by fun_prop) continuous_id continuous_id continuous_const ?_
    intro y hy
    subst hy
    simp only [hq]
    field_simp
    ring
  have hall : Continuous (fun y : ℝ => if -ε ≤ y then (if y ≤ ε then q y else y) else 0) := by
    refine Continuous.if_le hinner continuous_const continuous_const continuous_id ?_
    intro y hy
    subst hy
    have : -ε ≤ ε := by linarith
    simp only [this, if_true, hq]
    field_simp
    ring
  have : rho ε = fun y => if -ε ≤ y then (if y ≤ ε then q y else y) else 0 := by
    funext y
    unfold rho
    by_cases h1 : y < -ε
    · have : ¬ (-ε ≤ y) := by linarith
      simp [h1, this]
    · have h1' : -ε ≤ y := by linarith
      by_cases h2 : ε < y
      · have : ¬ (y ≤ ε) := by linarith
        simp [h1, h2, h1', this]
      · have h2' : y ≤ ε := by linarith
        simp [h1, h2, h1', h2', hq]
  rw [this]
  exact hall

lemma rho_abs_le (ε y : ℝ) (hε : ε ∈ Set.Ioo (0:ℝ) 1) : |rho ε y| ≤ |y| + 2 := by
  obtain ⟨h0, h1⟩ := hε
  unfold rho
  split_ifs with ha hb
  · simp; positivity
  · linarith [le_abs_self y]
  · push Not at ha hb
    have hy : |y| ≤ ε := abs_le.2 ⟨ha, hb⟩
    have hy4 : y ^ 4 ≤ ε ^ 4 := by
      have := pow_le_pow_left₀ (abs_nonneg y) hy 4
      rwa [pow_abs, abs_of_nonneg (by positivity)] at this
    have hy2 : y ^ 2 ≤ ε ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg y) hy 2
      rwa [pow_abs, abs_of_nonneg (by positivity)] at this
    have e1 : y ^ 4 / (16 * ε ^ 3) ≤ ε / 16 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e2 : 3 * y ^ 2 / (8 * ε) ≤ 3 * ε / 8 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e3 : 0 ≤ y ^ 4 / (16 * ε ^ 3) := by positivity
    have e4 : 0 ≤ 3 * y ^ 2 / (8 * ε) := by positivity
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg y, abs_le.1 hy]

lemma rho_sub_le (ε y : ℝ) (hε : ε ∈ Set.Ioo (0:ℝ) 1) : |rho ε y - max y 0| ≤ 3 * ε := by
  obtain ⟨h0, h1⟩ := hε
  unfold rho
  split_ifs with ha hb
  · rw [max_eq_right (by linarith)]; simp; positivity
  · rw [max_eq_left (by linarith)]; simp; positivity
  · push Not at ha hb
    have hy : |y| ≤ ε := abs_le.2 ⟨ha, hb⟩
    have hy4 : y ^ 4 ≤ ε ^ 4 := by
      have := pow_le_pow_left₀ (abs_nonneg y) hy 4
      rwa [pow_abs, abs_of_nonneg (by positivity)] at this
    have hy2 : y ^ 2 ≤ ε ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg y) hy 2
      rwa [pow_abs, abs_of_nonneg (by positivity)] at this
    have e1 : y ^ 4 / (16 * ε ^ 3) ≤ ε / 16 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e2 : 3 * y ^ 2 / (8 * ε) ≤ 3 * ε / 8 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e3 : 0 ≤ y ^ 4 / (16 * ε ^ 3) := by positivity
    have e4 : 0 ≤ 3 * y ^ 2 / (8 * ε) := by positivity
    have hm1 : max y 0 ≤ ε := max_le hb h0.le
    have hm2 : 0 ≤ max y 0 := le_max_right _ _
    rw [abs_le]
    constructor <;> nlinarith [abs_le.1 hy]

/-- The vector `(R − αI)p`. -/
noncomputable def v0 (M : Model d) : E d := mat (M.R - M.α • 1) M.pE

noncomputable def A0 (M : Model d) : ℝ := |M.β| * ‖M.pE‖ + 2 * ‖v0 M‖

noncomputable def L1 (M : Model d) : ℝ := ‖mat M.R‖ + d * ‖v0 M‖

lemma A0_nonneg (M : Model d) : 0 ≤ A0 M := by unfold A0; positivity

lemma L1_nonneg (M : Model d) : 0 ≤ L1 M := by unfold L1; positivity

lemma g_eq (M : Model d) (y : E d) :
    M.g y = -(M.β • M.pE) - mat M.R y + max (eDot y) 0 • v0 M := rfl

lemma gEps_eq (M : Model d) (ε : ℝ) (y : E d) :
    M.gEps ε y = -(M.β • M.pE) - mat M.R y + rho ε (eDot y) • v0 M := rfl

lemma growth_aux (M : Model d) (y : E d) (c : ℝ) (hc : |c| ≤ |eDot y| + 2) :
    ‖-(M.β • M.pE) - mat M.R y + c • v0 M‖ ≤ A0 M + L1 M * ‖y‖ := by
  have h1 : ‖-(M.β • M.pE)‖ = |M.β| * ‖M.pE‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs]
  have h2 : ‖mat M.R y‖ ≤ ‖mat M.R‖ * ‖y‖ := (mat M.R).le_opNorm y
  have h3 : ‖c • v0 M‖ = |c| * ‖v0 M‖ := by rw [norm_smul, Real.norm_eq_abs]
  have he := abs_eDot_le y
  have hv : 0 ≤ ‖v0 M‖ := norm_nonneg _
  have h4 : |c| * ‖v0 M‖ ≤ (d * ‖y‖ + 2) * ‖v0 M‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hv
  calc ‖-(M.β • M.pE) - mat M.R y + c • v0 M‖
      ≤ ‖-(M.β • M.pE)‖ + ‖mat M.R y‖ + ‖c • v0 M‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ A0 M + L1 M * ‖y‖ := by
        rw [h1, h3]; unfold A0 L1; nlinarith

lemma g_growth (M : Model d) (y : E d) : ‖M.g y‖ ≤ A0 M + L1 M * ‖y‖ := by
  rw [g_eq]
  apply growth_aux
  rcases le_total (eDot y) 0 with h | h
  · rw [max_eq_right h]; simp; positivity
  · rw [max_eq_left h]; linarith [le_abs_self (eDot y)]

lemma gEps_growth (M : Model d) (ε : ℝ) (hε : ε ∈ Set.Ioo (0:ℝ) 1) (y : E d) :
    ‖M.gEps ε y‖ ≤ A0 M + L1 M * ‖y‖ := by
  rw [gEps_eq]
  exact growth_aux M y _ (rho_abs_le ε _ hε)

lemma g_lip (M : Model d) (y z : E d) : ‖M.g y - M.g z‖ ≤ L1 M * ‖y - z‖ := by
  have : M.g y - M.g z = -(mat M.R (y - z)) + (max (eDot y) 0 - max (eDot z) 0) • v0 M := by
    rw [g_eq, g_eq, map_sub, sub_smul]; abel
  rw [this]
  have h2 : ‖mat M.R (y - z)‖ ≤ ‖mat M.R‖ * ‖y - z‖ := (mat M.R).le_opNorm _
  have h3 : |max (eDot y) 0 - max (eDot z) 0| ≤ d * ‖y - z‖ := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← eDot_sub]; exact abs_eDot_le _
  have hv : 0 ≤ ‖v0 M‖ := norm_nonneg _
  calc _ ≤ ‖-(mat M.R (y - z))‖ + ‖(max (eDot y) 0 - max (eDot z) 0) • v0 M‖ := norm_add_le _ _
    _ = ‖mat M.R (y - z)‖ + |max (eDot y) 0 - max (eDot z) 0| * ‖v0 M‖ := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs]
    _ ≤ ‖mat M.R‖ * ‖y - z‖ + (d * ‖y - z‖) * ‖v0 M‖ := by gcongr
    _ = L1 M * ‖y - z‖ := by unfold L1; ring

lemma gEps_sub_g (M : Model d) (ε : ℝ) (hε : ε ∈ Set.Ioo (0:ℝ) 1) (y : E d) :
    ‖M.gEps ε y - M.g y‖ ≤ 3 * ε * ‖v0 M‖ := by
  have : M.gEps ε y - M.g y = (rho ε (eDot y) - max (eDot y) 0) • v0 M := by
    rw [gEps_eq, g_eq, sub_smul]; abel
  rw [this, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (rho_sub_le ε _ hε) (norm_nonneg _)

lemma g_cont (M : Model d) : Continuous M.g := by
  have he : Continuous (fun y : E d => eDot y) := by
    unfold eDot; fun_prop
  have : M.g = fun y => -(M.β • M.pE) - mat M.R y + max (eDot y) 0 • v0 M := rfl
  rw [this]
  exact ((continuous_const.sub (mat M.R).continuous).add
    ((he.max continuous_const).smul continuous_const))

lemma gEps_cont (M : Model d) (ε : ℝ) (hε : 0 < ε) : Continuous (M.gEps ε) := by
  have he : Continuous (fun y : E d => eDot y) := by
    unfold eDot; fun_prop
  have : M.gEps ε = fun y => -(M.β • M.pE) - mat M.R y + rho ε (eDot y) • v0 M := rfl
  rw [this]
  exact ((continuous_const.sub (mat M.R).continuous).add
    (((rho_cont ε hε).comp he).smul continuous_const))

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

namespace Occ34

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma diff_bound (M : Model d) (B : ℝ≥0 → Ω → E d) (X Y : E d → ℝ≥0 → Ω → E d)
    (hX : IsSolution M.g M.σ B X) (ε : ℝ) (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hY : IsSolution (M.gEps ε) M.σ B Y) (x : E d) (ω : Ω) (t : ℝ≥0) :
    ‖Y x t ω - X x t ω‖ ≤ ((t:ℝ) * (3 * ε * ‖v0 M‖)) * Real.exp (L1 M * t) := by
  obtain ⟨hXc, hXe⟩ := hX x ω
  obtain ⟨hYc, hYe⟩ := hY x ω
  set c : ℝ := 3 * ε * ‖v0 M‖ with hc
  have hc0 : 0 ≤ c := by have := hε.1; positivity
  set u : ℝ → ℝ := fun s => ‖Y x s.toNNReal ω - X x s.toNNReal ω‖ with hu
  have hXc' : Continuous (fun s : ℝ => X x s.toNNReal ω) := hXc.comp continuous_real_toNNReal
  have hYc' : Continuous (fun s : ℝ => Y x s.toNNReal ω) := hYc.comp continuous_real_toNNReal
  have huc : Continuous u := continuous_norm.comp (hYc'.sub hXc')
  have hgX : Continuous (fun s : ℝ => M.g (X x s.toNNReal ω)) := (g_cont M).comp hXc'
  have hgY : Continuous (fun s : ℝ => M.gEps ε (Y x s.toNNReal ω)) :=
    (gEps_cont M ε hε.1).comp hYc'
  have hαm : MonotoneOn (fun s : ℝ => s * c) (Set.Ici 0) := by
    intro s1 _ s2 _ h12
    exact mul_le_mul_of_nonneg_right h12 hc0
  have hL := L1_nonneg M
  have hmain : ∀ s, 0 ≤ s → u s ≤ s * c + L1 M * ∫ r in (0:ℝ)..s, u r := by
    intro s hs
    have h1 := hXe s.toNNReal
    have h2 := hYe s.toNNReal
    rw [Real.coe_toNNReal _ hs] at h1 h2
    have heq : Y x s.toNNReal ω - X x s.toNNReal ω =
        ∫ r in (0:ℝ)..s, (M.gEps ε (Y x r.toNNReal ω) - M.g (X x r.toNNReal ω)) := by
      rw [intervalIntegral.integral_sub (hgY.intervalIntegrable _ _) (hgX.intervalIntegrable _ _),
        h1, h2]
      abel
    have hcont : Continuous (fun r => c + L1 M * u r) := by fun_prop
    have hle := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun r => M.gEps ε (Y x r.toNNReal ω) - M.g (X x r.toNNReal ω))
      (g := fun r => c + L1 M * u r) (μ := volume) hs
      (Eventually.of_forall fun r _ => by
        have e1 := gEps_sub_g M ε hε (Y x r.toNNReal ω)
        have e2 := g_lip M (Y x r.toNNReal ω) (X x r.toNNReal ω)
        calc ‖M.gEps ε (Y x r.toNNReal ω) - M.g (X x r.toNNReal ω)‖
            = ‖(M.gEps ε (Y x r.toNNReal ω) - M.g (Y x r.toNNReal ω))
                + (M.g (Y x r.toNNReal ω) - M.g (X x r.toNNReal ω))‖ := by abel_nf
          _ ≤ _ := norm_add_le _ _
          _ ≤ c + L1 M * u r := add_le_add e1 e2)
      (hcont.intervalIntegrable _ _)
    have hcalc : (∫ r in (0:ℝ)..s, (c + L1 M * u r)) = s * c + L1 M * ∫ r in (0:ℝ)..s, u r := by
      rw [intervalIntegral.integral_add (f := fun _ => c) (g := fun r => L1 M * u r)
        intervalIntegrable_const
        ((continuous_const.mul huc).intervalIntegrable _ _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp
    calc u s = ‖∫ r in (0:ℝ)..s, (M.gEps ε (Y x r.toNNReal ω) - M.g (X x r.toNNReal ω))‖ := by
          simp only [hu]; rw [heq]
      _ ≤ _ := hle
      _ = _ := hcalc
  have := gronwall_int hL huc hαm hmain t t.2
  simpa [hu] using this

end Occ34

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open GPhNGIDiffusion.OccupationCLT

theorem solution {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (Xε : ℝ → E d → ℝ≥0 → Ω → E d)
    (hXε : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, IsSolution (M.gEps ε) M.σ B (Xε ε)) :
    (∀ m : ℕ, 2 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (x : E d) (t : ℝ≥0),
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        ∫⁻ ω, ‖Xε ε x t ω‖ₑ ^ m ∂P ≤ ENNReal.ofReal (Real.exp (C * t) * (‖x‖ ^ m + 1))) ∧
      ∫⁻ ω, ‖X x t ω‖ₑ ^ m ∂P ≤ ENNReal.ofReal (Real.exp (C * t) * (‖x‖ ^ m + 1))) ∧
    (∀ m : ℕ, 2 ≤ m → ∀ (x : E d) (t : ℝ≥0),
      Tendsto (fun ε : ℝ => ∫⁻ ω, ‖Xε ε x t ω - X x t ω‖ₑ ^ m ∂P) (𝓝[>] 0) (𝓝 0)) := by
  obtain ⟨hP, hB, hsol⟩ := hX
  have hA := Occ34.A0_nonneg M
  have hL := Occ34.L1_nonneg M
  refine ⟨fun m hm => ?_, fun m hm x t => ?_⟩
  · refine ⟨Occ34.Cst (Occ34.A0 M + Occ34.L1 M) (Occ34.L1 M) ‖mat M.σ‖ d (m - 1),
      Occ34.Cst_pos _ _ _ (by positivity) hL (norm_nonneg _) d _, fun x t => ⟨?_, ?_⟩⟩
    · intro ε hε
      exact Occ34.moment_m hB (M.gEps ε) (Occ34.A0 M) (Occ34.L1 M) hA hL
        (Occ34.gEps_growth M ε hε) M.σ (Xε ε) (hXε ε hε) m hm x t
    · exact Occ34.moment_m hB M.g (Occ34.A0 M) (Occ34.L1 M) hA hL
        (Occ34.g_growth M) M.σ X hsol m hm x t
  · set K : ℝ := (t:ℝ) * (3 * ‖Occ34.v0 M‖) * Real.exp (Occ34.L1 M * t) with hK
    have hK0 : 0 ≤ K := by positivity
    have hbound : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∫⁻ ω, ‖Xε ε x t ω - X x t ω‖ₑ ^ m ∂P
        ≤ ENNReal.ofReal (K * ε) ^ m := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      have hpt : ∀ ω, ‖Xε ε x t ω - X x t ω‖ₑ ^ m ≤ ENNReal.ofReal (K * ε) ^ m := by
        intro ω
        have h := Occ34.diff_bound M B X (Xε ε) hsol ε hε (hXε ε hε) x ω t
        have h' : ‖Xε ε x t ω - X x t ω‖ ≤ K * ε := by
          calc _ ≤ _ := h
            _ = K * ε := by rw [hK]; ring
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal h'
      calc ∫⁻ ω, ‖Xε ε x t ω - X x t ω‖ₑ ^ m ∂P ≤ ∫⁻ _ω, ENNReal.ofReal (K * ε) ^ m ∂P :=
            lintegral_mono hpt
        _ = _ := by simp
    have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε) ^ m) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun ε : ℝ => ENNReal.ofReal (K * ε) ^ m) :=
        (ENNReal.continuous_pow m).comp (ENNReal.continuous_ofReal.comp (continuous_const.mul
          continuous_id))
      have := hc.tendsto 0
      simp only [mul_zero, ENNReal.ofReal_zero, zero_pow (show m ≠ 0 by omega)] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) hbound

