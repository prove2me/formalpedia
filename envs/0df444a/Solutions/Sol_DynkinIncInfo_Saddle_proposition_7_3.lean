-- Prove2me | solution 1 for DynkinIncInfo.Saddle.proposition_7_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:09:32.629971+00:00
-- url     : https://prove2.me/submissions/82a1cc2d-f7be-4f0c-8fda-cbe88a606f4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions
import Theorems.Thm_DynkinIncInfo_Saddle_lemma_3_1
import Theorems.Thm_DynkinIncInfo_Saddle_theorem_3_2_seller
import Theorems.Thm_DynkinIncInfo_Saddle_theorem_3_2_sub
import Theorems.Thm_DynkinIncInfo_Saddle_corollary_4_5
import Theorems.Thm_DynkinIncInfo_Saddle_lemma_4_6
import Theorems.Thm_DynkinIncInfo_Saddle_eq_5_3
import Theorems.Thm_DynkinIncInfo_Saddle_corollary_5_5_c1
import Theorems.Thm_DynkinIncInfo_Saddle_lemma_7_2

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace DynkinOSAux

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

lemma coe_untopA_min (t : ℝ≥0) (a : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) a).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) a := by
  have h : min (t : WithTop ℝ≥0) a ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop h, WithTop.coe_untop]

lemma untopA_min_le (t : ℝ≥0) (a : WithTop ℝ≥0) : (min (t : WithTop ℝ≥0) a).untopA ≤ t := by
  have := coe_untopA_min t a
  have h2 : ((min (t : WithTop ℝ≥0) a).untopA : WithTop ℝ≥0) ≤ t := by
    rw [this]; exact min_le_left _ _
  exact_mod_cast h2

/-- Optional sampling (continuous time) for a bounded submartingale with right-continuous paths,
at the bounded stopping time `t ∧ γ`. -/
theorem submartingale_integral_zero_le_stopped [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} {X : ℝ≥0 → Ω → ℝ} (hX : Submartingale X ℱ μ)
    (hrc : ∀ ω s, ContinuousWithinAt (fun u => X u ω) (Set.Ici s) s)
    (C : ℝ) (hC : ∀ᵐ ω ∂μ, ∀ s, |X s ω| ≤ C)
    {γ : Ω → WithTop ℝ≥0} (hγ : IsStoppingTime ℱ γ) (t : ℝ≥0) :
    ∫ ω, X 0 ω ∂μ ≤ ∫ ω, stoppedProcess X γ t ω ∂μ := by
  rcases eq_or_ne t 0 with rfl | ht
  · apply le_of_eq
    congr 1
    funext ω
    simp [stoppedProcess]
  have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
  -- the stopped time σ = t ∧ γ, as an `ℝ≥0`-valued function
  set σ : Ω → ℝ≥0 := fun ω => (min (t : WithTop ℝ≥0) (γ ω)).untopA with hσdef
  have hσle : ∀ ω, σ ω ≤ t := fun ω => untopA_min_le t (γ ω)
  have hσST : ∀ s : ℝ≥0, MeasurableSet[ℱ s] {ω | σ ω ≤ s} := by
    intro s
    have h1 : IsStoppingTime ℱ (fun ω => min (t : WithTop ℝ≥0) (γ ω)) :=
      (isStoppingTime_const ℱ t).min hγ
    have : {ω | σ ω ≤ s} = {ω | min (t : WithTop ℝ≥0) (γ ω) ≤ s} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [← coe_untopA_min t (γ ω)]
      exact WithTop.coe_le_coe.symm
    rw [this]; exact h1 s
  -- grid points
  let g : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * t / 2 ^ n
  have hg_mono : ∀ n, Monotone (g n) := by
    intro n a b hab
    simp only [g]
    gcongr
  let 𝒢 : ℕ → Filtration ℕ m0 := fun n =>
    { seq := fun k => ℱ (g n k)
      mono' := fun a b hab => ℱ.mono (hg_mono n hab)
      le' := fun k => ℱ.le _ }
  let f : ℕ → ℕ → Ω → ℝ := fun n k => X (g n k)
  have hf : ∀ n, Submartingale (f n) (𝒢 n) μ := by
    intro n
    refine ⟨fun k => hX.1 (g n k), fun i j hij => hX.2.1 _ _ (hg_mono n hij), fun i => hX.2.2 _⟩
  let ρ : ℕ → Ω → ℕ := fun n ω => ⌈(2 : ℝ≥0) ^ n * σ ω / t⌉₊
  have hρ_iff : ∀ n ω (k : ℕ), ρ n ω ≤ k ↔ σ ω ≤ g n k := by
    intro n ω k
    simp only [ρ, g]
    rw [Nat.ceil_le]
    have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos (by norm_num) n
    rw [div_le_iff₀ htpos, le_div_iff₀ h2]
    constructor <;> intro h <;> [skip; skip] <;> nlinarith [h]
  have hρST : ∀ n, IsStoppingTime (𝒢 n) (fun ω => ((ρ n ω : ℕ) : ℕ∞)) := by
    intro n k
    have : {ω | ((ρ n ω : ℕ) : ℕ∞) ≤ (k : ℕ∞)} = {ω | σ ω ≤ g n k} := by
      ext ω
      simp only [Set.mem_setOf_eq, Nat.cast_le]
      exact hρ_iff n ω k
    show MeasurableSet[ℱ (g n k)] {ω | ((ρ n ω : ℕ) : ℕ∞) ≤ (k : ℕ∞)}
    rw [this]; exact hσST _
  have hρbdd : ∀ n ω, ((ρ n ω : ℕ) : ℕ∞) ≤ ((2 ^ n : ℕ) : ℕ∞) := by
    intro n ω
    rw [Nat.cast_le, hρ_iff]
    simp only [g]
    push_cast
    have h2 : (2 : ℝ≥0) ^ n * t / 2 ^ n = t := by
      field_simp
    rw [h2]; exact hσle ω
  -- integrals
  have hineq : ∀ n, ∫ ω, X 0 ω ∂μ ≤ ∫ ω, X (g n (ρ n ω)) ω ∂μ := by
    intro n
    have := (hf n).expected_stoppedValue_mono (isStoppingTime_const (𝒢 n) 0) (hρST n)
      (fun ω => bot_le) (hρbdd n)
    simpa [stoppedValue, f, g] using this
  -- convergence of the grid times
  have hgρ_ge : ∀ n ω, σ ω ≤ g n (ρ n ω) := fun n ω => (hρ_iff n ω _).1 le_rfl
  have hgρ_le : ∀ n ω, g n (ρ n ω) ≤ σ ω + t / 2 ^ n := by
    intro n ω
    simp only [g, ρ]
    have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos (by norm_num) n
    have hc := Nat.ceil_lt_add_one (zero_le : (0 : ℝ≥0) ≤ (2 : ℝ≥0) ^ n * σ ω / t)
    have : ((⌈(2 : ℝ≥0) ^ n * σ ω / t⌉₊ : ℕ) : ℝ≥0) ≤ 2 ^ n * σ ω / t + 1 := hc.le
    calc ((⌈(2 : ℝ≥0) ^ n * σ ω / t⌉₊ : ℕ) : ℝ≥0) * t / 2 ^ n
        ≤ (2 ^ n * σ ω / t + 1) * t / 2 ^ n := by gcongr
      _ = σ ω + t / 2 ^ n := by
        field_simp
  have htend_time : ∀ ω, Tendsto (fun n => g n (ρ n ω)) atTop (𝓝[Set.Ici (σ ω)] σ ω) := by
    intro ω
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hlim : Tendsto (fun n : ℕ => σ ω + t / 2 ^ n) atTop (𝓝 (σ ω)) := by
        have : Tendsto (fun n : ℕ => t / (2 : ℝ≥0) ^ n) atTop (𝓝 0) := by
          simp_rw [div_eq_mul_inv, ← inv_pow]
          have := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹)
            (by rw [inv_lt_one₀ (by norm_num)]; norm_num)
          simpa using this.const_mul t
        simpa using (tendsto_const_nhds (x := σ ω)).add this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun n => hgρ_ge n ω) (fun n => hgρ_le n ω)
    · exact Eventually.of_forall (fun n => hgρ_ge n ω)
  have hlimX : ∀ ω, Tendsto (fun n => X (g n (ρ n ω)) ω) atTop (𝓝 (X (σ ω) ω)) :=
    fun ω => (hrc ω (σ ω)).tendsto.comp (htend_time ω)
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => X (g n (ρ n ω)) ω) μ := by
    intro n
    have := integrable_stoppedValue ℕ (hρST n) (fun k => (hf n).integrable k) (hρbdd n)
    exact this.aestronglyMeasurable
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => C) hmeas
    (integrable_const C)
    (fun n => by filter_upwards [hC] with ω hω; simpa [Real.norm_eq_abs] using hω _)
    (Eventually.of_forall hlimX)
  have : ∫ ω, X (σ ω) ω ∂μ = ∫ ω, stoppedProcess X γ t ω ∂μ := rfl
  rw [← this]
  exact ge_of_tendsto hDCT (Eventually.of_forall hineq)

end DynkinOSAux


open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open DynkinIncInfo.Saddle

namespace DynkinRedAux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma S_pos (p : Params) (st : Setting Ω) {x : ℝ} (hx : 0 < x) (y : ℝ) (t : ℝ≥0) (ω : Ω) :
    0 < S p st x y t ω := by
  unfold S; positivity

lemma Y_mem (p : Params) (st : Setting Ω) (x : ℝ) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ≥0) (ω : Ω) : Y p st x y t ω ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hy0, hy1⟩ := hy
  have hl : 0 < ell p st x y t ω := Real.exp_pos _
  have h1y : 0 < 1 - y := by linarith
  have hden : 0 < y * ell p st x y t ω + (1 - y) := by positivity
  unfold Y
  constructor
  · positivity
  · rw [div_lt_one hden]; linarith

lemma continuous_S (p : Params) (st : Setting Ω) (x y : ℝ) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => S p st x y t ω) := by
  unfold S
  have hB := st.continuous_B ω
  have hc : Continuous (fun t : ℝ≥0 => (t : ℝ)) := NNReal.continuous_coe
  fun_prop

lemma continuous_Y (p : Params) (st : Setting Ω) {x : ℝ} (hx : 0 < x) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => Y p st x y t ω) := by
  have hS := continuous_S p st x y ω
  have hc : Continuous (fun t : ℝ≥0 => (t : ℝ)) := NNReal.continuous_coe
  have hell : Continuous (fun t : ℝ≥0 => ell p st x y t ω) := by
    unfold ell
    have hlog : Continuous (fun t : ℝ≥0 => Real.log (S p st x y t ω / x)) := by
      apply Continuous.log (hS.div_const x)
      intro t
      exact (div_pos (S_pos p st hx y t ω) hx).ne'
    fun_prop
  unfold Y
  apply Continuous.div (continuous_const.mul hell)
    ((continuous_const.mul hell).add continuous_const)
  intro t
  have hl : 0 < ell p st x y t ω := Real.exp_pos _
  have := mul_pos hy.1 hl
  have : 0 < y * ell p st x y t ω + (1 - y) := by linarith [hy.2]
  exact this.ne'

/-- Continuity of `t ↦ V(a t, b t)` along continuous paths in `(0, ∞) × [0, 1]`,
from Lemma 3.1 (ii)–(iii). -/
lemma continuous_V_comp (p : Params) (st : Setting Ω) {a b : ℝ≥0 → ℝ}
    (ha : Continuous a) (hb : Continuous b) (ha0 : ∀ t, 0 < a t)
    (hb01 : ∀ t, b t ∈ Set.Icc (0 : ℝ) 1) :
    Continuous (fun t => V p st (a t) (b t)) := by
  obtain ⟨_, _, hlipx, C, hC, hlipy⟩ :=
    lemma_3_1 p st (fun x y => V p st x y) (Or.inr rfl)
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ s, dist (V p st (a s) (b s)) (V p st (a t0) (b t0)) ≤
      |a s - a t0| + C * (1 + |a t0|) * |b s - b t0| := by
    intro s
    rw [Real.dist_eq]
    have h1 := hlipx (a s) (a t0) (b s) (ha0 s).le (ha0 t0).le (hb01 s)
    have h2 := hlipy (a t0) (b s) (b t0) (ha0 t0) (hb01 s) (hb01 t0)
    calc |V p st (a s) (b s) - V p st (a t0) (b t0)|
        = |(V p st (a s) (b s) - V p st (a t0) (b s)) +
            (V p st (a t0) (b s) - V p st (a t0) (b t0))| := by ring_nf
      _ ≤ |V p st (a s) (b s) - V p st (a t0) (b s)| +
            |V p st (a t0) (b s) - V p st (a t0) (b t0)| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  apply squeeze_zero (fun s => dist_nonneg) hbound
  have hlim : Tendsto (fun s => |a s - a t0| + C * (1 + |a t0|) * |b s - b t0|) (𝓝 t0)
      (𝓝 (|a t0 - a t0| + C * (1 + |a t0|) * |b t0 - b t0|)) := by
    apply Tendsto.add
    · exact ((ha.tendsto t0).sub tendsto_const_nhds).abs
    · exact tendsto_const_nhds.mul (((hb.tendsto t0).sub tendsto_const_nhds).abs)
  simpa using hlim

lemma G1_le_G2 (p : Params) (x : ℝ) : G1 p x ≤ G2 p x := by
  unfold G1 G2; linarith [p.ε0_pos]

lemma G2_mono (p : Params) {x x' : ℝ} (h : x ≤ x') : G2 p x ≤ G2 p x' := by
  unfold G2
  have : max (x - p.K) 0 ≤ max (x' - p.K) 0 := max_le_max (by linarith) le_rfl
  linarith

lemma G2_nonneg (p : Params) (x : ℝ) : 0 ≤ G2 p x := by
  unfold G2; have := p.ε0_pos; positivity

lemma continuous_G1 (p : Params) : Continuous (G1 p) := by
  unfold G1; fun_prop

lemma S_zero_of_B (p : Params) (st : Setting Ω) (x y : ℝ) (ω : Ω) (h : st.B 0 ω = 0) :
    S p st x y 0 ω = x := by
  simp [S, h]

lemma Y_zero_of_B (p : Params) (st : Setting Ω) {x : ℝ} (hx : 0 < x) {y : ℝ}
    (ω : Ω) (h : st.B 0 ω = 0) : Y p st x y 0 ω = y := by
  have hS := S_zero_of_B p st x y ω h
  simp only [Y, ell, hS, div_self hx.ne', Real.log_one, mul_zero, NNReal.coe_zero, add_zero,
    Real.exp_zero, mul_one]
  simp

/-- `V̄(x', y') ≤ G2(x')` (take `γ ≡ 0`). -/
lemma Vup_le_G2 (p : Params) (st : Setting Ω) (x' y' : ℝ) :
    Vup p st x' y' ≤ ENNReal.ofReal (G2 p x') := by
  haveI := st.isProb
  unfold Vup dynkinUpper
  refine (iInf₂_le (fun _ : Ω => (0 : WithTop ℝ≥0)) (isStoppingTime_const _ _)).trans ?_
  refine iSup₂_le fun τ _ => ?_
  have hB := st.brownian.eval_zero_ae_eq_zero
  calc dynkinM st.P (L1 p st x' y') (U2 p st x' y') τ (fun _ => 0)
      ≤ ∫⁻ _, ENNReal.ofReal (G2 p x') ∂st.P := by
        apply lintegral_mono_ae
        filter_upwards [hB] with ω hω
        have hS := S_zero_of_B p st x' y' ω hω
        unfold dynkinPayoff
        split_ifs with h1 h2
        · have : τ ω = 0 := le_antisymm h1.1 bot_le
          rw [this]
          show ENNReal.ofReal (Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * G1 p (S p st x' y' 0 ω)) ≤ _
          rw [hS]
          apply ENNReal.ofReal_le_ofReal
          simpa using G1_le_G2 p x'
        · show ENNReal.ofReal (Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * G2 p (S p st x' y' 0 ω)) ≤ _
          rw [hS]; simp
        · exact zero_le
    _ = ENNReal.ofReal (G2 p x') := by simp

lemma Vup_ne_top (p : Params) (st : Setting Ω) (x' y' : ℝ) : Vup p st x' y' ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Vup_le_G2 p st x' y')

lemma V_le_G2 (p : Params) (st : Setting Ω) (x' y' : ℝ) : V p st x' y' ≤ G2 p x' := by
  unfold V
  exact ENNReal.toReal_le_of_le_ofReal (G2_nonneg p x') (Vup_le_G2 p st x' y')

lemma V_nonneg (p : Params) (st : Setting Ω) (x' y' : ℝ) : 0 ≤ V p st x' y' :=
  ENNReal.toReal_nonneg

lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) : ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases hf : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_toReal_le
    linarith [ENNReal.toReal_nonneg (a := ∫⁻ a, ENNReal.ofReal (-f a) ∂μ)]
  · rw [integral_undef hf]; simp

end DynkinRedAux


open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open DynkinIncInfo.Saddle

namespace DynkinRedAux

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The starting point `z = ln x + (σ²/δ0) ln(y/(1 − y))` of `Z`. -/
noncomputable def z0 (p : Params) (x y : ℝ) : ℝ :=
  Real.log x + p.σ ^ 2 / p.δ0 * Real.log (y / (1 - y))

lemma yK_lt_one (p : Params) (z : ℝ) : yK p z < 1 := by
  unfold yK
  have h1 : 0 < p.K ^ (p.δ0 / p.σ ^ 2) := Real.rpow_pos_of_pos p.K_pos _
  have h2 : 0 < Real.exp (p.δ0 / p.σ ^ 2 * z) := Real.exp_pos _
  rw [div_lt_one (by linarith)]
  linarith

lemma continuous_state_gap (p : Params) (st : Setting Ω) {x : ℝ} (hx : 0 < x) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω) :
    Continuous (fun t => V p st (S p st x y t ω) (Y p st x y t ω)) :=
  continuous_V_comp p st (continuous_S p st x y ω) (continuous_Y p st hx hy ω)
    (fun t => S_pos p st hx y t ω) (fun t => Set.Ioo_subset_Icc_self (Y_mem p st x hy t ω))

lemma continuous_discV (p : Params) (st : Setting Ω) {x : ℝ} (hx : 0 < x) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω) :
    Continuous (fun t => discV p st x y t ω) := by
  unfold discV
  have h := continuous_state_gap p st hx hy ω
  have hc : Continuous (fun t : ℝ≥0 => (t : ℝ)) := NNReal.continuous_coe
  fun_prop

/-- At a finite value `T` of `τ*`, the state lies in `{V ≤ G1}` (closedness of the hitting set
along the continuous path). -/
lemma V_le_G1_at_tau (p : Params) (st : Setting Ω) {x : ℝ} (hx : 0 < x) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω) (T : ℝ≥0) (hT : τstar p st x y ω = T) :
    V p st (S p st x y T ω) (Y p st x y T ω) ≤ G1 p (S p st x y T ω) := by
  set A : Set ℝ≥0 := {i | V p st (S p st x y i ω) (Y p st x y i ω) ≤ G1 p (S p st x y i ω)}
  have hA : IsClosed A :=
    isClosed_le (continuous_state_gap p st hx hy ω)
      ((continuous_G1 p).comp (continuous_S p st x y ω))
  have hdef := hT
  unfold τstar hittingAfter at hdef
  split_ifs at hdef with h
  · have hset : {i : ℝ≥0 | 0 ≤ i ∧ state p st x y i ω ∈
        {q : ℝ × ℝ | V p st q.1 q.2 ≤ G1 p q.1}} = A := by
      ext i; simp [A, state]
    rw [hset] at hdef
    have hne : A.Nonempty := by
      obtain ⟨j, _, hj⟩ := h
      exact ⟨j, hj⟩
    have hmem := hA.csInf_mem hne (OrderBot.bddBelow A)
    have : sInf A = T := WithTop.coe_injective hdef
    rw [this] at hmem
    exact hmem
  · exact absurd hdef WithTop.top_ne_coe

/-- Before `τ*`, the price stays below `a_z = b1(c1(z))` (proof of Proposition 7.3, p. 27). -/
lemma S_lt_before_tau (p : Params) (st : Setting Ω) (h71 : 1 < p.σ ^ 2 / p.δ0)
    (hk : 0 < k p) {x : ℝ} (hx : 0 < x) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω)
    (t : ℝ≥0) (ht : (t : WithTop ℝ≥0) < τstar p st x y ω) :
    S p st x y t ω < (b1 p st (c1 p st (z0 p x y))).toReal := by
  have hns := notMem_of_lt_hittingAfter ht (bot_le : (0 : ℝ≥0) ≤ t)
  simp only [state, Set.mem_setOf_eq, not_le] at hns
  obtain ⟨_, hF⟩ := eq_5_3 p st x y hx hy t ω
  obtain ⟨hmono, hc1, hS1'⟩ := corollary_5_5_c1 p st h71.le hk.ne'
  obtain ⟨hb1anti, _, hS1, -⟩ := corollary_4_5 p st
  have hYm := Y_mem p st x hy t ω
  set Yt := Y p st x y t ω
  set St := S p st x y t ω
  set zt := Real.log x + p.σ ^ 2 / p.δ0 * Real.log (y / (1 - y)) + k p * (t : ℝ)
  -- not in `S1'`
  have hnot' : (zt, Yt) ∉ S1' p st := by
    intro h
    have h2 := h.2
    simp only [v, H1] at h2
    rw [← hF] at h2
    linarith
  rw [hS1'] at hnot'
  simp only [Set.mem_setOf_eq, not_and, not_le] at hnot'
  have hc1lt : c1 p st zt < Yt := hnot' hYm
  have hzle : z0 p x y ≤ zt := by
    simp only [zt, z0]
    have : 0 ≤ k p * (t : ℝ) := mul_nonneg hk.le t.2
    linarith
  have hc1le : c1 p st (z0 p x y) ≤ Yt := (hmono hzle).trans hc1lt.le
  -- not in `S1`
  have hnotS1 : (St, Yt) ∉ S1 p st := by
    intro h
    have h2 := h.2
    simp only at h2
    linarith
  rw [hS1] at hnotS1
  have hdom : (St, Yt) ∈ dom := ⟨S_pos p st hx y t ω, Set.Ioo_subset_Icc_self hYm⟩
  simp only [Set.mem_setOf_eq, not_and, not_le] at hnotS1
  have hlt : ENNReal.ofReal St < b1 p st Yt := hnotS1 hdom
  have hcz := hc1 (z0 p x y)
  have hb1le : b1 p st Yt ≤ b1 p st (c1 p st (z0 p x y)) :=
    hb1anti hcz.1 (Set.Ioo_subset_Icc_self hYm) hc1le
  have hc1pos : 0 < c1 p st (z0 p x y) := lemma_7_2 p st h71 hk.ne' _
  have hc1lt1 : c1 p st (z0 p x y) < 1 := lt_of_le_of_lt hcz.2 (yK_lt_one p _)
  have hfin := lemma_4_6 p st (c1 p st (z0 p x y)) ⟨hc1pos, hc1lt1⟩
  exact (ENNReal.ofReal_lt_iff_lt_toReal (S_pos p st hx y t ω).le hfin.ne).1
    (lt_of_lt_of_le hlt hb1le)

/-- Up to and including `τ*`, the price is bounded by `max(a_z, x)` (on `{B_0 = 0}`). -/
lemma S_le_upto_tau (p : Params) (st : Setting Ω) (h71 : 1 < p.σ ^ 2 / p.δ0)
    (hk : 0 < k p) {x : ℝ} (hx : 0 < x) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω)
    (hB : st.B 0 ω = 0) (u : ℝ≥0) (hu : (u : WithTop ℝ≥0) ≤ τstar p st x y ω) :
    S p st x y u ω ≤ max (b1 p st (c1 p st (z0 p x y))).toReal x := by
  set A := (b1 p st (c1 p st (z0 p x y))).toReal
  rcases hu.lt_or_eq with hlt | heq
  · exact (S_lt_before_tau p st h71 hk hx hy ω u hlt).le.trans (le_max_left _ _)
  · rcases eq_or_ne u 0 with rfl | hu0
    · rw [S_zero_of_B p st x y ω hB]; exact le_max_right _ _
    · have hC : IsClosed {t : ℝ≥0 | S p st x y t ω ≤ max A x} :=
        isClosed_le (continuous_S p st x y ω) continuous_const
      have hsub : Set.Iio u ⊆ {t : ℝ≥0 | S p st x y t ω ≤ max A x} := by
        intro t ht
        have : (t : WithTop ℝ≥0) < τstar p st x y ω := by
          rw [← heq]; exact WithTop.coe_lt_coe.mpr ht
        exact (S_lt_before_tau p st h71 hk hx hy ω t this).le.trans (le_max_left _ _)
      have hcl := closure_minimal hsub hC
      rw [closure_Iio' ⟨0, pos_iff_ne_zero.mpr hu0⟩] at hcl
      exact hcl (le_refl u)

lemma exp_neg_le_one (p : Params) (u : ℝ≥0) : Real.exp (-p.r * (u : ℝ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have := p.r_pos
  have : 0 ≤ (u : ℝ) := u.2
  nlinarith

lemma discV_le (p : Params) (st : Setting Ω) {x : ℝ} (y : ℝ) (u : ℝ≥0) (ω : Ω) (M : ℝ)
    (hM : S p st x y u ω ≤ M) : |discV p st x y u ω| ≤ G2 p M := by
  unfold discV
  have h0 := V_nonneg p st (S p st x y u ω) (Y p st x y u ω)
  have h1 := V_le_G2 p st (S p st x y u ω) (Y p st x y u ω)
  have h2 := G2_mono p hM
  have he := exp_neg_le_one p u
  have hep := Real.exp_pos (-p.r * (u : ℝ))
  rw [abs_of_nonneg (mul_nonneg hep.le h0)]
  calc Real.exp (-p.r * (u : ℝ)) * V p st (S p st x y u ω) (Y p st x y u ω)
      ≤ 1 * G2 p M := by
        apply mul_le_mul he (h1.trans h2) h0 zero_le_one
    _ = G2 p M := one_mul _

lemma untopA_min_coe_exists (T : WithTop ℝ≥0) :
    ∃ m : ℝ≥0 → ℝ≥0, Continuous m ∧ ∀ s : ℝ≥0, (min (s : WithTop ℝ≥0) T).untopA = m s := by
  induction T with
  | top => exact ⟨id, continuous_id, fun s => by rw [min_top_right]; rfl⟩
  | coe T =>
    refine ⟨fun s => min s T, continuous_id.min continuous_const, fun s => ?_⟩
    rw [← WithTop.coe_min]; rfl

/-- The key inequality of the proof of Proposition 7.3: `V(x, y) ≤ M(τ*, γ)` for all `γ`. -/
theorem V_le_M_tau (p : Params) (st : Setting Ω) (h71 : 1 < p.σ ^ 2 / p.δ0)
    (hk : 0 < k p) {x : ℝ} (hx : 0 < x) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (γ : Ω → WithTop ℝ≥0) (hγ : IsST p st x y γ) :
    ENNReal.ofReal (V p st x y) ≤ M p st x y (τstar p st x y) γ := by
  haveI := st.isProb
  have hyI : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  obtain ⟨_, hsub⟩ := theorem_3_2_sub p st x y hx.le hyI
  set τs := τstar p st x y
  set X := stoppedProcess (discV p st x y) τs
  set A := (b1 p st (c1 p st (z0 p x y))).toReal
  have hBae := st.brownian.eval_zero_ae_eq_zero
  -- right-continuity of the stopped process
  have hrc : ∀ ω s, ContinuousWithinAt (fun u => X u ω) (Set.Ici s) s := by
    intro ω s
    obtain ⟨m, hm, hmeq⟩ := untopA_min_coe_exists (τs ω)
    have : (fun u => X u ω) = fun u => discV p st x y (m u) ω := by
      funext u; simp only [X, stoppedProcess, hmeq]
    rw [this]
    exact ((continuous_discV p st hx hy ω).comp hm).continuousWithinAt
  -- boundedness of the stopped process
  have hCb : ∀ᵐ ω ∂st.P, ∀ s, |X s ω| ≤ G2 p (max A x) := by
    filter_upwards [hBae] with ω hω s
    simp only [X, stoppedProcess]
    apply discV_le
    apply S_le_upto_tau p st h71 hk hx hy ω hω
    rw [DynkinOSAux.coe_untopA_min]
    exact min_le_right _ _
  -- initial value
  have hX0 : ∫ ω, X 0 ω ∂st.P = V p st x y := by
    have : (fun ω => X 0 ω) =ᵐ[st.P] fun _ => V p st x y := by
      filter_upwards [hBae] with ω hω
      have hmin : min ((0 : ℝ≥0) : WithTop ℝ≥0) (τs ω) = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
        min_eq_left (le_hittingAfter (n := (0 : ℝ≥0)) ω)
      simp only [X, stoppedProcess, hmin, discV]
      show Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * V p st (S p st x y 0 ω) (Y p st x y 0 ω) = _
      rw [S_zero_of_B p st x y ω hω, Y_zero_of_B p st hx ω hω]
      simp
    rw [integral_congr_ae this]
    simp
  -- pointwise comparison with the payoff
  have hpt : ∀ (n : ℕ) ω, ENNReal.ofReal (stoppedProcess X γ (n : ℝ≥0) ω) ≤
      dynkinPayoff (L1 p st x y) (U2 p st x y) τs γ ω +
        ENNReal.ofReal (Real.exp (-p.r * (n : ℝ)) * G2 p A) := by
    intro n ω
    have heq : stoppedProcess X γ (n : ℝ≥0) ω =
        discV p st x y (min (min ((n : ℝ≥0) : WithTop ℝ≥0) (γ ω)) (τs ω)).untopA ω := by
      simp only [X, stoppedProcess]
      rw [DynkinOSAux.coe_untopA_min]
    rw [heq]
    by_cases hA : τs ω ≤ min ((n : ℝ≥0) : WithTop ℝ≥0) (γ ω)
    · -- the buyer stops first
      rw [min_eq_right hA]
      have hne : τs ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hA.trans (min_le_left _ _))
      obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hT]
      have hV := V_le_G1_at_tau p st hx hy ω T hT.symm
      have hpay : dynkinPayoff (L1 p st x y) (U2 p st x y) τs γ ω = L1 p st x y T ω := by
        unfold dynkinPayoff
        rw [if_pos ⟨hA.trans (min_le_right _ _), hne⟩, ← hT]
        rfl
      rw [hpay]
      refine le_trans ?_ le_self_add
      unfold discV L1
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le
    · rw [not_le] at hA
      rcases lt_or_ge (γ ω) ((n : ℝ≥0) : WithTop ℝ≥0) with hG | hG
      · -- the seller stops first
        rw [min_eq_right hG.le] at hA ⊢
        rw [min_eq_left hA.le]
        have hne : γ ω ≠ ⊤ := ne_top_of_lt hG
        obtain ⟨G, hGe⟩ := WithTop.ne_top_iff_exists.mp hne
        rw [← hGe]
        have hpay : dynkinPayoff (L1 p st x y) (U2 p st x y) τs γ ω = U2 p st x y G ω := by
          unfold dynkinPayoff
          rw [if_neg (fun h => absurd h.1 (not_le.mpr hA)), if_pos hA, ← hGe]
          rfl
        rw [hpay]
        refine le_trans ?_ le_self_add
        unfold discV U2
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (V_le_G2 p st _ _) (Real.exp_pos _).le
      · -- nobody has stopped before time n
        rw [min_eq_left hG] at hA ⊢
        rw [min_eq_left hA.le]
        refine le_trans ?_ le_add_self
        apply ENNReal.ofReal_le_ofReal
        have hS := S_lt_before_tau p st h71 hk hx hy ω n hA
        show discV p st x y (n : ℝ≥0) ω ≤ _
        unfold discV
        have : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by simp
        rw [this]
        exact mul_le_mul_of_nonneg_left ((V_le_G2 p st _ _).trans (G2_mono p hS.le))
          (Real.exp_pos _).le
  have hn : ∀ n : ℕ, ENNReal.ofReal (V p st x y) ≤
      M p st x y τs γ + ENNReal.ofReal (Real.exp (-p.r * (n : ℝ)) * G2 p A) := by
    intro n
    have hOS := DynkinOSAux.submartingale_integral_zero_le_stopped hsub hrc _ hCb hγ (n : ℝ≥0)
    rw [hX0] at hOS
    calc ENNReal.ofReal (V p st x y)
        ≤ ENNReal.ofReal (∫ ω, stoppedProcess X γ (n : ℝ≥0) ω ∂st.P) :=
          ENNReal.ofReal_le_ofReal hOS
      _ ≤ ∫⁻ ω, ENNReal.ofReal (stoppedProcess X γ (n : ℝ≥0) ω) ∂st.P :=
          ofReal_integral_le_lintegral _
      _ ≤ ∫⁻ ω, (dynkinPayoff (L1 p st x y) (U2 p st x y) τs γ ω +
            ENNReal.ofReal (Real.exp (-p.r * (n : ℝ)) * G2 p A)) ∂st.P := lintegral_mono (hpt n)
      _ = M p st x y τs γ + ENNReal.ofReal (Real.exp (-p.r * (n : ℝ)) * G2 p A) := by
          rw [lintegral_add_right _ measurable_const]
          simp [M, dynkinM]
  have hexp : Tendsto (fun n : ℕ => Real.exp (-p.r * (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos p.r_pos))
  have hc : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-p.r * (n : ℝ)) * G2 p A)) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    simpa using hexp.mul_const (G2 p A)
  have htend := (tendsto_const_nhds (x := M p st x y τs γ)).add hc
  rw [add_zero] at htend
  exact ge_of_tendsto htend (Eventually.of_forall hn)

end DynkinRedAux

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open DynkinIncInfo.Saddle

theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (h71 : 1 < p.σ ^ 2 / p.δ0) (hk : 0 < k p)
    (x y : ℝ) (hx : 0 < x) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    IsSaddle p st x y (τstar p st x y) (γstar p st x y) := by
  have hyI : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  obtain ⟨hτ, _⟩ := theorem_3_2_sub p st x y hx.le hyI
  obtain ⟨hγ, hsel⟩ := theorem_3_2_seller p st x y hx.le hyI
  have hVup : Vup p st x y = ENNReal.ofReal (V p st x y) :=
    (ENNReal.ofReal_toReal (DynkinRedAux.Vup_ne_top p st x y)).symm
  have hle : ∀ τ, IsST p st x y τ → M p st x y τ (γstar p st x y) ≤ ENNReal.ofReal (V p st x y) := by
    intro τ hτ'
    rw [← hVup, hsel]
    exact le_iSup₂ (f := fun τ (_ : IsST p st x y τ) => M p st x y τ (γstar p st x y)) τ hτ'
  refine ⟨hτ, hγ, fun τ γ hτ' hγ' => ⟨?_, ?_⟩⟩
  · exact (hle τ hτ').trans (DynkinRedAux.V_le_M_tau p st h71 hk hx hy _ hγ)
  · exact (hle _ hτ).trans (DynkinRedAux.V_le_M_tau p st h71 hk hx hy γ hγ')
