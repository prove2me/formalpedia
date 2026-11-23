-- Prove2me | solution 1 for DistributionTheoryMission.convergence
-- status  : ACCEPTED   (disprove)
-- author  : @Xeroth
-- created : 2026-11-23T17:26:31.425431+00:00
-- url     : https://prove2.me/submissions/d923d49c-9403-44ce-b055-ab92f31845b4

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_ConvergenceTargets
import Mathlib

open MeasureTheory Filter Topology

namespace PathoStair

noncomputable def eps (k : ℕ) : ℝ := (1/16) * (1/2) ^ k

theorem eps_pos (k : ℕ) : 0 < eps k := by unfold eps; positivity

def qs (k : ℕ) : ℚ := Denumerable.ofNat ℚ k

def U : Set ℝ := ⋃ k, Metric.ball ((qs k : ℚ) : ℝ) (eps k)

noncomputable def h (x : ℝ) : ℝ := (volume (Set.Icc 0 x \ U)).toReal

theorem vol_fin (x : ℝ) : volume (Set.Icc 0 x \ U) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.sdiff_subset)

theorem h_nonneg (x : ℝ) : 0 ≤ h x := ENNReal.toReal_nonneg

theorem h_mono {x y : ℝ} (hxy : x ≤ y) : h x ≤ h y :=
  ENNReal.toReal_mono (vol_fin y)
    (measure_mono (Set.sdiff_subset_sdiff_left (Set.Icc_subset_Icc_right hxy)))

theorem h_lip {x y : ℝ} (hxy : x ≤ y) : h y ≤ h x + (y - x) := by
  have hsub : Set.Icc 0 y \ U ⊆ (Set.Icc 0 x \ U) ∪ Set.Icc x y := by
    rintro z ⟨⟨hz0, hzy⟩, hzU⟩
    by_cases hzx : z ≤ x
    · exact Or.inl ⟨⟨hz0, hzx⟩, hzU⟩
    · exact Or.inr ⟨(not_le.1 hzx).le, hzy⟩
  have hm := (measure_mono hsub).trans (measure_union_le (μ := volume) _ _)
  rw [Real.volume_Icc] at hm
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨vol_fin x, ENNReal.ofReal_ne_top⟩) hm
  rw [ENNReal.toReal_add (vol_fin x) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)] at this
  exact this

theorem h_abs (x y : ℝ) : |h x - h y| ≤ |x - y| := by
  rcases le_total x y with hxy | hxy
  · have := h_mono hxy; have := h_lip hxy
    rw [abs_le, abs_of_nonpos (by linarith)]; constructor <;> linarith
  · have := h_mono hxy; have := h_lip hxy
    rw [abs_le, abs_of_nonneg (by linarith)]; constructor <;> linarith

theorem h_nonpos {x : ℝ} (hx : x ≤ 0) : h x = 0 := by
  apply le_antisymm _ (h_nonneg x)
  have : volume (Set.Icc 0 x \ U) = 0 := by
    apply le_antisymm _ bot_le
    calc volume (Set.Icc 0 x \ U) ≤ volume (Set.Icc 0 x) := measure_mono Set.sdiff_subset
      _ = 0 := by rw [Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith)
  simp [h, this]

theorem h_le_one {x : ℝ} (hx : x ≤ 1) : h x ≤ 1 := by
  unfold h
  have : volume (Set.Icc 0 x \ U) ≤ ENNReal.ofReal 1 :=
    (measure_mono Set.sdiff_subset).trans (by rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal (by linarith))
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
  rwa [ENNReal.toReal_ofReal (by norm_num)] at this

theorem vol_U_le : volume U ≤ ENNReal.ofReal (1/4) := by
  have hs : Summable (fun k => 2 * eps k) := by
    unfold eps
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _ |>.mul_left _
  have ht : ∑' k, 2 * eps k = 1/4 := by
    unfold eps
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc volume U ≤ ∑' k, volume (Metric.ball ((qs k : ℚ) : ℝ) (eps k)) := measure_iUnion_le _
    _ = ∑' k, ENNReal.ofReal (2 * eps k) := by simp [Real.volume_ball]
    _ = ENNReal.ofReal (∑' k, 2 * eps k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by have := eps_pos k; positivity) hs).symm
    _ = ENNReal.ofReal (1/4) := by rw [ht]

theorem h_one : 3/4 ≤ h 1 := by
  have hsub : Set.Icc (0:ℝ) 1 ⊆ (Set.Icc 0 1 \ U) ∪ U := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inr hzU
    · exact Or.inl ⟨hz, hzU⟩
  have hm := (measure_mono hsub).trans (measure_union_le (μ := volume) _ _)
  rw [Real.volume_Icc] at hm
  have hm2 := hm.trans (add_le_add le_rfl vol_U_le)
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨vol_fin 1, ENNReal.ofReal_ne_top⟩) hm2
  rw [ENNReal.toReal_add (vol_fin 1) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)] at this
  unfold h
  linarith

theorem h_locConst (q : ℚ) : ∃ ρ > 0, ∀ y : ℝ, |y - q| < ρ → h y = h q := by
  obtain ⟨k, e⟩ : ∃ k, qs k = q := ⟨_, Denumerable.ofNat_encode q⟩
  refine ⟨eps k, eps_pos _, fun y hy => ?_⟩
  have hball : ∀ z : ℝ, |z - q| < eps k → z ∈ U := by
    intro z hz
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    rw [e]
    exact hz
  have hset : Set.Icc 0 y \ U = Set.Icc 0 (q:ℝ) \ U := by
    ext z
    constructor
    · rintro ⟨⟨hz0, hzy⟩, hzU⟩
      refine ⟨⟨hz0, ?_⟩, hzU⟩
      by_contra hzq
      push Not at hzq
      exact hzU (hball z (by rw [abs_lt] at hy ⊢; constructor <;> linarith))
    · rintro ⟨⟨hz0, hzq⟩, hzU⟩
      refine ⟨⟨hz0, ?_⟩, hzU⟩
      by_contra hzy
      push Not at hzy
      exact hzU (hball z (by rw [abs_lt] at hy ⊢; constructor <;> linarith))
  simp [h, hset]

/-- The staircase bump: Lipschitz, locally constant near every rational, supported in `[0,2]`. -/
noncomputable def psi (x : ℝ) : ℝ := min (h x) (h (2 - x))

theorem psi_abs (x y : ℝ) : |psi x - psi y| ≤ |x - y| := by
  unfold psi
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (h_abs x y) ?_)
  have := h_abs (2 - x) (2 - y)
  rwa [show 2 - x - (2 - y) = -(x - y) by ring, abs_neg] at this

theorem psi_nonneg (x : ℝ) : 0 ≤ psi x := le_min (h_nonneg _) (h_nonneg _)

theorem psi_le_one (x : ℝ) : psi x ≤ 1 := by
  unfold psi
  rcases le_total x 1 with hx | hx
  · exact (min_le_left _ _).trans (h_le_one hx)
  · exact (min_le_right _ _).trans (h_le_one (by linarith))

theorem psi_out {x : ℝ} (hx : x ≤ 0 ∨ 2 ≤ x) : psi x = 0 := by
  unfold psi
  rcases hx with hx | hx
  · rw [h_nonpos hx]; exact min_eq_left (h_nonneg _)
  · rw [h_nonpos (by linarith : 2 - x ≤ 0)]; exact min_eq_right (h_nonneg _)

theorem psi_one : 3/4 ≤ psi 1 := by
  unfold psi
  norm_num
  exact h_one

theorem psi_locConst (q : ℚ) : ∃ ρ > 0, ∀ y : ℝ, |y - q| < ρ → psi y = psi q := by
  obtain ⟨ρ1, h1, k1⟩ := h_locConst q
  obtain ⟨ρ2, h2, k2⟩ := h_locConst (2 - q)
  refine ⟨min ρ1 ρ2, lt_min h1 h2, fun y hy => ?_⟩
  unfold psi
  rw [k1 y (lt_of_lt_of_le hy (min_le_left _ _))]
  have : |(2 - y) - ((2 - q : ℚ) : ℝ)| < ρ2 := by
    push_cast
    rw [show 2 - y - (2 - (q:ℝ)) = -(y - q) by ring, abs_neg]
    exact lt_of_lt_of_le hy (min_le_right _ _)
  rw [k2 _ this]
  push_cast
  rfl

end PathoStair

set_option autoImplicit true

open ComputableAnalysis Filter Topology

namespace ComputableDistributions
namespace CBridge

theorem ofRat_valid' (q : ℚ) : (RealCompute.ofRat q).Valid := RealCompute.ofRat_valid q

theorem add_valid' {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    (RealCompute.add x y).Valid := RealCompute.add_valid hx hy

/-- Classical value of a raw real name (meaningful for valid names). -/
noncomputable def val (x : RealCompute) : ℝ := ⨆ n, (((x.compute n).lo : ℚ) : ℝ)

theorem lo_le_hi {x : RealCompute} (hx : x.Valid) (n m : Nat) :
    (x.compute n).lo ≤ (x.compute m).hi := by
  have h := hx.2.1 n (max n m) (le_max_left _ _)
  have h' := hx.2.1 m (max n m) (le_max_right _ _)
  linarith [h.1, h.2.1, h'.2.2]

theorem mem {x : RealCompute} (hx : x.Valid) (n : Nat) :
    (((x.compute n).lo : ℚ) : ℝ) ≤ val x ∧ val x ≤ (((x.compute n).hi : ℚ) : ℝ) := by
  have hb : BddAbove (Set.range fun n => (((x.compute n).lo : ℚ) : ℝ)) :=
    ⟨(x.compute 0).hi, by
      rintro _ ⟨k, rfl⟩
      show (((x.compute k).lo : ℚ) : ℝ) ≤ _
      exact_mod_cast lo_le_hi hx k 0⟩
  exact ⟨le_ciSup hb n, ciSup_le fun k => by exact_mod_cast lo_le_hi hx k n⟩

theorem width_small {x : RealCompute} (hx : x.Valid) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → (((x.compute n).hi : ℚ) : ℝ) - (((x.compute n).lo : ℚ) : ℝ) ≤ ε := by
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  obtain ⟨N, hN⟩ := hx.2.2 ⟨q, by exact_mod_cast hq0⟩
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  unfold QInterval.width at h
  have h2 : (((x.compute n).hi - (x.compute n).lo : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
  push_cast at h2
  linarith

theorem eq_val_of_mem {x : RealCompute} (hx : x.Valid) {r : ℝ}
    (hr : ∀ n, (((x.compute n).lo : ℚ) : ℝ) ≤ r ∧ r ≤ (((x.compute n).hi : ℚ) : ℝ)) :
    r = val x := by
  by_contra hne
  have hpos : 0 < |r - val x| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := width_small hx (|r - val x| / 2) (by linarith)
  have h1 := hN N le_rfl
  have h2 := hr N
  have h3 := mem hx N
  have : |r - val x| ≤ (((x.compute N).hi : ℚ) : ℝ) - (((x.compute N).lo : ℚ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem val_eq_of_equiv {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    val x = val y := by
  by_contra hne
  have hpos : 0 < |val x - val y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := width_small hx (|val x - val y| / 3) (by linarith)
  obtain ⟨M, hM⟩ := width_small hy (|val x - val y| / 3) (by linarith)
  have h1 := hN (max N M) (le_max_left _ _)
  have h2 := hM (max N M) (le_max_right _ _)
  have hov := (RealCompute.compareAt_overlap_iff x y (max N M) (max N M)).1 (h (max N M))
  obtain ⟨o1, o2⟩ := hov
  have o1' : (((x.compute (max N M)).lo : ℚ) : ℝ) ≤ (((y.compute (max N M)).hi : ℚ) : ℝ) := by
    exact_mod_cast o1
  have o2' : (((y.compute (max N M)).lo : ℚ) : ℝ) ≤ (((x.compute (max N M)).hi : ℚ) : ℝ) := by
    exact_mod_cast o2
  have h3 := mem hx (max N M)
  have h4 := mem hy (max N M)
  have : |val x - val y| ≤ 2 * (|val x - val y| / 3) := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem equiv_of_val_eq {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (h : val x = val y) :
    x.Equiv y := by
  intro n
  apply (RealCompute.compareAt_overlap_iff x y n n).2
  have h3 := mem hx n
  have h4 := mem hy n
  constructor
  · have : (((x.compute n).lo : ℚ) : ℝ) ≤ (((y.compute n).hi : ℚ) : ℝ) := by linarith
    exact_mod_cast this
  · have : (((y.compute n).lo : ℚ) : ℝ) ≤ (((x.compute n).hi : ℚ) : ℝ) := by linarith
    exact_mod_cast this

theorem val_ofRat (q : ℚ) : val (RealCompute.ofRat q) = q := by
  symm
  apply eq_val_of_mem (x := RealCompute.ofRat q) (ofRat_valid' q)
  intro n
  exact ⟨le_rfl, le_rfl⟩

theorem le_iff {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    x.Le y ↔ val x ≤ val y := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨N, hN⟩ := width_small hx ((val x - val y) / 3) (by linarith)
    obtain ⟨M, hM⟩ := width_small hy ((val x - val y) / 3) (by linarith)
    have h1 := hN N le_rfl
    have h2 := hM M le_rfl
    have h3 := mem hx N
    have h4 := mem hy M
    have h5 : (((x.compute N).lo : ℚ) : ℝ) ≤ (((y.compute M).hi : ℚ) : ℝ) := by
      exact_mod_cast h N M
    linarith
  · intro h n m
    have h3 := mem hx n
    have h4 := mem hy m
    have : (((x.compute n).lo : ℚ) : ℝ) ≤ (((y.compute m).hi : ℚ) : ℝ) := by linarith
    exact_mod_cast this

theorem val_add {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.add x y) = val x + val y := by
  symm
  apply eq_val_of_mem (add_valid' hx hy)
  intro n
  have h3 := mem hx n
  have h4 := mem hy n
  show (((x.compute n).lo + (y.compute n).lo : ℚ) : ℝ) ≤ _ ∧
    _ ≤ (((x.compute n).hi + (y.compute n).hi : ℚ) : ℝ)
  push_cast
  constructor <;> linarith

theorem mul_mem_aux {a b c d s t : ℝ} (hs : a ≤ s ∧ s ≤ b) (ht : c ≤ t ∧ t ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ s * t ∧
      s * t ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  have k1 : min (a * t) (b * t) ≤ s * t ∧ s * t ≤ max (a * t) (b * t) := by
    rcases le_total 0 t with h | h
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  have k2 : ∀ e : ℝ, min (e * c) (e * d) ≤ e * t ∧ e * t ≤ max (e * c) (e * d) := by
    intro e
    rcases le_total 0 e with h | h
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  obtain ⟨ka1, ka2⟩ := k2 a
  obtain ⟨kb1, kb2⟩ := k2 b
  constructor
  · exact le_trans (le_min (le_trans (min_le_left _ _) ka1) (le_trans (min_le_right _ _) kb1)) k1.1
  · exact le_trans k1.2 (max_le (le_trans ka2 (le_max_left _ _)) (le_trans kb2 (le_max_right _ _)))


theorem val_mul {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.mul x y) = val x * val y := by
  symm
  apply eq_val_of_mem (RealCompute.mul_valid hx hy)
  intro n
  have h := mul_mem_aux (mem hx n) (mem hy n)
  show ((min4 _ _ _ _ : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((max4 _ _ _ _ : ℚ) : ℝ)
  have e1 : ∀ a b : ℚ, minRat a b = min a b := fun a b => by unfold minRat; rw [min_def]
  have e2 : ∀ a b : ℚ, maxRat2 a b = max a b := fun a b => by unfold maxRat2; rw [max_def]
  simp only [min4, max4, e1, e2]
  push_cast
  exact h

theorem tendsto_val {u : Nat → RealCompute} {x : RealCompute} (h : RawLimit.TendsTo u x) :
    Tendsto (fun n => val (u n)) atTop (𝓝 (val x)) := by
  obtain ⟨hx, hu, hc⟩ := h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := width_small hx (ε / 3) (by linarith)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (show (0:ℝ) < ε / 3 by linarith)
  obtain ⟨N, hN⟩ := hc m ⟨q, by exact_mod_cast hq0⟩
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have l1 := (le_iff (ofRat_valid' _) (hu n)).1 h1
  have l2 := (le_iff (hu n) (ofRat_valid' _)).1 h2
  rw [val_ofRat] at l1 l2
  simp only [QInterval.expand] at l1 l2
  push_cast at l1 l2
  have w := hm m le_rfl
  have mx := mem hx m
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem smallApprox_iff {x : RealCompute} (hx : x.Valid) (C : ℚ) :
    RealApproximationOrder.Small (RealApproximationOrder.parameter x hx) C ↔ |val x| ≤ (C : ℝ) := by
  show (RealCompute.ofRat (-C)).Le x ∧ x.Le (RealCompute.ofRat C) ↔ _
  rw [le_iff (ofRat_valid' _) hx, le_iff hx (ofRat_valid' _), val_ofRat,
    val_ofRat, abs_le]
  push_cast
  rfl


theorem sub_valid' {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    (RealCompute.sub x y).Valid := RealCompute.sub_valid hx hy

theorem val_sub {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.sub x y) = val x - val y := by
  symm
  apply eq_val_of_mem (sub_valid' hx hy)
  intro n
  have h3 := mem hx n
  have h4 := mem hy n
  show (((x.compute n).lo - (y.compute n).hi : ℚ) : ℝ) ≤ _ ∧
    _ ≤ (((x.compute n).hi - (y.compute n).lo : ℚ) : ℝ)
  push_cast
  constructor <;> linarith

theorem val_scaleRat {c : ℚ} {x : RealCompute} (hx : x.Valid) :
    val (RealCompute.scaleRat c x) = c * val x := by
  symm
  apply eq_val_of_mem (RealCompute.scaleRat_valid hx)
  intro n
  have h := mem hx n
  show (((RealCompute.scaleRatCompute c x n).lo : ℚ) : ℝ) ≤ _ ∧
    _ ≤ (((RealCompute.scaleRatCompute c x n).hi : ℚ) : ℝ)
  unfold RealCompute.scaleRatCompute
  split_ifs with hc
  · have hc' : (0:ℝ) ≤ c := by exact_mod_cast hc
    push_cast
    constructor <;> nlinarith
  · have hc' : (c:ℝ) < 0 := by push Not at hc; exact_mod_cast hc
    push_cast
    constructor <;> nlinarith

theorem tendsto_of_val {u : Nat → RealCompute} {x : RealCompute} (hx : x.Valid)
    (hu : ∀ n, (u n).Valid) (h : Tendsto (fun n => val (u n)) atTop (𝓝 (val x))) :
    RawLimit.TendsTo u x := by
  refine ⟨hx, hu, fun m eps => ?_⟩
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h) eps.val (by exact_mod_cast eps.2)
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  rw [Real.dist_eq, abs_lt] at hd
  have mx := mem hx m
  constructor
  · rw [le_iff (ofRat_valid' _) (hu n), val_ofRat]
    simp only [QInterval.expand]
    push_cast
    linarith
  · rw [le_iff (hu n) (ofRat_valid' _), val_ofRat]
    simp only [QInterval.expand]
    push_cast
    linarith

theorem smallSub_iff {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (C : ℚ) :
    RealApproximationOrder.Small
      (RealApproximationOrder.sub (RealApproximationOrder.parameter x hx)
        (RealApproximationOrder.parameter y hy)) C ↔ |val x - val y| ≤ (C : ℝ) := by
  show (RealCompute.ofRat (-C)).Le (RealCompute.sub x y) ∧
    (RealCompute.sub x y).Le (RealCompute.ofRat C) ↔ _
  rw [le_iff (ofRat_valid' _) (sub_valid' hx hy), le_iff (sub_valid' hx hy) (ofRat_valid' _),
    val_ofRat, val_ofRat, val_sub hx hy, abs_le]
  push_cast
  rfl

/-- Dyadic name of a classical real. -/
noncomputable def name (r : ℝ) : RealCompute where
  compute := fun n => { lo := (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n, hi := ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n }

theorem name_lo_mono (r : ℝ) (n k : ℕ) :
    (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n ≤ (⌊r * 2 ^ (n + k)⌋ : ℚ) / 2 ^ (n + k) := by
  have h1 : ((⌊r * 2 ^ n⌋ * 2 ^ k : ℤ) : ℝ) ≤ r * 2 ^ (n + k) := by
    push_cast
    rw [pow_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (Int.floor_le _) (by positivity)
  have h2 : ⌊r * 2 ^ n⌋ * 2 ^ k ≤ ⌊r * 2 ^ (n + k)⌋ := Int.le_floor.2 h1
  have h3 : ((⌊r * 2 ^ n⌋ * 2 ^ k : ℤ) : ℚ) ≤ (⌊r * 2 ^ (n + k)⌋ : ℚ) := by exact_mod_cast h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at h3
  rw [show (2:ℚ) ^ (n + k) = 2 ^ n * 2 ^ k from pow_add _ _ _]
  nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) n]

theorem name_hi_anti (r : ℝ) (n k : ℕ) :
    ((⌊r * 2 ^ (n + k)⌋ : ℚ) + 1) / 2 ^ (n + k) ≤ ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n := by
  have h1 : r * 2 ^ (n + k) < (((⌊r * 2 ^ n⌋ + 1) * 2 ^ k : ℤ) : ℝ) := by
    push_cast
    rw [pow_add, ← mul_assoc]
    exact mul_lt_mul_of_pos_right (Int.lt_floor_add_one _) (by positivity)
  have h2 : ⌊r * 2 ^ (n + k)⌋ < (⌊r * 2 ^ n⌋ + 1) * 2 ^ k := Int.floor_lt.2 h1
  have h3 : ((⌊r * 2 ^ (n + k)⌋ + 1 : ℤ) : ℚ) ≤ (((⌊r * 2 ^ n⌋ + 1) * 2 ^ k : ℤ) : ℚ) := by
    exact_mod_cast h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at h3
  rw [show (2:ℚ) ^ (n + k) = 2 ^ n * 2 ^ k from pow_add _ _ _]
  nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) n]

theorem name_valid (r : ℝ) : (name r).Valid := by
  refine ⟨fun n => ?_, fun n m hnm => ?_, fun eps => ?_⟩
  · show (0:ℚ) ≤ ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n - (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n
    rw [← sub_div, add_sub_cancel_left]; positivity
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    refine ⟨name_lo_mono r n k, ?_, name_hi_anti r n k⟩
    show (⌊r * 2 ^ (n + k)⌋ : ℚ) / 2 ^ (n + k) ≤ ((⌊r * 2 ^ (n + k)⌋ : ℚ) + 1) / 2 ^ (n + k)
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one eps.2 (show (1/2 : ℚ) < 1 by norm_num)
    refine ⟨N, fun n hn => ?_⟩
    show ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n - (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n ≤ eps.val
    rw [← sub_div, add_sub_cancel_left]
    have : (1:ℚ) / 2 ^ n ≤ (1/2) ^ N := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hn)
    linarith

theorem val_name (r : ℝ) : val (name r) = r := by
  symm
  apply eq_val_of_mem (name_valid r)
  intro n
  have hp : (0:ℝ) < 2 ^ n := by positivity
  show (((⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n : ℚ) : ℝ) ≤ r ∧ r ≤ ((((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n : ℚ) : ℝ)
  push_cast
  constructor
  · rw [div_le_iff₀ hp]; exact Int.floor_le _
  · rw [le_div_iff₀ hp]; exact (Int.lt_floor_add_one _).le

/-! Classical form of the bracket derivative. -/

def HasDerivR (F : ℚ → ℝ) (x : ℚ) (D : ℝ) : Prop :=
  ∀ a b : ℕ → ℚ, (∀ n, a n < b n ∧ a n ≤ x ∧ x ≤ b n) → Monotone a → Antitone b →
    Tendsto (fun n => ((b n - a n : ℚ) : ℝ)) atTop (𝓝 0) →
    Tendsto (fun n => (F (b n) - F (a n)) / ((b n - a n : ℚ) : ℝ)) atTop (𝓝 D)

def bracket (a b : ℕ → ℚ) : RealCompute where
  compute := fun n => ⟨a n, b n⟩

theorem bracket_valid {a b : ℕ → ℚ} (hab : ∀ n, a n < b n) (ha : Monotone a) (hb : Antitone b)
    (hw : Tendsto (fun n => ((b n - a n : ℚ) : ℝ)) atTop (𝓝 0)) : (bracket a b).Valid := by
  refine ⟨fun n => ?_, fun n m hnm => ⟨ha hnm, (hab m).le, hb hnm⟩, fun eps => ?_⟩
  · show (0:ℚ) ≤ b n - a n
    linarith [hab n]
  · obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hw) eps.val (by exact_mod_cast eps.2)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    show b n - a n ≤ eps.val
    have : ((b n - a n : ℚ) : ℝ) ≤ (eps.val : ℝ) := h.2.le
    exact_mod_cast this

theorem val_secant {f : ℚ → RealCompute} (hf : ∀ r, (f r).Valid) {a b : ℚ} :
    val (BracketDerivative.secant f a b) = (val (f b) - val (f a)) / ((b - a : ℚ) : ℝ) := by
  unfold BracketDerivative.secant
  rw [val_scaleRat (RealCompute.sub_valid (hf b) (hf a))]
  rw [show (f b - f a) = RealCompute.sub (f b) (f a) from rfl, val_sub (hf b) (hf a)]
  push_cast
  ring

theorem hasDeriv_iff {f : ℚ → RealCompute} (hf : ∀ r, (f r).Valid) (x : ℚ) {d : RealCompute}
    (hd : d.Valid) :
    BracketDerivative.HasDerivativeAt (fun _ => True) f (RealCompute.ofRat x) d ↔
      HasDerivR (fun r => val (f r)) x (val d) := by
  rw [BracketDerivative.hasDerivative_iff_secantLimits]
  constructor
  · rintro ⟨-, -, -, -, h⟩ a b hab ha hb hw
    have hA : BracketDerivative.Admissible (fun _ => True) (RealCompute.ofRat x) (bracket a b) := by
      refine ⟨ofRat_valid' x, bracket_valid (fun n => (hab n).1) ha hb hw, ?_,
        fun n => ⟨(hab n).1, fun _ _ _ => trivial⟩⟩
      intro n
      apply (RealCompute.compareAt_overlap_iff _ _ n n).2
      exact ⟨(hab n).2.1, (hab n).2.2⟩
    have := tendsto_val (h _ hA)
    simpa [BracketDerivative.secants, bracket, val_secant hf] using this
  · intro h
    refine ⟨ofRat_valid' x, hd, fun r _ => hf r, ?_, fun A hA => ?_⟩
    · refine ⟨bracket (fun n => x - 1 / ((n:ℚ) + 1)) (fun n => x + 1 / ((n:ℚ) + 1)),
        ofRat_valid' x, ?_, ?_, fun n => ⟨?_, fun _ _ _ => trivial⟩⟩
      · apply bracket_valid
        · intro n; have : (0:ℚ) < 1 / ((n:ℚ) + 1) := by positivity
          linarith
        · intro n m hnm
          have : 1 / ((m:ℚ) + 1) ≤ 1 / ((n:ℚ) + 1) :=
            one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
          show x - 1 / ((n:ℚ) + 1) ≤ x - 1 / ((m:ℚ) + 1)
          linarith
        · intro n m hnm
          have : 1 / ((m:ℚ) + 1) ≤ 1 / ((n:ℚ) + 1) :=
            one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
          show x + 1 / ((m:ℚ) + 1) ≤ x + 1 / ((n:ℚ) + 1)
          linarith
        · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2:ℝ)
          rw [mul_zero] at this
          refine this.congr (fun n => ?_)
          push_cast
          ring
      · intro n
        apply (RealCompute.compareAt_overlap_iff _ _ n n).2
        have : (0:ℚ) ≤ 1 / ((n:ℚ) + 1) := by positivity
        show x - 1 / ((n:ℚ) + 1) ≤ x ∧ x ≤ x + 1 / ((n:ℚ) + 1)
        constructor <;> linarith
      · show x - 1 / ((n:ℚ) + 1) < x + 1 / ((n:ℚ) + 1)
        have : (0:ℚ) < 1 / ((n:ℚ) + 1) := by positivity
        linarith
    · obtain ⟨-, hAv, hAx, hAn⟩ := hA
      have hab : ∀ n, (A.compute n).lo < (A.compute n).hi ∧ (A.compute n).lo ≤ x ∧
          x ≤ (A.compute n).hi := by
        intro n
        have hov := (RealCompute.compareAt_overlap_iff _ _ n n).1 (hAx n)
        exact ⟨(hAn n).1, hov.1, hov.2⟩
      have hw : Tendsto (fun n => (((A.compute n).hi - (A.compute n).lo : ℚ) : ℝ)) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N, hN⟩ := width_small hAv (ε / 2) (by linarith)
        refine ⟨N, fun n hn => ?_⟩
        have h1 := hN n hn
        have h2 := (hab n).1
        have h3 : (((A.compute n).lo : ℚ) : ℝ) < (((A.compute n).hi : ℚ) : ℝ) := by exact_mod_cast h2
        rw [Real.dist_eq, sub_zero, abs_lt]
        push_cast
        constructor <;> linarith
      have := h (fun n => (A.compute n).lo) (fun n => (A.compute n).hi) hab
        (fun n m hnm => (hAv.2.1 n m hnm).1) (fun n m hnm => (hAv.2.1 n m hnm).2.2) hw
      apply tendsto_of_val hd (BracketDerivative.secants_valid (fun r _ => hf r) ⟨ofRat_valid' x, hAv, hAx, hAn⟩)
      simpa [BracketDerivative.secants, val_secant hf] using this


/-! Building tests from classical data. -/

noncomputable def dv {d : ℕ} (φ : TestFunction d) (α : MultiIndex d) (x : QPoint d) : ℝ :=
  val (φ.derivative α x)

theorem dv_vanish {d : ℕ} (φ : TestFunction d) (α : MultiIndex d) (x : QPoint d)
    (hx : ¬ φ.support.Contains x) : dv φ α x = 0 := by
  have := val_eq_of_equiv (φ.derivative_valid α x) (ofRat_valid' 0)
    (φ.derivative_vanishes_off_support α x hx)
  rw [val_ofRat] at this
  simpa [dv] using this

theorem dv_lip {d : ℕ} (φ : TestFunction d) (α : MultiIndex d) (x y : QPoint d) (δ : ℚ)
    (hδ : 0 ≤ δ) (hxy : ∀ i, x i ≤ y i + δ ∧ y i ≤ x i + δ) :
    |dv φ α x - dv φ α y| ≤ ((φ.derivativeLipschitz α * δ : ℚ) : ℝ) :=
  (smallSub_iff _ _ _).1 (φ.derivative_control α x y δ hδ hxy)

theorem dv_deriv {d : ℕ} (φ : TestFunction d) (α : MultiIndex d) (i : Fin d) (x : QPoint d) :
    HasDerivR (fun r => dv φ α (replaceCoordinate x i r)) (x i) (dv φ (incrementIndex α i) x) :=
  (hasDeriv_iff (fun r => φ.derivative_valid α _) (x i) (φ.derivative_valid _ x)).1
    (φ.partialDerivative α i x)

structure ClassicalTest (d : ℕ) where
  D : MultiIndex d → QPoint d → ℝ
  support : RationalBox d
  vanish : ∀ α x, ¬ support.Contains x → D α x = 0
  L : MultiIndex d → ℚ
  L_nonneg : ∀ α, 0 ≤ L α
  control : ∀ α x y (δ : ℚ), 0 ≤ δ → (∀ i, x i ≤ y i + δ ∧ y i ≤ x i + δ) →
    |D α x - D α y| ≤ ((L α * δ : ℚ) : ℝ)
  deriv : ∀ α i x, HasDerivR (fun r => D α (replaceCoordinate x i r)) (x i)
    (D (incrementIndex α i) x)

noncomputable def ClassicalTest.toTest {d : ℕ} (c : ClassicalTest d) : TestFunction d where
  derivative α x := name (c.D α x)
  derivative_valid α x := name_valid _
  support := c.support
  derivative_vanishes_off_support α x hx := by
    apply equiv_of_val_eq (name_valid _) (ofRat_valid' 0)
    rw [val_name, val_ofRat, c.vanish α x hx]
    simp
  derivativeLipschitz := c.L
  derivativeLipschitz_nonneg := c.L_nonneg
  derivative_control α x y δ hδ hxy := by
    rw [smallSub_iff, val_name, val_name]
    exact c.control α x y δ hδ hxy
  partialDerivative α i x := by
    rw [hasDeriv_iff (fun r => name_valid _) _ (name_valid _)]
    simp only [val_name]
    exact c.deriv α i x

theorem dv_toTest {d : ℕ} (c : ClassicalTest d) (α : MultiIndex d) (x : QPoint d) :
    dv c.toTest α x = c.D α x := val_name _

theorem equivalent_of_dv {d : ℕ} {φ ψ : TestFunction d} (h : ∀ α x, dv φ α x = dv ψ α x) :
    TestFunction.Equivalent φ ψ :=
  fun α x => equiv_of_val_eq (φ.derivative_valid α x) (ψ.derivative_valid α x) (h α x)

theorem dv_of_equivalent {d : ℕ} {φ ψ : TestFunction d} (h : TestFunction.Equivalent φ ψ)
    (α : MultiIndex d) (x : QPoint d) : dv φ α x = dv ψ α x :=
  val_eq_of_equiv (φ.derivative_valid α x) (ψ.derivative_valid α x) (h α x)

theorem hasDerivR_add {F G : ℚ → ℝ} {x : ℚ} {D E : ℝ} (hF : HasDerivR F x D)
    (hG : HasDerivR G x E) : HasDerivR (fun r => F r + G r) x (D + E) := by
  intro a b hab ha hb hw
  refine ((hF a b hab ha hb hw).add (hG a b hab ha hb hw)).congr (fun n => ?_)
  ring

theorem hasDerivR_const_mul {F : ℚ → ℝ} {x : ℚ} {D : ℝ} (c : ℝ) (hF : HasDerivR F x D) :
    HasDerivR (fun r => c * F r) x (c * D) := by
  intro a b hab ha hb hw
  refine ((hF a b hab ha hb hw).const_mul c).congr (fun n => ?_)
  ring

theorem hasDerivR_zero (x : ℚ) : HasDerivR (fun _ => (0:ℝ)) x 0 := by
  intro a b hab ha hb hw
  simp

def hullBox {d : ℕ} (B C : RationalBox d) : RationalBox d where
  lower i := min (B.lower i) (C.lower i)
  upper i := max (B.upper i) (C.upper i)
  ordered i := le_trans (min_le_left _ _) (le_trans (B.ordered i) (le_max_left _ _))

theorem not_contains_hull_left {d : ℕ} {B C : RationalBox d} {x : QPoint d}
    (h : ¬ (hullBox B C).Contains x) : ¬ B.Contains x := by
  intro hB
  apply h
  intro i
  exact ⟨le_trans (min_le_left _ _) (hB i).1, le_trans (hB i).2 (le_max_left _ _)⟩

theorem not_contains_hull_right {d : ℕ} {B C : RationalBox d} {x : QPoint d}
    (h : ¬ (hullBox B C).Contains x) : ¬ C.Contains x := by
  intro hC
  apply h
  intro i
  exact ⟨le_trans (min_le_right _ _) (hC i).1, le_trans (hC i).2 (le_max_right _ _)⟩

noncomputable def addC {d : ℕ} (φ ψ : TestFunction d) : ClassicalTest d where
  D α x := dv φ α x + dv ψ α x
  support := hullBox φ.support ψ.support
  vanish α x hx := by
    rw [dv_vanish φ α x (not_contains_hull_left hx), dv_vanish ψ α x (not_contains_hull_right hx)]
    simp
  L α := φ.derivativeLipschitz α + ψ.derivativeLipschitz α
  L_nonneg α := add_nonneg (φ.derivativeLipschitz_nonneg α) (ψ.derivativeLipschitz_nonneg α)
  control α x y δ hδ hxy := by
    have h1 := dv_lip φ α x y δ hδ hxy
    have h2 := dv_lip ψ α x y δ hδ hxy
    calc |dv φ α x + dv ψ α x - (dv φ α y + dv ψ α y)|
        = |(dv φ α x - dv φ α y) + (dv ψ α x - dv ψ α y)| := by ring_nf
      _ ≤ |dv φ α x - dv φ α y| + |dv ψ α x - dv ψ α y| := abs_add_le _ _
      _ ≤ _ := by push_cast at h1 h2 ⊢; linarith
  deriv α i x := hasDerivR_add (dv_deriv φ α i x) (dv_deriv ψ α i x)

/-- A rational bound for the absolute value of a valid name. -/
def ratBound (r : RealCompute) : ℚ := |(r.compute 0).lo| + |(r.compute 0).hi|

theorem ratBound_nonneg (r : RealCompute) : 0 ≤ ratBound r :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem abs_val_le_ratBound {r : RealCompute} (hr : r.Valid) : |val r| ≤ (ratBound r : ℝ) := by
  have h := mem hr 0
  unfold ratBound
  push_cast
  rw [abs_le]
  constructor
  · have := neg_abs_le (((r.compute 0).lo : ℚ) : ℝ)
    have := abs_nonneg (((r.compute 0).hi : ℚ) : ℝ)
    linarith
  · have := le_abs_self (((r.compute 0).hi : ℚ) : ℝ)
    have := abs_nonneg (((r.compute 0).lo : ℚ) : ℝ)
    linarith

noncomputable def scaleC {d : ℕ} (r : RealCompute) (hr : r.Valid) (φ : TestFunction d) :
    ClassicalTest d where
  D α x := val r * dv φ α x
  support := φ.support
  vanish α x hx := by rw [dv_vanish φ α x hx]; simp
  L α := ratBound r * φ.derivativeLipschitz α
  L_nonneg α := mul_nonneg (ratBound_nonneg r) (φ.derivativeLipschitz_nonneg α)
  control α x y δ hδ hxy := by
    have h1 := dv_lip φ α x y δ hδ hxy
    have h2 := abs_val_le_ratBound hr
    rw [← mul_sub, abs_mul]
    push_cast at h1 ⊢
    rw [mul_assoc]
    exact mul_le_mul h2 h1 (abs_nonneg _)
      (by have := φ.derivativeLipschitz_nonneg α; have : (0:ℝ) ≤ ratBound r := by exact_mod_cast ratBound_nonneg r
          positivity)
  deriv α i x := hasDerivR_const_mul (val r) (dv_deriv φ α i x)

def zeroBox (d : ℕ) : RationalBox d where
  lower _ := 0
  upper _ := 0
  ordered _ := le_rfl

noncomputable def zeroC (d : ℕ) : ClassicalTest d where
  D _ _ := 0
  support := zeroBox d
  vanish _ _ _ := rfl
  L _ := 0
  L_nonneg _ := le_rfl
  control α x y δ hδ hxy := by simp
  deriv α i x := hasDerivR_zero _

noncomputable def space (d : ℕ) : TestFunctionSpace d where
  zero := (zeroC d).toTest
  add φ ψ := (addC φ ψ).toTest
  scale r hr φ := (scaleC r hr φ).toTest
  zero_derivative α x := by
    apply equiv_of_val_eq (name_valid _) (ofRat_valid' 0)
    rw [val_name, val_ofRat]; simp [zeroC]
  add_derivative φ ψ α x := by
    apply equiv_of_val_eq (name_valid _) (add_valid' (φ.derivative_valid α x) (ψ.derivative_valid α x))
    rw [val_name, val_add (φ.derivative_valid α x) (ψ.derivative_valid α x)]
    rfl
  scale_derivative r hr φ α x := by
    apply equiv_of_val_eq (name_valid _) (RealCompute.mul_valid hr (φ.derivative_valid α x))
    rw [val_name, val_mul hr (φ.derivative_valid α x)]
    rfl
  add_zero φ := equivalent_of_dv fun α x => by
    simp [dv_toTest, addC, zeroC]
  zero_add φ := equivalent_of_dv fun α x => by
    simp [dv_toTest, addC, zeroC]
  add_comm φ ψ := equivalent_of_dv fun α x => by
    simp [dv_toTest, addC]; ring
  add_assoc φ ψ χ := equivalent_of_dv fun α x => by
    simp [dv_toTest, addC]; ring
  scale_one φ := equivalent_of_dv fun α x => by
    simp [dv_toTest, scaleC, val_ofRat]
  scale_zero φ := equivalent_of_dv fun α x => by
    simp [dv_toTest, scaleC, zeroC, val_ofRat]
  scale_add_scalar r hr s hs φ := equivalent_of_dv fun α x => by
    simp [dv_toTest, scaleC, addC, val_add hr hs]; ring
  scale_mul_scalar r hr s hs φ := equivalent_of_dv fun α x => by
    simp [dv_toTest, scaleC, val_mul hr hs]; ring
  scale_add_test r hr φ ψ := equivalent_of_dv fun α x => by
    simp [dv_toTest, scaleC, addC]; ring
  add_congr φ φ' ψ ψ' h1 h2 := equivalent_of_dv fun α x => by
    simp [dv_toTest, addC, dv_of_equivalent h1, dv_of_equivalent h2]
  scale_test_congr r hr φ ψ h := equivalent_of_dv fun α x => by
    simp [dv_toTest, scaleC, dv_of_equivalent h]
  scale_scalar_congr r s hr hs φ h := equivalent_of_dv fun α x => by
    simp [dv_toTest, scaleC, val_eq_of_equiv hr hs h]


/-! The counterexample. -/

theorem hasDerivR_of_locConst {F : ℚ → ℝ} {x : ℚ}
    (h : ∃ ρ > 0, ∀ r : ℚ, |(r:ℝ) - x| < ρ → F r = F x) : HasDerivR F x 0 := by
  obtain ⟨ρ, hρ, hF⟩ := h
  intro a b hab ha hb hw
  apply tendsto_const_nhds.congr'
  filter_upwards [hw.eventually (gt_mem_nhds hρ)] with n hn
  have h1 := (hab n).1
  have h2 := (hab n).2.1
  have h3 := (hab n).2.2
  have c2 : ((a n : ℚ) : ℝ) ≤ x := by exact_mod_cast h2
  have c3 : (x : ℝ) ≤ ((b n : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at hn
  rw [hF (b n) (by rw [abs_lt]; constructor <;> linarith),
    hF (a n) (by rw [abs_lt]; constructor <;> linarith)]
  simp

def aa (n : ℕ) : ℚ := (1/2) ^ (n + 1)
def ww (n : ℕ) : ℚ := (1/2) ^ n * (1/2) ^ n / 16

theorem ww_pos (n : ℕ) : 0 < ww n := by unfold ww; positivity
theorem aa_pos (n : ℕ) : 0 < aa n := by unfold aa; positivity

theorem two_ww_le (n : ℕ) : 2 * ww n ≤ aa n := by
  unfold ww aa
  have h1 : (1/2 : ℚ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : (0 : ℚ) ≤ (1/2) ^ n := by positivity
  rw [pow_succ]
  nlinarith

theorem aa_le_half (n : ℕ) : aa n ≤ 1/2 := by
  unfold aa
  rw [pow_succ]
  have h1 : (1/2 : ℚ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem aa_lt {m n : ℕ} (h : m < n) : aa n + 2 * ww n ≤ aa m := by
  have := two_ww_le n
  have h2 : (1/2 : ℚ) ^ (n + 1) ≤ (1/2) ^ (m + 1 + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold aa at *
  rw [pow_succ _ (m + 1)] at h2
  linarith

theorem aa_gt {m n : ℕ} (h : n < m) : aa m + ww m ≤ aa n := by
  have := two_ww_le m
  have := ww_pos m
  have h2 : (1/2 : ℚ) ^ (m + 1) ≤ (1/2) ^ (n + 1 + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold aa at *
  rw [pow_succ _ (n + 1)] at h2
  linarith

noncomputable def psiVal (n : ℕ) (p : ℚ) : ℝ := PathoStair.psi (((p - aa n) / ww n : ℚ) : ℝ)

theorem psiVal_out (n : ℕ) {p : ℚ} (h : p ≤ aa n ∨ aa n + 2 * ww n ≤ p) : psiVal n p = 0 := by
  unfold psiVal
  apply PathoStair.psi_out
  have hw := ww_pos n
  rcases h with h | h
  · left
    have : (p - aa n) / ww n ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
    exact_mod_cast this
  · right
    have : 2 ≤ (p - aa n) / ww n := by rw [le_div_iff₀ hw]; linarith
    exact_mod_cast this

def pt (t : ℚ) : QPoint 1 := fun _ => t

def suppBox (n : ℕ) : RationalBox 1 where
  lower _ := aa n
  upper _ := aa n + 2 * ww n
  ordered _ := by have := ww_pos n; linarith

noncomputable def psiC (n : ℕ) : ClassicalTest 1 where
  D α x := if α 0 = 0 then psiVal n (x 0) else 0
  support := suppBox n
  vanish α x hx := by
    split_ifs
    · apply psiVal_out
      by_contra hc
      push Not at hc
      apply hx
      intro i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact ⟨hc.1.le, hc.2.le⟩
    · rfl
  L α := if α 0 = 0 then 1 / ww n else 0
  L_nonneg α := by split_ifs <;> [exact (one_div_pos.2 (ww_pos n)).le; exact le_rfl]
  control α x y δ hδ hxy := by
    split_ifs
    · unfold psiVal
      refine (PathoStair.psi_abs _ _).trans ?_
      have hw := ww_pos n
      have h0 := hxy 0
      rw [← Rat.cast_sub, ← sub_div, show x 0 - aa n - (y 0 - aa n) = x 0 - y 0 by ring]
      have : |(x 0 - y 0) / ww n| ≤ 1 / ww n * δ := by
        rw [abs_div, abs_of_pos hw, div_le_iff₀ hw, abs_le]
        field_simp
        constructor <;> linarith
      exact_mod_cast this
    · simp
  deriv α i x := by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have hinc : incrementIndex α 0 0 = α 0 + 1 := by simp [incrementIndex]
    have hrep : ∀ r, replaceCoordinate x 0 r 0 = r := fun r => by simp [replaceCoordinate]
    simp only [hinc, hrep, Nat.add_one_ne_zero, if_false]
    split_ifs with h0
    · apply hasDerivR_of_locConst
      obtain ⟨ρ, hρ, hc⟩ := PathoStair.psi_locConst ((x 0 - aa n) / ww n)
      have hw := ww_pos n
      have hw' : (0:ℝ) < ww n := by exact_mod_cast hw
      refine ⟨ρ * ww n, by positivity, fun r hr => ?_⟩
      unfold psiVal
      apply hc
      push_cast
      rw [← sub_div, show (r:ℝ) - aa n - (x 0 - aa n) = r - x 0 by ring, abs_div,
        abs_of_pos hw', div_lt_iff₀ hw']
      exact hr
    · exact hasDerivR_zero _

theorem dv_psi (n : ℕ) (p : ℚ) : dv (psiC n).toTest (zeroIndex 1) (pt p) = psiVal n p := by
  rw [dv_toTest]
  simp [psiC, zeroIndex, pt]

noncomputable def term (n : ℕ) (φ : TestFunction 1) : ℝ :=
  2 ^ n * (dv φ (zeroIndex 1) (pt (aa n + ww n)) - dv φ (zeroIndex 1) (pt (aa n)))

theorem term_bound (n : ℕ) (φ : TestFunction 1) :
    |term n φ| ≤ (φ.derivativeLipschitz (zeroIndex 1) : ℝ) * ((1/16) * (1/2) ^ n) := by
  have hw := ww_pos n
  have h := dv_lip φ (zeroIndex 1) (pt (aa n + ww n)) (pt (aa n)) (ww n) hw.le
    (fun i => by simp only [pt]; constructor <;> linarith)
  unfold term
  rw [abs_mul, abs_of_pos (by positivity)]
  have e : (2:ℝ) ^ n * (ww n : ℝ) = (1/16) * (1/2) ^ n := by
    unfold ww
    push_cast
    have : (2:ℝ) ^ n * (1/2) ^ n = 1 := by rw [← mul_pow]; norm_num
    calc (2:ℝ) ^ n * ((1/2) ^ n * (1/2) ^ n / 16) = ((2:ℝ) ^ n * (1/2) ^ n) * ((1/2) ^ n / 16) := by ring
      _ = _ := by rw [this]; ring
  push_cast at h
  calc (2:ℝ) ^ n * |dv φ (zeroIndex 1) (pt (aa n + ww n)) - dv φ (zeroIndex 1) (pt (aa n))|
      ≤ 2 ^ n * ((φ.derivativeLipschitz (zeroIndex 1) : ℝ) * ww n) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [← e]; ring

theorem term_summable (φ : TestFunction 1) : Summable (fun n => term n φ) := by
  refine Summable.of_norm_bounded (g := fun n => (φ.derivativeLipschitz (zeroIndex 1) : ℝ) * ((1/16) * (1/2) ^ n)) ?_ (fun n => by rw [Real.norm_eq_abs]; exact term_bound n φ)
  exact ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _).mul_left _

theorem dv_zeroT (α : MultiIndex 1) (x : QPoint 1) : dv (space 1).zero α x = 0 := by
  show dv (zeroC 1).toTest α x = 0
  rw [dv_toTest]; rfl

theorem dv_addT (φ ψ : TestFunction 1) (α : MultiIndex 1) (x : QPoint 1) :
    dv ((space 1).add φ ψ) α x = dv φ α x + dv ψ α x := by
  show dv (addC φ ψ).toTest α x = _
  rw [dv_toTest]; rfl

theorem dv_scaleT (r : RealCompute) (hr : r.Valid) (φ : TestFunction 1) (α : MultiIndex 1)
    (x : QPoint 1) : dv ((space 1).scale r hr φ) α x = val r * dv φ α x := by
  show dv (scaleC r hr φ).toTest α x = _
  rw [dv_toTest]; rfl

noncomputable def uAct (j : ℕ) (φ : TestFunction 1) : RealCompute :=
  name (∑ n ∈ Finset.range j, term n φ)

noncomputable def uDist (j : ℕ) : Distribution (space 1) where
  action := uAct j
  action_linear := by
    refine ⟨fun φ => name_valid _, ?_, ?_, ?_, ?_⟩
    · intro φ ψ h
      apply equiv_of_val_eq (name_valid _) (name_valid _)
      simp [uAct, val_name, term, dv_of_equivalent h]
    · apply equiv_of_val_eq (name_valid _) (ofRat_valid' 0)
      simp [uAct, val_name, val_ofRat, term, dv_zeroT]
    · intro φ ψ
      apply equiv_of_val_eq (name_valid _) (add_valid' (name_valid _) (name_valid _))
      rw [val_add (name_valid _) (name_valid _)]
      simp only [uAct, val_name, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      simp only [term, dv_addT]
      ring
    · intro r hr φ
      apply equiv_of_val_eq (name_valid _) (RealCompute.mul_valid hr (name_valid _))
      rw [val_mul hr (name_valid _)]
      simp only [uAct, val_name, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      simp only [term, dv_scaleT]
      ring
  action_continuous := by
    intro B
    refine ⟨0, 2 * ∑ n ∈ Finset.range j, (2:ℚ) ^ n, by positivity, ?_⟩
    intro φ _ b hb hbd
    rw [smallApprox_iff]
    unfold uAct
    rw [val_name]
    have hv : ∀ x, |dv φ (zeroIndex 1) x| ≤ (b : ℝ) := fun x =>
      (smallApprox_iff _ _).1 (hbd (zeroIndex 1) (by simp) x)
    have ht : ∀ n, |term n φ| ≤ 2 ^ n * (2 * b) := by
      intro n
      unfold term
      rw [abs_mul, abs_of_pos (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 := hv (pt (aa n + ww n))
      have h2 := hv (pt (aa n))
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    calc |∑ n ∈ Finset.range j, term n φ| ≤ ∑ n ∈ Finset.range j, |term n φ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range j, 2 ^ n * (2 * (b:ℝ)) := Finset.sum_le_sum (fun n _ => ht n)
      _ = _ := by push_cast; rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro n _; ring

noncomputable def limAct (φ : TestFunction 1) : RealCompute := name (∑' n, term n φ)

theorem converges : Distribution.ConvergesOnTests uDist limAct := by
  intro φ
  apply tendsto_of_val (name_valid _) (fun j => name_valid _)
  simp only [uDist, uAct, limAct, val_name]
  exact (term_summable φ).hasSum.tendsto_sum_nat

def box01 : RationalBox 1 where
  lower _ := 0
  upper _ := 1
  ordered _ := by norm_num

theorem term_psi_self (n : ℕ) : term n (psiC n).toTest = 2 ^ n * PathoStair.psi 1 := by
  unfold term
  rw [dv_psi, dv_psi, psiVal_out n (Or.inl le_rfl)]
  have hw := ww_pos n
  unfold psiVal
  rw [show (aa n + ww n - aa n) / ww n = 1 by field_simp; ring]
  simp

theorem term_psi_other {m n : ℕ} (h : m ≠ n) : term m (psiC n).toTest = 0 := by
  unfold term
  have hw := ww_pos m
  rcases lt_or_gt_of_ne h with hmn | hmn
  · have := aa_lt hmn
    rw [dv_psi, dv_psi, psiVal_out n (Or.inr (by linarith)), psiVal_out n (Or.inr (by linarith))]
    simp
  · have := aa_gt hmn
    rw [dv_psi, dv_psi, psiVal_out n (Or.inl (by linarith)), psiVal_out n (Or.inl (by linarith))]
    simp

theorem not_target : ¬ DistributionConvergenceTarget := by
  intro H
  obtain ⟨T, hT⟩ := H 1 (space 1) uDist limAct converges
  obtain ⟨k, C, hC, hb⟩ := T.action_continuous box01
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * (C:ℝ)) (by norm_num : (1:ℝ) < 2)
  have hsupp : (psiC n).toTest.SupportedInBox box01 := by
    intro x hx
    apply equiv_of_val_eq ((psiC n).toTest.value_valid x) (ofRat_valid' 0)
    rw [val_ofRat]
    show dv (psiC n).toTest (zeroIndex 1) x = _
    rw [dv_toTest, (psiC n).vanish _ x ?_]
    · simp
    intro hc
    apply hx
    intro i
    have h1 := hc i
    have := aa_pos n
    have := two_ww_le n
    have := aa_le_half n
    change aa n ≤ x i ∧ x i ≤ aa n + 2 * ww n at h1
    show 0 ≤ x i ∧ x i ≤ 1
    constructor <;> linarith [h1.1, h1.2]
  have hbd : (psiC n).toTest.DerivativesBoundedBy k 1 := by
    intro α _ x
    rw [smallApprox_iff]
    show |dv (psiC n).toTest α x| ≤ _
    rw [dv_toTest]
    simp only [psiC]
    split_ifs
    · unfold psiVal
      rw [abs_of_nonneg (PathoStair.psi_nonneg _)]
      exact_mod_cast PathoStair.psi_le_one _
    · simp
  have hsmall := (smallApprox_iff _ _).1 (hb (psiC n).toTest hsupp 1 (by norm_num) hbd)
  rw [val_eq_of_equiv (T.action_valid _) (name_valid _) (hT _)] at hsmall
  simp only [limAct, val_name] at hsmall
  rw [tsum_eq_single n (fun m hm => term_psi_other hm), term_psi_self] at hsmall
  have h1 := PathoStair.psi_one
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  rw [abs_of_nonneg (by positivity)] at hsmall
  push_cast at hsmall
  nlinarith

end CBridge

end ComputableDistributions

theorem solution : ¬ ComputableDistributions.DistributionConvergenceTarget :=
  ComputableDistributions.CBridge.not_target
