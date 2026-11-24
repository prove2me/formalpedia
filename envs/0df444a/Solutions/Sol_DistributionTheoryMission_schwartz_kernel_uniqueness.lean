-- Prove2me | solution 1 for DistributionTheoryMission.schwartz_kernel_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T17:34:30.421361+00:00
-- url     : https://prove2.me/submissions/9dd2d1a2-7223-4da0-a7f7-3fa6cac85eb3

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_KernelTargets
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

/-! ## A Lipschitz staircase, locally constant at every rational -/

noncomputable def stp (x : ℝ) : ℝ := PathoStair.h (min x 1) / PathoStair.h 1

theorem h1_pos : 0 < PathoStair.h 1 := by have := PathoStair.h_one; linarith

theorem stp_mono {x y : ℝ} (hxy : x ≤ y) : stp x ≤ stp y :=
  div_le_div_of_nonneg_right (PathoStair.h_mono (min_le_min_right 1 hxy)) h1_pos.le

theorem stp_zero {x : ℝ} (hx : x ≤ 0) : stp x = 0 := by
  unfold stp; rw [PathoStair.h_nonpos (le_trans (min_le_left _ _) hx)]; simp

theorem stp_one {x : ℝ} (hx : 1 ≤ x) : stp x = 1 := by
  unfold stp; rw [min_eq_right hx]; exact div_self h1_pos.ne'

theorem stp_nonneg (x : ℝ) : 0 ≤ stp x := div_nonneg (PathoStair.h_nonneg _) h1_pos.le

theorem stp_le_one (x : ℝ) : stp x ≤ 1 := by
  unfold stp; rw [div_le_one h1_pos]; exact PathoStair.h_mono (min_le_right _ _)

theorem stp_lip (x y : ℝ) : |stp x - stp y| ≤ 2 * |x - y| := by
  unfold stp
  rw [← sub_div, abs_div, abs_of_pos h1_pos, div_le_iff₀ h1_pos]
  have h3 := PathoStair.h_one
  have h4 := PathoStair.h_abs (min x 1) (min y 1)
  have hm : |min x 1 - min y 1| ≤ |x - y| :=
    (abs_min_sub_min_le_max x 1 y 1).trans (by simp)
  have := mul_nonneg (abs_nonneg (x - y)) (by linarith : (0:ℝ) ≤ 2 * PathoStair.h 1 - 1)
  nlinarith

theorem stp_locConst (q : ℚ) : ∃ ρ > 0, ∀ y : ℝ, |y - q| < ρ → stp y = stp q := by
  by_cases hq : (q : ℝ) ≤ 1
  · obtain ⟨ρ, hρ, hh⟩ := PathoStair.h_locConst q
    refine ⟨ρ, hρ, fun y hy => ?_⟩
    unfold stp
    rw [min_eq_left hq]
    by_cases hy1 : y ≤ 1
    · rw [min_eq_left hy1, hh y hy]
    · rw [min_eq_right (le_of_not_ge hy1)]
      rw [hh 1 (by rw [abs_lt] at hy ⊢; constructor <;> linarith)]
  · push_neg at hq
    refine ⟨q - 1, by linarith, fun y hy => ?_⟩
    rw [abs_lt] at hy
    rw [stp_one (by linarith), stp_one hq.le]

/-! ## Staircase hats -/

noncomputable def hat (c h : ℚ) (t : ℝ) : ℝ := stp ((t - c) / h + 1) - stp ((t - c) / h)

theorem hat_nonneg (c h : ℚ) (t : ℝ) : 0 ≤ hat c h t := by
  unfold hat; have := stp_mono (show (t - c) / h ≤ (t - c) / h + 1 by linarith); linarith

theorem hat_le_one (c h : ℚ) (t : ℝ) : hat c h t ≤ 1 := by
  unfold hat; have := stp_le_one ((t - c) / h + 1); have := stp_nonneg ((t - c) / h); linarith

theorem hat_out {c h : ℚ} (hh : (0:ℝ) < h) {t : ℝ} (ht : t ≤ c - h ∨ c + h ≤ t) :
    hat c h t = 0 := by
  unfold hat
  rcases ht with ht | ht
  · have e : (t - c) / h ≤ -1 := by rw [div_le_iff₀ hh]; linarith
    rw [stp_zero (by linarith), stp_zero (by linarith)]; simp
  · have e : 1 ≤ (t - c) / h := by rw [le_div_iff₀ hh]; linarith
    rw [stp_one (by linarith), stp_one e]; simp

theorem hat_ne_zero {c h : ℚ} (hh : (0:ℝ) < h) {t : ℝ} (ht : hat c h t ≠ 0) :
    (c:ℝ) - h < t ∧ t < c + h := by
  by_contra hc
  rw [not_and_or] at hc
  apply ht
  apply hat_out hh
  rcases hc with hc | hc
  · left; linarith [not_lt.1 hc]
  · right; linarith [not_lt.1 hc]

theorem hat_lip {c h : ℚ} (hh : (0:ℝ) < h) (t u : ℝ) :
    |hat c h t - hat c h u| ≤ 4 / h * |t - u| := by
  unfold hat
  have e1 := stp_lip ((t - c) / h + 1) ((u - c) / h + 1)
  have e2 := stp_lip ((t - c) / h) ((u - c) / h)
  have e3 : (t - c) / h + 1 - ((u - c) / h + 1) = (t - u) / h := by ring
  have e4 : (t - c) / h - (u - c) / h = (t - u) / h := by ring
  rw [e3] at e1; rw [e4] at e2
  rw [abs_div, abs_of_pos hh] at e1 e2
  have : |stp ((t - c) / h + 1) - stp ((t - c) / h) - (stp ((u - c) / h + 1) - stp ((u - c) / h))|
      ≤ |stp ((t - c) / h + 1) - stp ((u - c) / h + 1)| + |stp ((t - c) / h) - stp ((u - c) / h)| := by
    rw [show stp ((t - c) / h + 1) - stp ((t - c) / h) - (stp ((u - c) / h + 1) - stp ((u - c) / h))
      = (stp ((t - c) / h + 1) - stp ((u - c) / h + 1)) - (stp ((t - c) / h) - stp ((u - c) / h)) by ring]
    exact abs_sub _ _
  have e5 : 4 / (h:ℝ) * |t - u| = 2 * (|t - u| / h) + 2 * (|t - u| / h) := by ring
  rw [e5]; linarith

theorem hat_locConst (c h : ℚ) (hh : (0:ℝ) < h) (q : ℚ) :
    ∃ ρ > 0, ∀ y : ℝ, |y - q| < ρ → hat c h y = hat c h q := by
  obtain ⟨ρ1, hρ1, h1⟩ := stp_locConst ((q - c) / h + 1)
  obtain ⟨ρ2, hρ2, h2⟩ := stp_locConst ((q - c) / h)
  refine ⟨h * min ρ1 ρ2, mul_pos hh (lt_min hρ1 hρ2), fun y hy => ?_⟩
  have hy' : |y - q| / h < min ρ1 ρ2 := by rw [div_lt_iff₀ hh]; linarith
  have k1 : |((y - c) / h + 1) - (((q - c) / h + 1 : ℚ) : ℝ)| = |y - q| / h := by
    push_cast; rw [show (y - c) / h + 1 - ((q - c) / h + 1) = (y - q) / h by ring, abs_div,
      abs_of_pos hh]
  have k2 : |((y - c) / h) - (((q - c) / h : ℚ) : ℝ)| = |y - q| / h := by
    push_cast; rw [show (y - c) / h - (q - c) / h = (y - q) / h by ring, abs_div, abs_of_pos hh]
  unfold hat
  rw [h1 ((y - c) / h + 1) (by rw [k1]; exact lt_of_lt_of_le hy' (min_le_left _ _)),
    h2 ((y - c) / h) (by rw [k2]; exact lt_of_lt_of_le hy' (min_le_right _ _))]
  congr 2 <;> push_cast <;> ring

theorem hat_sum (a h : ℚ) (hh : (0:ℝ) < h) (N : ℕ) (t : ℝ) :
    ∑ j ∈ Finset.range N, hat (a + j * h) h t =
      stp ((t - a) / h + 1) - stp ((t - a) / h + 1 - N) := by
  have e : ∀ j : ℕ, hat (a + j * h) h t =
      stp ((t - a) / h + 1 - j) - stp ((t - a) / h + 1 - (j + 1 : ℕ)) := by
    intro j
    unfold hat
    have e1 : (t - ((a + j * h : ℚ) : ℝ)) / h + 1 = (t - a) / h + 1 - j := by
      push_cast; field_simp; ring
    have e2 : (t - ((a + j * h : ℚ) : ℝ)) / h = (t - a) / h + 1 - (j + 1 : ℕ) := by
      push_cast; field_simp; ring
    rw [e1, e2]
  simp_rw [e]
  rw [Finset.sum_range_sub' (fun j : ℕ => stp ((t - a) / h + 1 - j)) N]
  simp

/-! ## Clamped monomials -/

noncomputable def cl (c h : ℚ) (t : ℝ) : ℝ := max ((c:ℝ) - h) (min t (c + h))

theorem cl_near {c h : ℚ} (hh : (0:ℝ) ≤ h) (t : ℝ) : |cl c h t - c| ≤ h := by
  unfold cl; rw [abs_le]; constructor
  · linarith [le_max_left ((c:ℝ) - h) (min t (c + h))]
  · have := min_le_right t ((c:ℝ) + h)
    rcases le_total ((c:ℝ) - h) (min t (c + h)) with h' | h'
    · rw [max_eq_right h']; linarith
    · rw [max_eq_left h']; linarith

theorem cl_lip (c h : ℚ) (t u : ℝ) : |cl c h t - cl c h u| ≤ |t - u| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  refine max_le (abs_nonneg _) ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  simp

theorem cl_eq {c h : ℚ} {t : ℝ} (h1 : (c:ℝ) - h < t) (h2 : t < c + h) : cl c h t = t := by
  unfold cl; rw [min_eq_left h2.le, max_eq_right h1.le]

theorem pow_lip (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ∀ n : ℕ, |x ^ n - y ^ n| ≤ n * |x - y|
  | 0 => by simp
  | n + 1 => by
    have ih := pow_lip x y hx hy n
    have hyn : |y ^ n| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hy
    calc |x ^ (n + 1) - y ^ (n + 1)| = |x * (x ^ n - y ^ n) + (x - y) * y ^ n| := by ring_nf
      _ ≤ |x * (x ^ n - y ^ n)| + |(x - y) * y ^ n| := abs_add_le _ _
      _ = |x| * |x ^ n - y ^ n| + |x - y| * |y ^ n| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (n * |x - y|) + |x - y| * 1 := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * |x - y| := by push_cast; ring

theorem descF_nonneg (n k : ℕ) : 0 ≤ (n.descFactorial k : ℝ) / n.factorial := by positivity

theorem descF_le (n k : ℕ) : (n.descFactorial k : ℝ) / n.factorial ≤ 1 := by
  rw [div_le_one (by exact_mod_cast Nat.factorial_pos n)]
  by_cases hk : k ≤ n
  · have e := Nat.factorial_mul_descFactorial hk
    have : n.descFactorial k ≤ n.factorial := by
      rw [← e]; exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    exact_mod_cast this
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; simp

/-! ## Classical derivative lemmas -/

theorem hasDerivR_congr_near {F G : ℚ → ℝ} {x : ℚ} {D : ℝ} (hG : HasDerivR G x D)
    (h : ∃ ρ > 0, ∀ r : ℚ, |(r:ℝ) - x| < ρ → F r = G r) : HasDerivR F x D := by
  obtain ⟨ρ, hρ, hF⟩ := h
  intro a b hab ha hb hw
  apply (hG a b hab ha hb hw).congr'
  filter_upwards [hw.eventually (gt_mem_nhds hρ)] with n hn
  have h1 := (hab n).1
  have c2 : ((a n : ℚ) : ℝ) ≤ x := by exact_mod_cast (hab n).2.1
  have c3 : (x : ℝ) ≤ ((b n : ℚ) : ℝ) := by exact_mod_cast (hab n).2.2
  push_cast at hn
  rw [hF (b n) (by rw [abs_lt]; constructor <;> linarith),
    hF (a n) (by rw [abs_lt]; constructor <;> linarith)]

theorem hasDerivR_of_deriv (F F' : ℝ → ℝ) (hF : ∀ x, HasDerivAt F (F' x) x)
    (hc : Continuous F') (q : ℚ) : HasDerivR (fun r : ℚ => F r) q (F' q) := by
  intro a b hab ha hb hw
  have hlt : ∀ n, ((a n : ℚ) : ℝ) < b n := fun n => by exact_mod_cast (hab n).1
  have hex : ∀ n, ∃ ξ ∈ Set.Ioo ((a n : ℚ) : ℝ) (b n),
      F' ξ = (F (b n) - F (a n)) / ((b n : ℝ) - a n) := fun n =>
    exists_hasDerivAt_eq_slope F F' (hlt n) (fun y _ => (hF y).continuousAt.continuousWithinAt)
      (fun y _ => hF y)
  choose ξ hξ hξe using hex
  have hw' : Tendsto (fun n => ((b n : ℚ) : ℝ) - a n) atTop (𝓝 0) := by
    refine hw.congr (fun n => ?_); push_cast; ring
  have hξt : Tendsto ξ atTop (𝓝 (q : ℝ)) := by
    have l1 : Tendsto (fun n => (q:ℝ) - (((b n : ℚ) : ℝ) - a n)) atTop (𝓝 q) := by
      simpa using (tendsto_const_nhds (x := (q:ℝ))).sub hw'
    have l2 : Tendsto (fun n => (q:ℝ) + (((b n : ℚ) : ℝ) - a n)) atTop (𝓝 q) := by
      simpa using (tendsto_const_nhds (x := (q:ℝ))).add hw'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le l1 l2 (fun n => ?_) (fun n => ?_)
    · have := (hξ n).1; have : ((a n : ℚ) : ℝ) ≤ q := by exact_mod_cast (hab n).2.1
      have : (q : ℝ) ≤ b n := by exact_mod_cast (hab n).2.2
      simp only; linarith
    · have := (hξ n).2; have : ((a n : ℚ) : ℝ) ≤ q := by exact_mod_cast (hab n).2.1
      simp only; linarith
  refine ((hc.tendsto _).comp hξt).congr (fun n => ?_)
  simp only [Function.comp]
  rw [hξe n]; push_cast; rfl

/-! ## One-dimensional profiles and their products -/

structure Prof where
  f : ℕ → ℝ → ℝ
  lo : ℚ
  hi : ℚ
  hlo : lo ≤ hi
  vanish : ∀ j (t : ℚ), ¬ (lo ≤ t ∧ t ≤ hi) → f j t = 0
  M : ℕ → ℝ
  bound : ∀ j (t : ℚ), |f j t| ≤ M j
  Lc : ℕ → ℝ
  Lc_nonneg : ∀ j, 0 ≤ Lc j
  lip : ∀ j (t u : ℚ), |f j t - f j u| ≤ Lc j * |(t:ℝ) - u|
  deriv : ∀ j (q : ℚ), HasDerivR (fun r : ℚ => f j r) q (f (j + 1) q)

theorem Prof.M_nonneg (P : Prof) (j : ℕ) : 0 ≤ P.M j := (abs_nonneg _).trans (P.bound j 0)

theorem prod_sub_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b K : ι → ℝ)
    (hK : ∀ i, 1 ≤ K i) (ha : ∀ i, |a i| ≤ K i) (hb : ∀ i, |b i| ≤ K i) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ (∑ i ∈ s, |a i - b i|) * ∏ i ∈ s, K i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    have hbs : |∏ j ∈ s, b j| ≤ ∏ j ∈ s, K j := by
      rw [Finset.abs_prod]; exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hb j)
    have hK0 : 0 ≤ ∏ j ∈ s, K j := Finset.prod_nonneg (fun j _ => by linarith [hK j])
    have hS0 : 0 ≤ ∑ j ∈ s, |a j - b j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    calc |a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j|
        = |a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j| := by ring_nf
      _ ≤ |a i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| + |a i - b i| * |∏ j ∈ s, b j| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ K i * ((∑ j ∈ s, |a j - b j|) * ∏ j ∈ s, K j) + |a i - b i| * (K i * ∏ j ∈ s, K j) := by
          have t1 : |a i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| ≤
              K i * ((∑ j ∈ s, |a j - b j|) * ∏ j ∈ s, K j) :=
            mul_le_mul (ha i) ih (abs_nonneg _) (by linarith [hK i])
          have t2 : |a i - b i| * |∏ j ∈ s, b j| ≤ |a i - b i| * (K i * ∏ j ∈ s, K j) :=
            mul_le_mul_of_nonneg_left (hbs.trans (le_mul_of_one_le_left hK0 (hK i))) (abs_nonneg _)
          linarith
      _ = (|a i - b i| + ∑ j ∈ s, |a j - b j|) * (K i * ∏ j ∈ s, K j) := by ring

noncomputable def prodC {d : ℕ} (P : Fin d → Prof) : ClassicalTest d where
  D α x := ∏ i, (P i).f (α i) ((x i : ℚ) : ℝ)
  support := ⟨fun i => (P i).lo, fun i => (P i).hi, fun i => (P i).hlo⟩
  vanish α x hx := by
    simp only [RationalBox.Contains, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((P i).vanish _ _ hi)
  L α := ((⌈(∑ i, (P i).Lc (α i)) * ∏ i, (1 + (P i).M (α i))⌉₊ : ℕ) : ℚ)
  L_nonneg α := Nat.cast_nonneg _
  control α x y δ hδ hxy := by
    have hK : ∀ i, 1 ≤ 1 + (P i).M (α i) := fun i => by linarith [(P i).M_nonneg (α i)]
    have h1 := prod_sub_le Finset.univ (fun i => (P i).f (α i) ((x i : ℚ) : ℝ))
      (fun i => (P i).f (α i) ((y i : ℚ) : ℝ)) (fun i => 1 + (P i).M (α i)) hK
      (fun i => ((P i).bound _ _).trans (by linarith)) (fun i => ((P i).bound _ _).trans (by linarith))
    have h2 : ∑ i, |(P i).f (α i) ((x i : ℚ) : ℝ) - (P i).f (α i) ((y i : ℚ) : ℝ)| ≤
        (∑ i, (P i).Lc (α i)) * δ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i _ => ((P i).lip _ _ _).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ ((P i).Lc_nonneg _)
      rw [abs_le]; have := hxy i
      constructor
      · have : (x i : ℝ) ≥ y i - δ := by exact_mod_cast (by linarith [this.2] : (x i) ≥ y i - δ)
        linarith
      · have : (x i : ℝ) ≤ y i + δ := by exact_mod_cast this.1
        linarith
    have hK0 : 0 ≤ ∏ i, (1 + (P i).M (α i)) := Finset.prod_nonneg (fun i _ => by linarith [hK i])
    have hc := Nat.le_ceil ((∑ i, (P i).Lc (α i)) * ∏ i, (1 + (P i).M (α i)))
    have hδ' : (0:ℝ) ≤ δ := by exact_mod_cast hδ
    push_cast
    calc _ ≤ _ := h1
      _ ≤ (∑ i, (P i).Lc (α i)) * δ * ∏ i, (1 + (P i).M (α i)) := mul_le_mul_of_nonneg_right h2 hK0
      _ = ((∑ i, (P i).Lc (α i)) * ∏ i, (1 + (P i).M (α i))) * δ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hδ'
  deriv α i x := by
    have hfun : (fun r : ℚ => ∏ j, (P j).f (α j) (((replaceCoordinate x i r) j : ℚ) : ℝ)) =
        fun r : ℚ => (∏ j ∈ Finset.univ.erase i, (P j).f (α j) ((x j : ℚ) : ℝ)) *
          (P i).f (α i) (r : ℝ) := by
      funext r
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm]
      congr 1
      · apply Finset.prod_congr rfl; intro j hj
        rw [replaceCoordinate, if_neg (Finset.ne_of_mem_erase hj)]
      · simp [replaceCoordinate]
    have hval : ∏ j, (P j).f (incrementIndex α i j) ((x j : ℚ) : ℝ) =
        (∏ j ∈ Finset.univ.erase i, (P j).f (α j) ((x j : ℚ) : ℝ)) *
          (P i).f (α i + 1) ((x i : ℚ) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm]
      congr 1
      · apply Finset.prod_congr rfl; intro j hj
        rw [incrementIndex, if_neg (Finset.ne_of_mem_erase hj), Nat.add_zero]
      · simp [incrementIndex]
    change HasDerivR (fun r : ℚ => ∏ j, (P j).f (α j) (((replaceCoordinate x i r) j : ℚ) : ℝ))
      (x i) (∏ j, (P j).f (incrementIndex α i j) ((x j : ℚ) : ℝ))
    rw [hfun, hval]
    exact hasDerivR_const_mul _ ((P i).deriv (α i) (x i))

theorem dv_prodC {d : ℕ} (P : Fin d → Prof) (α : MultiIndex d) (x : QPoint d) :
    dv (prodC P).toTest α x = ∏ i, (P i).f (α i) ((x i : ℚ) : ℝ) := dv_toTest _ _ _

theorem tensor_prodC {m n : ℕ} (P : Fin (m + n) → Prof) :
    IsTensorTest (prodC (fun i => P (Fin.castAdd n i))).toTest
      (prodC (fun j => P (Fin.natAdd m j))).toTest (prodC P).toTest := by
  intro α z
  apply equiv_of_val_eq ((prodC P).toTest.derivative_valid α z)
    (RealCompute.mul_valid ((prodC _).toTest.derivative_valid _ _)
      ((prodC _).toTest.derivative_valid _ _))
  rw [val_mul ((prodC _).toTest.derivative_valid _ _) ((prodC _).toTest.derivative_valid _ _)]
  change dv (prodC P).toTest α z = dv (prodC _).toTest _ _ * dv (prodC _).toTest _ _
  rw [dv_prodC, dv_prodC, dv_prodC]
  exact Fin.prod_univ_add _

/-! ## Uniqueness of kernels -/

theorem dv_Zzero {d : ℕ} (Z : TestFunctionSpace d) (α : MultiIndex d) (x : QPoint d) :
    dv Z.zero α x = 0 := by
  have := val_eq_of_equiv (Z.zero.derivative_valid α x) (ofRat_valid' 0) (Z.zero_derivative α x)
  rw [val_ofRat] at this
  simpa [dv] using this

theorem dv_Zadd {d : ℕ} (Z : TestFunctionSpace d) (φ ψ : TestFunction d) (α : MultiIndex d)
    (x : QPoint d) : dv (Z.add φ ψ) α x = dv φ α x + dv ψ α x := by
  have := val_eq_of_equiv ((Z.add φ ψ).derivative_valid α x)
    (add_valid' (φ.derivative_valid α x) (ψ.derivative_valid α x)) (Z.add_derivative φ ψ α x)
  rw [val_add (φ.derivative_valid α x) (ψ.derivative_valid α x)] at this
  exact this

theorem dv_Zscale {d : ℕ} (Z : TestFunctionSpace d) (r : RealCompute) (hr : r.Valid)
    (φ : TestFunction d) (α : MultiIndex d) (x : QPoint d) :
    dv (Z.scale r hr φ) α x = val r * dv φ α x := by
  have := val_eq_of_equiv ((Z.scale r hr φ).derivative_valid α x)
    (RealCompute.mul_valid hr (φ.derivative_valid α x)) (Z.scale_derivative r hr φ α x)
  rw [val_mul hr (φ.derivative_valid α x)] at this
  exact this

/-- Finite real-linear combinations of separated tests, inside the space `Z`. -/
inductive TensorSpan {m n : Nat} (Z : TestFunctionSpace (m + n)) :
    TestFunction (m + n) → Prop
  | zero : TensorSpan Z Z.zero
  | tensor (φ : TestFunction m) (ψ : TestFunction n) (θ : TestFunction (m + n)) :
      IsTensorTest φ ψ θ → TensorSpan Z θ
  | add {a b} : TensorSpan Z a → TensorSpan Z b → TensorSpan Z (Z.add a b)
  | scale (r : RealCompute) (hr : r.Valid) {a} : TensorSpan Z a → TensorSpan Z (Z.scale r hr a)

theorem agree_on_span {m n : Nat} {Z : TestFunctionSpace (m + n)} (K L : Distribution Z)
    (hK : ∀ φ ψ θ, IsTensorTest φ ψ θ → val (K.action θ) = val (L.action θ))
    {S : TestFunction (m + n)} (hS : TensorSpan Z S) : val (K.action S) = val (L.action S) := by
  induction hS with
  | zero =>
    rw [val_eq_of_equiv (K.action_valid _) (ofRat_valid' 0) K.action_linear.map_zero,
      val_eq_of_equiv (L.action_valid _) (ofRat_valid' 0) L.action_linear.map_zero]
  | tensor φ ψ θ h => exact hK φ ψ θ h
  | add _ _ iha ihb =>
    rw [val_eq_of_equiv (K.action_valid _) (add_valid' (K.action_valid _) (K.action_valid _))
        (K.action_linear.map_add _ _), val_add (K.action_valid _) (K.action_valid _),
      val_eq_of_equiv (L.action_valid _) (add_valid' (L.action_valid _) (L.action_valid _))
        (L.action_linear.map_add _ _), val_add (L.action_valid _) (L.action_valid _), iha, ihb]
  | scale r hr _ ih =>
    rw [val_eq_of_equiv (K.action_valid _) (RealCompute.mul_valid hr (K.action_valid _))
        (K.action_linear.map_scale _ _ _), val_mul hr (K.action_valid _),
      val_eq_of_equiv (L.action_valid _) (RealCompute.mul_valid hr (L.action_valid _))
        (L.action_linear.map_scale _ _ _), val_mul hr (L.action_valid _), ih]

theorem val_action_sub {d : ℕ} {Z : TestFunctionSpace d} (K : Distribution Z)
    (θ S : TestFunction d) (r : RealCompute) (hr : r.Valid) (h1 : val r = -1) :
    val (K.action (Z.add θ (Z.scale r hr S))) =
      val (K.action θ) - val (K.action S) := by
  rw [val_eq_of_equiv (K.action_valid _) (add_valid' (K.action_valid _) (K.action_valid _))
      (K.action_linear.map_add _ _), val_add (K.action_valid _) (K.action_valid _),
    val_eq_of_equiv (K.action_valid _) (RealCompute.mul_valid hr (K.action_valid _))
      (K.action_linear.map_scale _ _ _), val_mul hr (K.action_valid _), h1]
  ring

theorem dv_sub_test {d : ℕ} (Z : TestFunctionSpace d) (θ S : TestFunction d) (α : MultiIndex d)
    (x : QPoint d) (r : RealCompute) (hr : r.Valid) (h1 : val r = -1) :
    dv (Z.add θ (Z.scale r hr S)) α x = dv θ α x - dv S α x := by
  rw [dv_Zadd, dv_Zscale, h1]; ring

theorem index_le_order : ∀ {d : ℕ} (α : MultiIndex d) (i : Fin d), α i ≤ multiIndexOrder α
  | 0, _, i => i.elim0
  | d + 1, α, i => by
    show α i ≤ multiIndexOrder (fun i : Fin d => α i.castSucc) + α (Fin.last d)
    induction i using Fin.lastCases with
    | last => omega
    | cast j =>
      have := index_le_order (fun i : Fin d => α i.castSucc) j
      simpa using this.trans (Nat.le_add_right _ _)

theorem eq_of_close {a b : ℝ} (h : ∀ ε : ℚ, 0 < ε → |a - b| ≤ ε) : a = b := by
  by_contra hne
  have hpos : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn hpos
  have := h q (by exact_mod_cast hq0)
  linarith


/-! ## Staircase-cut monomials -/

noncomputable def mono (c h : ℚ) (hh : (0:ℝ) < h) (hh1 : (h:ℝ) ≤ 1) (b : ℕ) : Prof where
  f j t := hat c h t * ((b.descFactorial j : ℝ) / b.factorial) * (cl c h t - c) ^ (b - j)
  lo := c - h
  hi := c + h
  hlo := by have : (0:ℚ) < h := by exact_mod_cast hh
            linarith
  vanish j t ht := by
    rw [hat_out hh, zero_mul, zero_mul]
    rw [not_and_or] at ht
    rcases ht with ht | ht
    · left; have : (t:ℚ) ≤ c - h := le_of_lt (not_le.1 ht)
      exact_mod_cast this
    · right; have : c + h ≤ (t:ℚ) := le_of_lt (not_le.1 ht)
      exact_mod_cast this
  M _ := 1
  bound j t := by
    rw [abs_mul, abs_mul, abs_pow]
    have e1 := hat_le_one c h t; have e0 := hat_nonneg c h t
    have e2 := descF_le b j; have e3 := descF_nonneg b j
    have e4 : |cl c h t - c| ^ (b - j) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) ((cl_near hh.le t).trans hh1)
    rw [abs_of_nonneg e0, abs_of_nonneg e3]
    have e5 : 0 ≤ |cl c h t - c| ^ (b - j) := by positivity
    calc hat c h t * ((b.descFactorial j : ℝ) / b.factorial) * |cl c h t - c| ^ (b - j)
        ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  Lc _ := 4 / h + b
  Lc_nonneg _ := by positivity
  lip j t u := by
    set κ : ℝ := (b.descFactorial j : ℝ) / b.factorial
    have hκ0 := descF_nonneg b j; have hκ1 := descF_le b j
    set P : ℝ → ℝ := fun x => (cl c h x - c) ^ (b - j)
    have hP1 : ∀ x, |P x| ≤ 1 := fun x => by
      simp only [P]; rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ((cl_near hh.le x).trans hh1)
    have hPl : |P t - P u| ≤ b * |(t:ℝ) - u| := by
      have := pow_lip (cl c h t - c) (cl c h u - c) ((cl_near hh.le t).trans hh1)
        ((cl_near hh.le u).trans hh1) (b - j)
      rw [show cl c h t - c - (cl c h u - c) = cl c h t - cl c h u by ring] at this
      refine this.trans ?_
      have hb : ((b - j : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b j
      exact mul_le_mul hb (cl_lip c h t u) (abs_nonneg _) (Nat.cast_nonneg _)
    have hA := hat_lip (c := c) hh t u
    have hA1 := hat_le_one c h u; have hA0 := hat_nonneg c h u
    have eq : hat c h t * κ * P t - hat c h u * κ * P u =
        κ * ((hat c h t - hat c h u) * P t + hat c h u * (P t - P u)) := by ring
    show |hat c h t * κ * P t - hat c h u * κ * P u| ≤ (4 / h + b) * |(t:ℝ) - u|
    rw [eq, abs_mul, abs_of_nonneg hκ0]
    have s1 : |(hat c h t - hat c h u) * P t + hat c h u * (P t - P u)| ≤
        4 / h * |(t:ℝ) - u| + b * |(t:ℝ) - u| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hA0]
      have := mul_le_mul hA (hP1 t) (abs_nonneg _) (by positivity)
      have := mul_le_mul hA1 hPl (abs_nonneg _) zero_le_one
      linarith
    have s2 : 0 ≤ |(hat c h t - hat c h u) * P t + hat c h u * (P t - P u)| := abs_nonneg _
    calc κ * |(hat c h t - hat c h u) * P t + hat c h u * (P t - P u)|
        ≤ 1 * |(hat c h t - hat c h u) * P t + hat c h u * (P t - P u)| :=
          mul_le_mul_of_nonneg_right hκ1 s2
      _ ≤ _ := by rw [one_mul]; linarith
  deriv j q := by
    obtain ⟨ρ, hρ, hc⟩ := hat_locConst c h hh q
    by_cases hq : hat c h q = 0
    · have e : hat c h q * ((b.descFactorial (j + 1) : ℝ) / b.factorial) *
          (cl c h q - c) ^ (b - (j + 1)) = 0 := by rw [hq]; ring
      rw [e]
      exact hasDerivR_congr_near (hasDerivR_zero q)
        ⟨ρ, hρ, fun r hr => by rw [hc r hr, hq]; ring⟩
    · obtain ⟨hq1, hq2⟩ := hat_ne_zero hh hq
      set κ : ℝ := (b.descFactorial j : ℝ) / b.factorial
      have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => hat c h q * κ * (y - c) ^ (b - j))
          (hat c h q * κ * (((b - j : ℕ) : ℝ) * (x - c) ^ (b - j - 1))) x := by
        intro x
        have := (((hasDerivAt_id x).sub_const (c:ℝ)).pow (b - j)).const_mul (hat c h q * κ)
        simpa using this
      have hcont : Continuous (fun x : ℝ => hat c h q * κ * (((b - j : ℕ) : ℝ) * (x - c) ^ (b - j - 1))) := by
        fun_prop
      have key := hasDerivR_of_deriv _ _ hd hcont q
      have hv : hat c h q * κ * (((b - j : ℕ) : ℝ) * ((q:ℝ) - c) ^ (b - j - 1)) =
          hat c h q * ((b.descFactorial (j + 1) : ℝ) / b.factorial) * (cl c h q - c) ^ (b - (j + 1)) := by
        rw [cl_eq hq1 hq2, Nat.descFactorial_succ, Nat.sub_sub]
        simp only [κ]; push_cast; ring
      rw [← hv]
      refine hasDerivR_congr_near key ⟨min ρ (min ((q:ℝ) - (c - h)) ((c + h) - q)),
        lt_min hρ (lt_min (by linarith) (by linarith)), fun r hr => ?_⟩
      have hr1 := lt_of_lt_of_le hr (min_le_left _ _)
      have hr2 := lt_of_lt_of_le hr ((min_le_right _ _).trans (min_le_left _ _))
      have hr3 := lt_of_lt_of_le hr ((min_le_right _ _).trans (min_le_right _ _))
      rw [abs_lt] at hr2 hr3
      rw [hc r hr1, cl_eq (by linarith) (by linarith)]

/-! ## Finite sums in an abstract test space -/

noncomputable def sumZ {d : ℕ} (Z : TestFunctionSpace d) : List (ℝ × TestFunction d) → TestFunction d
  | [] => Z.zero
  | p :: l => Z.add (Z.scale (name p.1) (name_valid _) p.2) (sumZ Z l)

theorem dv_sumZ {d : ℕ} (Z : TestFunctionSpace d) (l : List (ℝ × TestFunction d))
    (α : MultiIndex d) (x : QPoint d) :
    dv (sumZ Z l) α x = (l.map fun p => p.1 * dv p.2 α x).sum := by
  induction l with
  | nil => exact dv_Zzero Z α x
  | cons p l ih => simp only [sumZ, dv_Zadd, dv_Zscale, val_name, ih, List.map_cons, List.sum_cons]

theorem span_sumZ {m n : ℕ} (Z : TestFunctionSpace (m + n)) (l : List (ℝ × TestFunction (m + n)))
    (h : ∀ p ∈ l, ∃ φ ψ, IsTensorTest φ ψ p.2) : TensorSpan Z (sumZ Z l) := by
  induction l with
  | nil => exact TensorSpan.zero
  | cons p l ih =>
    obtain ⟨φ, ψ, hp⟩ := h p List.mem_cons_self
    exact TensorSpan.add (TensorSpan.scale _ _ (TensorSpan.tensor φ ψ _ hp))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ## The approximating sums -/

def hN (N : ℕ) : ℚ := 1 / (N + 1)

theorem hN_pos (N : ℕ) : (0:ℝ) < hN N := by unfold hN; push_cast; positivity

theorem hN_le (N : ℕ) : (hN N : ℝ) ≤ 1 := by
  unfold hN; push_cast
  rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

def cen {d : ℕ} (θ : TestFunction d) (N : ℕ) (j : Fin d → ℕ) (i : Fin d) : ℚ :=
  θ.support.lower i + j i * hN N

def NN {d : ℕ} (θ : TestFunction d) (N : ℕ) (i : Fin d) : ℕ :=
  ⌈(θ.support.upper i - θ.support.lower i) * (N + 1)⌉₊ + 1

def grid {d : ℕ} (θ : TestFunction d) (N : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (NN θ N i))

def cube (d k : ℕ) : Finset (Fin d → ℕ) := Fintype.piFinset (fun _ : Fin d => Finset.range (k + 1))

noncomputable def termP {d : ℕ} (θ : TestFunction d) (N : ℕ) (j β : Fin d → ℕ) : Fin d → Prof :=
  fun i => mono (cen θ N j i) (hN N) (hN_pos N) (hN_le N) (β i)

noncomputable def termL {d : ℕ} (θ : TestFunction d) (N k : ℕ) : List (ℝ × TestFunction d) :=
  (grid θ N ×ˢ cube d k).toList.map
    (fun p => (dv θ p.2 (fun i => cen θ N p.1 i), (prodC (termP θ N p.1 p.2)).toTest))

theorem dv_approx {d : ℕ} (Z : TestFunctionSpace d) (θ : TestFunction d) (N k : ℕ)
    (α : MultiIndex d) (z : QPoint d) :
    dv (sumZ Z (termL θ N k)) α z = ∑ p ∈ grid θ N ×ˢ cube d k,
      dv θ p.2 (fun i => cen θ N p.1 i) * ∏ i, (termP θ N p.1 p.2 i).f (α i) ((z i : ℚ) : ℝ) := by
  rw [dv_sumZ, termL, List.map_map, Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Function.comp, dv_prodC]

/-! ## Estimates -/

def Wd {d : ℕ} (θ : TestFunction d) : ℚ := ∑ i, (θ.support.upper i - θ.support.lower i)

theorem Wd_nonneg {d : ℕ} (θ : TestFunction d) : 0 ≤ Wd θ :=
  Finset.sum_nonneg (fun i _ => sub_nonneg.2 (θ.support.ordered i))

noncomputable def Mb {d : ℕ} (θ : TestFunction d) (β : MultiIndex d) : ℝ :=
  |dv θ β θ.support.lower| + ((θ.derivativeLipschitz β * Wd θ : ℚ) : ℝ)

theorem Mb_nonneg {d : ℕ} (θ : TestFunction d) (β : MultiIndex d) : 0 ≤ Mb θ β :=
  add_nonneg (abs_nonneg _)
    (by exact_mod_cast mul_nonneg (θ.derivativeLipschitz_nonneg β) (Wd_nonneg θ))

theorem dv_bound {d : ℕ} (θ : TestFunction d) (β : MultiIndex d) (z : QPoint d) :
    |dv θ β z| ≤ Mb θ β := by
  by_cases hz : θ.support.Contains z
  · have hw : ∀ i, z i ≤ θ.support.lower i + Wd θ ∧ θ.support.lower i ≤ z i + Wd θ := by
      intro i
      have h1 : θ.support.upper i - θ.support.lower i ≤ Wd θ :=
        Finset.single_le_sum (f := fun i => θ.support.upper i - θ.support.lower i)
          (fun j _ => sub_nonneg.2 (θ.support.ordered j)) (Finset.mem_univ i)
      have h2 := hz i
      have h3 := Wd_nonneg θ
      constructor <;> linarith [h2.1, h2.2]
    have e1 := dv_lip θ β z θ.support.lower (Wd θ) (Wd_nonneg θ) hw
    have e2 := abs_sub_abs_le_abs_sub (dv θ β z) (dv θ β θ.support.lower)
    unfold Mb
    linarith
  · rw [dv_vanish θ β z hz, abs_zero]; exact Mb_nonneg θ β

noncomputable def Ecst {d : ℕ} (θ : TestFunction d) (k : ℕ) : ℝ :=
  ∑ β ∈ cube d k, Mb θ β + ∑ β ∈ cube d k, ((θ.derivativeLipschitz β : ℚ) : ℝ)

theorem Ecst_nonneg {d : ℕ} (θ : TestFunction d) (k : ℕ) : 0 ≤ Ecst θ k :=
  add_nonneg (Finset.sum_nonneg fun β _ => Mb_nonneg θ β)
    (Finset.sum_nonneg fun β _ => by exact_mod_cast θ.derivativeLipschitz_nonneg β)

noncomputable def wt {d : ℕ} (β α : MultiIndex d) (y c : Fin d → ℝ) : ℝ :=
  ∏ i, ((β i).descFactorial (α i) / (β i).factorial : ℝ) * (y i - c i) ^ (β i - α i)

theorem wt_self {d : ℕ} (α : MultiIndex d) (y c : Fin d → ℝ) : wt α α y c = 1 := by
  unfold wt; apply Finset.prod_eq_one; intro i _
  rw [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one,
    div_self (by exact_mod_cast (Nat.factorial_pos _).ne')]

theorem fac_le (n k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(n.descFactorial k / n.factorial : ℝ) * x ^ (n - k)| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (descF_nonneg n k), abs_pow]
  calc _ ≤ 1 * 1 :=
        mul_le_mul (descF_le n k) (pow_le_one₀ (abs_nonneg _) hx) (by positivity) zero_le_one
    _ = 1 := one_mul 1

theorem fac_le_h (n k : ℕ) (hk : k < n) {x h : ℝ} (hx : |x| ≤ h) (h1 : h ≤ 1) :
    |(n.descFactorial k / n.factorial : ℝ) * x ^ (n - k)| ≤ h := by
  rw [abs_mul, abs_of_nonneg (descF_nonneg n k), abs_pow]
  have : |x| ^ (n - k) ≤ |x| := pow_le_of_le_one (abs_nonneg _) (hx.trans h1) (by omega)
  calc _ ≤ 1 * h := mul_le_mul (descF_le n k) (this.trans hx) (by positivity) zero_le_one
    _ = h := one_mul h

theorem wt_small {d : ℕ} {β α : MultiIndex d} (hne : β ≠ α) {y c : Fin d → ℝ} {h : ℝ}
    (hy : ∀ i, |y i - c i| ≤ h) (h1 : h ≤ 1) (h0 : 0 ≤ h) : |wt β α y c| ≤ h := by
  unfold wt
  by_cases hlt : ∃ i, β i < α i
  · obtain ⟨i, hi⟩ := hlt
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [Nat.descFactorial_eq_zero_iff_lt.2 hi]; simp)]
    simpa using h0
  · simp only [not_exists, not_lt] at hlt
    have : ∃ i, β i ≠ α i := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hne (funext hc)
    obtain ⟨i0, hi0⟩ := this
    have hlt0 : α i0 < β i0 := lt_of_le_of_ne (hlt i0) (Ne.symm hi0)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), abs_mul, Finset.abs_prod]
    have p1 : ∏ x ∈ Finset.univ.erase i0,
        |((β x).descFactorial (α x) / (β x).factorial : ℝ) * (y x - c x) ^ (β x - α x)| ≤ 1 :=
      Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => fac_le _ _ ((hy j).trans h1))
    calc _ ≤ h * 1 := mul_le_mul (fac_le_h _ _ hlt0 (hy i0) h1) p1
          (Finset.prod_nonneg fun _ _ => abs_nonneg _) h0
      _ = h := mul_one h

theorem mem_cube {d k : ℕ} {α : MultiIndex d} (hα : ∀ i, α i ≤ k) : α ∈ cube d k :=
  Fintype.mem_piFinset.2 (fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (hα i)))

theorem T_bound {d : ℕ} (θ : TestFunction d) (k : ℕ) (α : MultiIndex d) (hα : ∀ i, α i ≤ k)
    (z c : QPoint d) (h : ℚ) (h0 : 0 ≤ h) (h1 : (h:ℝ) ≤ 1)
    (hzc : ∀ i, z i ≤ c i + h ∧ c i ≤ z i + h) :
    |∑ β ∈ cube d k, dv θ β c * wt β α (fun i => (z i : ℝ)) (fun i => (c i : ℝ)) - dv θ α z|
      ≤ Ecst θ k * h := by
  have hα' := mem_cube hα
  rw [← Finset.add_sum_erase _ _ hα', wt_self, mul_one]
  have hy : ∀ i, |((z i : ℚ) : ℝ) - c i| ≤ h := fun i => by
    rw [abs_le]; have hz := hzc i
    have a1 : (c i : ℝ) ≤ z i + h := by exact_mod_cast hz.2
    have a2 : (z i : ℝ) ≤ c i + h := by exact_mod_cast hz.1
    constructor <;> linarith
  have h0' : (0:ℝ) ≤ h := by exact_mod_cast h0
  have eR : |∑ β ∈ (cube d k).erase α,
      dv θ β c * wt β α (fun i => (z i : ℝ)) (fun i => (c i : ℝ))| ≤ (∑ β ∈ cube d k, Mb θ β) * h := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset α _)
      (fun β _ _ => mul_nonneg (Mb_nonneg θ β) h0'))
    refine Finset.sum_le_sum (fun β hβ => ?_)
    rw [abs_mul]
    exact mul_le_mul (dv_bound θ β c) (wt_small (Finset.ne_of_mem_erase hβ) hy h1 h0')
      (abs_nonneg _) (Mb_nonneg θ β)
  have eL := dv_lip θ α c z h h0 (fun i => ⟨(hzc i).2, (hzc i).1⟩)
  have hLα : ((θ.derivativeLipschitz α : ℚ) : ℝ) ≤
      ∑ β ∈ cube d k, ((θ.derivativeLipschitz β : ℚ) : ℝ) :=
    Finset.single_le_sum (f := fun β => ((θ.derivativeLipschitz β : ℚ) : ℝ))
      (fun β _ => by exact_mod_cast θ.derivativeLipschitz_nonneg β) hα'
  push_cast at eL
  set R := ∑ β ∈ (cube d k).erase α, dv θ β c * wt β α (fun i => (z i : ℝ)) (fun i => (c i : ℝ))
  calc |dv θ α c + R - dv θ α z| = |(dv θ α c - dv θ α z) + R| := by congr 1; ring
    _ ≤ |dv θ α c - dv θ α z| + |R| := abs_add_le _ _
    _ ≤ (θ.derivativeLipschitz α : ℝ) * h + (∑ β ∈ cube d k, Mb θ β) * h := add_le_add eL eR
    _ ≤ (∑ β ∈ cube d k, ((θ.derivativeLipschitz β : ℚ) : ℝ)) * h + (∑ β ∈ cube d k, Mb θ β) * h := by
        gcongr
    _ = Ecst θ k * h := by unfold Ecst; ring

theorem chi_sum {d : ℕ} (θ : TestFunction d) (N : ℕ) (z : QPoint d) :
    ∑ j ∈ grid θ N, ∏ i, hat (cen θ N j i) (hN N) (z i) =
      ∏ i, (stp ((z i - θ.support.lower i) / hN N + 1) -
        stp ((z i - θ.support.lower i) / hN N + 1 - NN θ N i)) := by
  have e : ∀ i, stp ((((z i : ℚ) : ℝ) - (θ.support.lower i : ℝ)) / (hN N : ℝ) + 1) -
      stp ((((z i : ℚ) : ℝ) - (θ.support.lower i : ℝ)) / (hN N : ℝ) + 1 - (NN θ N i : ℝ)) =
      ∑ j ∈ Finset.range (NN θ N i), hat (θ.support.lower i + j * hN N) (hN N) (z i) :=
    fun i => (hat_sum _ _ (hN_pos N) _ _).symm
  simp_rw [e]
  rw [Finset.prod_univ_sum]
  rfl

theorem chi_factor_nonneg (u : ℝ) (n : ℕ) : 0 ≤ stp (u + 1) - stp (u + 1 - n) := by
  have := stp_mono (show u + 1 - n ≤ u + 1 by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  linarith

theorem chi_factor_le (u : ℝ) (n : ℕ) : stp (u + 1) - stp (u + 1 - n) ≤ 1 := by
  have := stp_le_one (u + 1); have := stp_nonneg (u + 1 - n); linarith

theorem chi_sum_le {d : ℕ} (θ : TestFunction d) (N : ℕ) (z : QPoint d) :
    ∑ j ∈ grid θ N, ∏ i, hat (cen θ N j i) (hN N) (z i) ≤ 1 := by
  rw [chi_sum]
  exact Finset.prod_le_one (fun i _ => chi_factor_nonneg _ _) (fun i _ => chi_factor_le _ _)

theorem chi_sum_one {d : ℕ} (θ : TestFunction d) (N : ℕ) (z : QPoint d)
    (hz : θ.support.Contains z) :
    ∑ j ∈ grid θ N, ∏ i, hat (cen θ N j i) (hN N) (z i) = 1 := by
  rw [chi_sum]
  apply Finset.prod_eq_one
  intro i _
  have hzi := hz i
  have hpos := hN_pos N
  have a0 : (0:ℝ) ≤ ((z i : ℚ) : ℝ) - θ.support.lower i := by
    have : (θ.support.lower i : ℝ) ≤ z i := by exact_mod_cast hzi.1
    linarith
  have hu0 : 0 ≤ (((z i : ℚ) : ℝ) - θ.support.lower i) / hN N := div_nonneg a0 hpos.le
  rw [stp_one (by linarith)]
  have hceil := Nat.le_ceil ((θ.support.upper i - θ.support.lower i) * ((N : ℚ) + 1))
  have hc' : (((θ.support.upper i - θ.support.lower i) * ((N : ℚ) + 1) : ℚ) : ℝ) ≤
      ((⌈(θ.support.upper i - θ.support.lower i) * ((N : ℚ) + 1)⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hceil
  have hzu : ((z i : ℚ) : ℝ) ≤ θ.support.upper i := by exact_mod_cast hzi.2
  have hu : (((z i : ℚ) : ℝ) - θ.support.lower i) / hN N =
      (((z i : ℚ) : ℝ) - θ.support.lower i) * ((N : ℝ) + 1) := by
    unfold hN; push_cast; field_simp
  have hN1 : (0:ℝ) ≤ (N : ℝ) + 1 := by positivity
  have : (((z i : ℚ) : ℝ) - θ.support.lower i) / hN N + 1 - (NN θ N i : ℕ) ≤ 0 := by
    rw [hu]; unfold NN; push_cast at hc' ⊢
    nlinarith
  rw [stp_zero this]; ring

theorem approx_bound {d : ℕ} (θ : TestFunction d) (N k : ℕ) (α : MultiIndex d)
    (hα : ∀ i, α i ≤ k) (z : QPoint d) :
    |∑ p ∈ grid θ N ×ˢ cube d k, dv θ p.2 (fun i => cen θ N p.1 i) *
        ∏ i, (termP θ N p.1 p.2 i).f (α i) ((z i : ℚ) : ℝ) - dv θ α z| ≤ Ecst θ k * hN N := by
  set χ : (Fin d → ℕ) → ℝ := fun j => ∏ i, hat (cen θ N j i) (hN N) (z i) with hχ
  set T : (Fin d → ℕ) → ℝ := fun j => ∑ β ∈ cube d k, dv θ β (fun i => cen θ N j i) *
    wt β α (fun i => cl (cen θ N j i) (hN N) (z i)) (fun i => (cen θ N j i : ℝ)) with hT
  have hexp : ∀ j, ∑ β ∈ cube d k, dv θ β (fun i => cen θ N j i) *
      ∏ i, (termP θ N j β i).f (α i) ((z i : ℚ) : ℝ) = χ j * T j := by
    intro j
    rw [hT, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro β _
    have : ∏ i, (termP θ N j β i).f (α i) ((z i : ℚ) : ℝ) =
        χ j * wt β α (fun i => cl (cen θ N j i) (hN N) (z i)) (fun i => (cen θ N j i : ℝ)) := by
      rw [hχ, wt, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      simp only [termP, mono]; ring
    rw [this]; ring
  rw [Finset.sum_product]
  simp_rw [hexp]
  have hχ0 : ∀ j, 0 ≤ χ j := fun j => Finset.prod_nonneg fun i _ => hat_nonneg _ _ _
  have hE0 := Ecst_nonneg θ k
  have hh0 := hN_pos N
  have hsplit : ∑ j ∈ grid θ N, χ j * T j - dv θ α z =
      ∑ j ∈ grid θ N, χ j * (T j - dv θ α z) + (∑ j ∈ grid θ N, χ j - 1) * dv θ α z := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]; ring
  have hzero : (∑ j ∈ grid θ N, χ j - 1) * dv θ α z = 0 := by
    by_cases hz : θ.support.Contains z
    · rw [hχ, chi_sum_one θ N z hz]; ring
    · rw [dv_vanish θ α z hz]; ring
  rw [hsplit, hzero, add_zero]
  have hterm : ∀ j ∈ grid θ N, |χ j * (T j - dv θ α z)| ≤ χ j * (Ecst θ k * hN N) := by
    intro j _
    rw [abs_mul, abs_of_nonneg (hχ0 j)]
    by_cases hc : χ j = 0
    · rw [hc]; simp
    refine mul_le_mul_of_nonneg_left ?_ (hχ0 j)
    have hne : ∀ i, hat (cen θ N j i) (hN N) (z i) ≠ 0 := by
      intro i; rw [hχ] at hc
      exact (Finset.prod_ne_zero_iff.1 hc) i (Finset.mem_univ i)
    have hb : ∀ i, ((cen θ N j i : ℚ) : ℝ) - hN N < z i ∧ ((z i : ℚ) : ℝ) < cen θ N j i + hN N :=
      fun i => hat_ne_zero hh0 (hne i)
    have hcl : (fun i => cl (cen θ N j i) (hN N) (z i)) = fun i => ((z i : ℚ) : ℝ) :=
      funext fun i => cl_eq (hb i).1 (hb i).2
    have hzc : ∀ i, z i ≤ cen θ N j i + hN N ∧ cen θ N j i ≤ z i + hN N := by
      intro i
      have b1 := (hb i).1; have b2 := (hb i).2
      constructor
      · have : ((z i : ℚ) : ℝ) ≤ ((cen θ N j i + hN N : ℚ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · have : ((cen θ N j i : ℚ) : ℝ) ≤ ((z i + hN N : ℚ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
    have := T_bound θ k α hα z (fun i => cen θ N j i) (hN N) (by exact_mod_cast hh0.le) (hN_le N) hzc
    rw [hT]; simp only
    rw [hcl]
    exact this
  calc |∑ j ∈ grid θ N, χ j * (T j - dv θ α z)|
      ≤ ∑ j ∈ grid θ N, |χ j * (T j - dv θ α z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ grid θ N, χ j * (Ecst θ k * hN N) := Finset.sum_le_sum hterm
    _ = (∑ j ∈ grid θ N, χ j) * (Ecst θ k * hN N) := by rw [Finset.sum_mul]
    _ ≤ 1 * (Ecst θ k * hN N) :=
        mul_le_mul_of_nonneg_right (by rw [hχ]; exact chi_sum_le θ N z) (by positivity)
    _ = Ecst θ k * hN N := one_mul _

/-- Density of separated tests in the derivative norms, with a fixed support box. -/
theorem dense {m n : Nat} (Z : TestFunctionSpace (m + n)) (θ : TestFunction (m + n)) :
    ∃ B : RationalBox (m + n), ∀ (k : Nat) (δ : ℚ), 0 < δ →
      ∃ S, TensorSpan Z S ∧
        (∀ z, ¬ B.Contains z → dv θ (zeroIndex _) z = dv S (zeroIndex _) z) ∧
        (∀ α : MultiIndex (m + n), (∀ i, α i ≤ k) → ∀ z, |dv θ α z - dv S α z| ≤ δ) := by
  refine ⟨⟨fun i => θ.support.lower i - 2, fun i => θ.support.upper i + 2,
    fun i => by linarith [θ.support.ordered i]⟩, ?_⟩
  intro k δ hδ
  set N := ⌈Ecst θ k / δ⌉₊ with hNdef
  refine ⟨sumZ Z (termL θ N k), span_sumZ Z _ ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hp
    exact ⟨_, _, tensor_prodC _⟩
  · intro z hz
    rw [dv_approx]
    have hz' : ¬ θ.support.Contains z := fun h => hz (fun i =>
      ⟨by show θ.support.lower i - 2 ≤ z i; linarith [(h i).1],
       by show z i ≤ θ.support.upper i + 2; linarith [(h i).2]⟩)
    rw [dv_vanish θ _ z hz']
    symm; apply Finset.sum_eq_zero; intro p hp
    simp only [RationalBox.Contains, not_forall] at hz
    obtain ⟨i, hi⟩ := hz
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    show hat _ _ _ * _ * _ = 0
    rw [hat_out (hN_pos N), zero_mul, zero_mul]
    have hq0 : (0:ℚ) < hN N := by exact_mod_cast hN_pos N
    have hq1 : hN N ≤ 1 := by exact_mod_cast hN_le N
    have hj : p.1 i < NN θ N i := by
      have := (Finset.mem_product.1 hp).1
      exact Finset.mem_range.1 (Fintype.mem_piFinset.1 this i)
    have hjn : (0:ℚ) ≤ (p.1 i : ℚ) * hN N := by positivity
    rw [not_and_or] at hi
    rcases hi with hi | hi
    · left
      have : z i ≤ cen θ N p.1 i - hN N := by
        unfold cen; have := not_le.1 hi; linarith
      exact_mod_cast this
    · right
      have hNN : ((p.1 i : ℚ) + 1) * hN N ≤ θ.support.upper i - θ.support.lower i + 2 := by
        have hle : (p.1 i : ℚ) + 1 ≤ NN θ N i := by exact_mod_cast hj
        have hab : 0 ≤ (θ.support.upper i - θ.support.lower i) * ((N : ℚ) + 1) :=
          mul_nonneg (sub_nonneg.2 (θ.support.ordered i)) (by positivity)
        have hcl := Nat.ceil_lt_add_one hab
        have hNN' : (NN θ N i : ℚ) < (θ.support.upper i - θ.support.lower i) * ((N : ℚ) + 1) + 2 := by
          unfold NN; push_cast; linarith
        unfold hN
        rw [← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
        have : (0:ℚ) ≤ N := Nat.cast_nonneg N
        nlinarith [θ.support.ordered i]
      have : cen θ N p.1 i + hN N ≤ z i := by
        unfold cen; have := not_le.1 hi; nlinarith
      exact_mod_cast this
  · intro α hα z
    rw [dv_approx, abs_sub_comm]
    refine (approx_bound θ N k α hα z).trans ?_
    have hδ' : (0:ℝ) < δ := by exact_mod_cast hδ
    have hc := Nat.le_ceil (Ecst θ k / δ)
    rw [← hNdef] at hc
    have hE : Ecst θ k ≤ N * δ := (div_le_iff₀ hδ').1 hc
    unfold hN; push_cast
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith

theorem uniqueness : SchwartzKernelUniquenessTarget := by
  intro m n X Y Z B K L hK hL θ
  have hKL : ∀ φ ψ θ, IsTensorTest φ ψ θ → val (K.action θ) = val (L.action θ) :=
    fun φ ψ θ h =>
      (val_eq_of_equiv (K.action_valid θ) ((B.linear_left ψ).value_valid φ) (hK φ ψ θ h)).trans
        (val_eq_of_equiv (L.action_valid θ) ((B.linear_left ψ).value_valid φ) (hL φ ψ θ h)).symm
  apply equiv_of_val_eq (K.action_valid θ) (L.action_valid θ)
  obtain ⟨Bx, hB⟩ := dense Z θ
  apply eq_of_close
  intro ε hε
  obtain ⟨k1, δ1, hδ1, h1⟩ := K.small_action_on_box Bx (ε / 2) (by positivity)
  obtain ⟨k2, δ2, hδ2, h2⟩ := L.small_action_on_box Bx (ε / 2) (by positivity)
  obtain ⟨S, hS, hsupp, hbd⟩ := hB (max k1 k2) (min δ1 δ2) (lt_min hδ1 hδ2)
  have hm1 : val (RealCompute.ofRat (-1)) = -1 := by rw [val_ofRat]; norm_num
  set D := Z.add θ (Z.scale (RealCompute.ofRat (-1)) (ofRat_valid' (-1)) S) with hD
  have hDs : D.SupportedInBox Bx := by
    intro z hz
    apply equiv_of_val_eq (D.derivative_valid _ z) (ofRat_valid' 0)
    show dv D (zeroIndex _) z = _
    rw [hD, dv_sub_test Z θ S _ z _ _ hm1, hsupp z hz, val_ofRat]; simp
  have hDb : ∀ (k : ℕ) (δ : ℚ), k ≤ max k1 k2 → min δ1 δ2 ≤ δ → D.DerivativesBoundedBy k δ := by
    intro k δ hk hδ α hα x
    rw [smallApprox_iff]
    show |dv D α x| ≤ _
    rw [hD, dv_sub_test Z θ S α x _ _ hm1]
    refine (hbd α (fun i => ?_) x).trans (by exact_mod_cast hδ)
    have := index_le_order α i
    omega
  have e1 := (smallApprox_iff _ _).1 (h1 D hDs (hDb k1 δ1 (le_max_left _ _) (min_le_left _ _)))
  have e2 := (smallApprox_iff _ _).1 (h2 D hDs (hDb k2 δ2 (le_max_right _ _) (min_le_right _ _)))
  rw [hD, val_action_sub K θ S _ _ hm1] at e1
  rw [hD, val_action_sub L θ S _ _ hm1] at e2
  rw [agree_on_span K L hKL hS] at e1
  have := abs_sub_le (val (K.action θ) - val (L.action S)) 0 (val (L.action θ) - val (L.action S))
  calc |val (K.action θ) - val (L.action θ)|
      = |(val (K.action θ) - val (L.action S)) - (val (L.action θ) - val (L.action S))| := by
        ring_nf
    _ ≤ |val (K.action θ) - val (L.action S)| + |val (L.action θ) - val (L.action S)| :=
        abs_sub _ _
    _ ≤ ε := by push_cast at e1 e2; linarith

end CBridge
end ComputableDistributions

theorem solution : ComputableDistributions.SchwartzKernelUniquenessTarget :=
  ComputableDistributions.CBridge.uniqueness
