-- Prove2me | solution 1 for DistributionTheoryMission.classical_huygens
-- status  : ACCEPTED   (disprove)
-- author  : @Xeroth
-- created : 2026-11-24T01:18:52.307009+00:00
-- url     : https://prove2.me/submissions/57c083e6-ceb6-4af6-8824-0700063aeb42

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_ClassicalHuygens
import Mathlib

open MeasureTheory Filter Topology

namespace HuyStair

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

end HuyStair

set_option autoImplicit true

open ComputableAnalysis Filter Topology

namespace ComputableDistributions
namespace HBridge

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

theorem val_sumRaw_zero : ∀ (n : ℕ) (g : Fin n → RealCompute), (∀ i, (g i).Valid) →
    (∀ i, val (g i) = 0) → val (sumRaw n g) = 0
  | 0, _, _, _ => by simp [sumRaw, val_ofRat]
  | n + 1, g, hv, h0 => by
      show val (RealCompute.add _ _) = 0
      rw [val_add (sumRaw_valid n _ (fun i => hv i.castSucc)) (hv _),
        val_sumRaw_zero n _ (fun i => hv i.castSucc) (fun i => h0 i.castSucc), h0]
      simp

theorem incrementIndex_ne_zero {d : ℕ} (α : MultiIndex d) (i : Fin d) :
    incrementIndex α i ≠ zeroIndex d := by
  intro h
  have := congrFun h i
  simp [incrementIndex, zeroIndex] at this

open Classical in
/-- A "solution" whose value is the staircase `h` in time and whose
represented derivatives all vanish. -/
noncomputable def uD (α : MultiIndex 4) (p : QPoint 4) : ℝ :=
  if α = zeroIndex 4 then HuyStair.h (p (timeCoordinate 3)) else 0

theorem uD_inc (α : MultiIndex 4) (i : Fin 4) (p : QPoint 4) :
    uD (incrementIndex α i) p = 0 := by
  simp [uD, incrementIndex_ne_zero]

noncomputable def uSol : ClassicalHuygens.ClassicalSolution 3 where
  derivative α p := name (uD α p)
  valid _ _ := name_valid _
  localControl α B _ := ⟨1, by norm_num, fun p q _ _ r hr hc => by
    rw [smallSub_iff, val_name, val_name]
    unfold uD
    split_ifs
    · have h1 := HuyStair.h_abs (p (timeCoordinate 3)) (q (timeCoordinate 3))
      have hc0 := hc (timeCoordinate 3)
      have a1 : ((p (timeCoordinate 3) : ℚ) : ℝ) ≤ q (timeCoordinate 3) + r := by exact_mod_cast hc0.1
      have a2 : ((q (timeCoordinate 3) : ℚ) : ℝ) ≤ p (timeCoordinate 3) + r := by exact_mod_cast hc0.2
      push_cast
      refine h1.trans ?_
      rw [abs_le]; constructor <;> linarith
    · simp; exact_mod_cast hr⟩
  nextPartial α _ i p := by
    rw [hasDeriv_iff (fun r => name_valid _) _ (name_valid _)]
    simp only [val_name]
    rw [uD_inc]
    apply hasDerivR_of_locConst
    by_cases hα : α = zeroIndex 4
    · by_cases hi : i = timeCoordinate 3
      · subst hi
        obtain ⟨ρ, hρ, hh⟩ := HuyStair.h_locConst (p (timeCoordinate 3))
        refine ⟨ρ, hρ, fun r hr => ?_⟩
        simp only [uD, hα, if_true, replaceCoordinate]
        simpa using hh r hr
      · refine ⟨1, one_pos, fun r _ => ?_⟩
        have : timeCoordinate 3 ≠ i := Ne.symm hi
        simp [uD, hα, replaceCoordinate, this]
    · exact ⟨1, one_pos, fun r _ => by simp [uD, hα]⟩

theorem not_target : ¬ ClassicalHuygens.Target := by
  intro H
  have hsolve : ClassicalHuygens.Solves uSol (space 3).zero (space 3).zero (space 4).zero := by
    refine ⟨fun x => ⟨?_, ?_⟩, fun p _ => ?_⟩
    · refine RealCompute.equiv_trans (name_valid _) (ofRat_valid' 0)
        ((space 3).zero.value_valid x) ?_ (RealCompute.equiv_symm ((space 3).zero_derivative _ x))
      apply equiv_of_val_eq (name_valid _) (ofRat_valid' 0)
      rw [val_name, val_ofRat]
      simp [uD, ClassicalHuygens.onTimeZero, timeCoordinate]
      exact HuyStair.h_nonpos le_rfl
    · refine RealCompute.equiv_trans (name_valid _) (ofRat_valid' 0)
        ((space 3).zero.value_valid x) ?_ (RealCompute.equiv_symm ((space 3).zero_derivative _ x))
      apply equiv_of_val_eq (name_valid _) (ofRat_valid' 0)
      rw [val_name, val_ofRat, uD_inc]; simp
    · dsimp only
      have hv : ∀ i, (uSol.derivative (incrementIndex (incrementIndex (zeroIndex _) i) i) p).Valid :=
        fun i => name_valid _
      have h0 : ∀ i, val (uSol.derivative (incrementIndex (incrementIndex (zeroIndex _) i) i) p) = 0 :=
        fun i => by
          show val (name _) = 0
          rw [val_name, uD_inc]
      refine RealCompute.equiv_trans
        (RealCompute.sub_valid (hv _) (sumRaw_valid _ _ (fun i => hv _))) (ofRat_valid' 0)
        ((space 4).zero.value_valid p) ?_ (RealCompute.equiv_symm ((space 4).zero_derivative _ p))
      apply equiv_of_val_eq (RealCompute.sub_valid (hv _) (sumRaw_valid _ _ (fun i => hv _)))
        (ofRat_valid' 0)
      show val (RealCompute.sub _ _) = val (RealCompute.ofRat 0)
      rw [val_sub (hv _) (sumRaw_valid _ _ (fun i => hv _)), h0,
        val_sumRaw_zero _ _ (fun i => hv _) (fun i => h0 _), val_ofRat]
      simp
  have hdata : ClassicalHuygens.DataVanishNearBackwardBoundary (space 3).zero (space 3).zero
      (space 4).zero (fun _ => 1) 1 :=
    ⟨fun x _ _ _ => ⟨(space 3).zero_derivative _ x, (space 3).zero_derivative _ x⟩,
      fun q _ _ _ _ => (space 4).zero_derivative _ q⟩
  have hz := H 3 le_rfl rfl _ _ _ uSol hsolve (fun _ => 1) (by norm_num) ⟨1, by norm_num, hdata⟩
  have hv := val_eq_of_equiv (name_valid _) (ofRat_valid' 0) hz
  rw [val_name, val_ofRat] at hv
  have h1 := HuyStair.h_one
  simp [uD] at hv
  push_cast at hv
  linarith

end HBridge
end ComputableDistributions

theorem solution : ¬ ComputableDistributions.ClassicalHuygens.Target :=
  ComputableDistributions.HBridge.not_target
