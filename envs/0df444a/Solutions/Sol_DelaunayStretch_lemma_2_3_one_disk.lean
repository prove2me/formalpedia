-- Prove2me | solution 1 for DelaunayStretch.lemma_2_3_one_disk
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:47:08.592945+00:00
-- url     : https://prove2.me/submissions/e9370625-8351-45ea-b334-fda67360890e

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality

open DelaunayStretch

/-- Jordan's inequality with its equality case, in the form `2t ≤ π sin t` on `(0, π/2]`. -/
theorem jordan_two_mul_le_pi_mul_sin (t : ℝ) (h0 : 0 < t) (h1 : t ≤ Real.pi / 2) :
    2 * t ≤ Real.pi * Real.sin t ∧ (2 * t = Real.pi * Real.sin t ↔ t = Real.pi / 2) := by
  have hpi := Real.pi_pos
  have key : ∀ s : ℝ, 2 / Real.pi * s ≤ Real.sin s → 2 * s ≤ Real.pi * Real.sin s := by
    intro s hs
    have : 2 / Real.pi * s * Real.pi = 2 * s := by field_simp
    nlinarith
  refine ⟨key t (Real.mul_le_sin h0.le h1), ?_, ?_⟩
  · intro heq
    by_contra hne
    have hlt : t < Real.pi / 2 := lt_of_le_of_ne h1 hne
    have := Real.mul_lt_sin h0 hlt
    have : 2 / Real.pi * t * Real.pi = 2 * t := by field_simp
    nlinarith
  · rintro rfl
    rw [Real.sin_pi_div_two]; ring

/-- Recognising `Complex.arg` from polar coordinates. -/
theorem arg_eq_of_re_im (z : ℂ) (r θ : ℝ) (hr : 0 < r) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hre : z.re = r * Real.cos θ) (him : z.im = r * Real.sin θ) : Complex.arg z = θ := by
  have : z = (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext
    · simp [hre, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    · simp [him, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [this, Complex.arg_mul_cos_add_sin_mul_I hr hθ]

/-- Part 1: one circle. -/
theorem one_circle_bound (o u v : ℂ) (r : ℝ) (hu : u ∈ Metric.sphere o r)
    (hv : v ∈ Metric.sphere o r) (huv : u ≠ v) :
    r * EuclideanGeometry.angle u o v ≤ Real.pi / 2 * dist u v ∧
      (r * EuclideanGeometry.angle u o v = Real.pi / 2 * dist u v ↔
        EuclideanGeometry.angle u o v = Real.pi) := by
  rw [Metric.mem_sphere] at hu hv
  set θ := EuclideanGeometry.angle u o v with hθ
  have hθ0 : 0 ≤ θ := EuclideanGeometry.angle_nonneg _ _ _
  have hθπ : θ ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _
  have hlaw := EuclideanGeometry.law_cos u o v
  rw [hu, hv, ← hθ] at hlaw
  set t := θ / 2 with ht
  have hθt : θ = 2 * t := by rw [ht]; ring
  have hcos : Real.cos θ = 1 - 2 * Real.sin t ^ 2 := by
    rw [hθt, Real.cos_two_mul, Real.cos_sq']; ring
  have hsin0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hr0 : 0 ≤ r := hu ▸ dist_nonneg
  have hr : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exfalso; apply huv
      rw [← h] at hu hv
      rw [dist_eq_zero.1 hu, dist_eq_zero.1 hv]
  have hd : dist u v = 2 * r * Real.sin t := by
    have hsq : dist u v * dist u v = (2 * r * Real.sin t) * (2 * r * Real.sin t) := by
      rw [hlaw, hcos]; ring
    rcases mul_self_eq_mul_self_iff.1 hsq with h | h
    · exact h
    · have : 0 ≤ dist u v := dist_nonneg
      have : 0 ≤ 2 * r * Real.sin t := by positivity
      linarith
  have ht0 : 0 < t := by
    rcases (show 0 ≤ t by linarith).lt_or_eq with h | h
    · exact h
    · exfalso; apply huv
      rw [← h, Real.sin_zero, mul_zero] at hd
      exact dist_eq_zero.1 hd
  obtain ⟨hJ, hJeq⟩ := jordan_two_mul_le_pi_mul_sin t ht0 (by linarith)
  rw [hd, hθt]
  refine ⟨by nlinarith, ?_⟩
  constructor
  · intro h
    have : 2 * t = Real.pi * Real.sin t := by
      have : r * (2 * t) = r * (Real.pi * Real.sin t) := by linarith
      exact mul_left_cancel₀ hr.ne' this
    rw [hJeq.1 this]; ring
  · intro h
    have : t = Real.pi / 2 := by linarith
    rw [hJeq.2 this]; ring

/-- For a one-disk chain, every ladder edge is one of the two rails of `O₁`. -/
theorem ladderEdge_of_n_eq_one (C : DiskChain) (hn : C.n = 1) {x y : LadderVertex} {w : ℝ}
    (h : C.LadderEdge x y w) : w = C.upperRail 1 ∨ w = C.lowerRail 1 := by
  rcases h with ⟨i, h1, h2, -, rfl⟩ | ⟨i, h1, h2, -, rfl⟩ | ⟨i, h1, h2, -, -⟩
  · obtain rfl : i = 1 := by omega
    exact Or.inl rfl
  · obtain rfl : i = 1 := by omega
    exact Or.inr rfl
  · omega

/-- Lower bound on walk weights when all edge weights are at least `m ≥ 0`. -/
theorem ladderWalk_lower_bound (C : DiskChain) (k : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hedge : ∀ x y w, C.LadderEdge x y w → m ≤ w) {x z : LadderVertex} {L : ℝ}
    (hw : C.LadderWalk k x z L) : 0 ≤ L ∧ (x ≠ z → m ≤ L) := by
  induction hw with
  | nil x => exact ⟨le_rfl, fun h => absurd rfl h⟩
  | cons he _ _ _ ih =>
    have := hedge _ _ _ he
    exact ⟨by linarith [ih.1], fun _ => by linarith [ih.1]⟩

/-- For a one-disk chain, `P(u,v) = min(α₁, β₁)` provided both rails are nonnegative. -/
theorem shortestPath_n_eq_one (C : DiskChain) (hn : C.n = 1)
    (hα : 0 ≤ C.upperRail 1) (hβ : 0 ≤ C.lowerRail 1) :
    C.shortestPath = min (C.upperRail 1) (C.lowerRail 1) := by
  have htop0 : C.topV 0 = .start := by simp [DiskChain.topV]
  have htop1 : C.topV 1 = .finish := by simp [DiskChain.topV, hn]
  have hbot0 : C.botV 0 = .start := by simp [DiskChain.botV]
  have hbot1 : C.botV 1 = .finish := by simp [DiskChain.botV, hn]
  have hcs : C.column .start ≤ C.n := by simp [DiskChain.column]
  have hcf : C.column .finish ≤ C.n := by simp [DiskChain.column]
  have memα : C.upperRail 1 ∈ {L | C.LadderWalk C.n .start .finish L} := by
    have e : C.LadderEdge .start .finish (C.upperRail 1) :=
      Or.inl ⟨1, le_rfl, by omega, Or.inl ⟨by simpa using htop0.symm, htop1.symm⟩, rfl⟩
    have := DiskChain.LadderWalk.cons e hcs hcf (DiskChain.LadderWalk.nil .finish)
    simpa using this
  have memβ : C.lowerRail 1 ∈ {L | C.LadderWalk C.n .start .finish L} := by
    have e : C.LadderEdge .start .finish (C.lowerRail 1) :=
      Or.inr (Or.inl ⟨1, le_rfl, by omega, Or.inl ⟨by simpa using hbot0.symm, hbot1.symm⟩, rfl⟩)
    have := DiskChain.LadderWalk.cons e hcs hcf (DiskChain.LadderWalk.nil .finish)
    simpa using this
  have hleast : IsLeast {L | C.LadderWalk C.n .start .finish L}
      (min (C.upperRail 1) (C.lowerRail 1)) := by
    refine ⟨?_, ?_⟩
    · rcases min_choice (C.upperRail 1) (C.lowerRail 1) with h | h <;> rw [h]
      · exact memα
      · exact memβ
    · intro L hL
      have hedge : ∀ x y w, C.LadderEdge x y w → min (C.upperRail 1) (C.lowerRail 1) ≤ w := by
        intro x y w he
        rcases ladderEdge_of_n_eq_one C hn he with rfl | rfl
        · exact min_le_left _ _
        · exact min_le_right _ _
      exact (ladderWalk_lower_bound C C.n _ (le_min hα hβ) hedge hL).2 (by simp)
  exact hleast.csInf_eq

/-- Geometry of a one-disk chain: with `γ = arcsin(y(o)/r)`, the ends are the two axis points
of `∂O₁`, `α₁ = r(π + 2γ)`, `β₁ = r(π − 2γ)`, `‖u − v‖ = 2r cos γ`. -/
theorem one_disk_chain_geometry (C : DiskChain) (hC : C.IsDiskChain) (hn : C.n = 1) :
    0 < (C.O 1).radius ∧
    -(Real.pi / 2) < Real.arcsin ((C.O 1).center.im / (C.O 1).radius) ∧
    Real.arcsin ((C.O 1).center.im / (C.O 1).radius) < Real.pi / 2 ∧
    (Real.arcsin ((C.O 1).center.im / (C.O 1).radius) = 0 ↔ (C.O 1).center.im = 0) ∧
    C.upperRail 1 = (C.O 1).radius *
      (Real.pi + 2 * Real.arcsin ((C.O 1).center.im / (C.O 1).radius)) ∧
    C.lowerRail 1 = (C.O 1).radius *
      (Real.pi - 2 * Real.arcsin ((C.O 1).center.im / (C.O 1).radius)) ∧
    dist C.u C.v = 2 * (C.O 1).radius *
      Real.cos (Real.arcsin ((C.O 1).center.im / (C.O 1).radius)) := by
  obtain ⟨-, hrad, huim, hvim, hu, hv, hlt, -⟩ := hC
  rw [hn] at hv
  have hr : 0 < (C.O 1).radius := hrad 1 le_rfl hn.ge
  simp only [Disk.boundary, Metric.mem_sphere, Complex.dist_eq] at hu hv
  set r := (C.O 1).radius with hrdef
  set o := (C.O 1).center with hodef
  set y := o.im with hydef
  have hu2 : (C.u.re - o.re) ^ 2 + y ^ 2 = r ^ 2 := by
    rw [← hu, Complex.sq_norm, Complex.normSq_apply]; simp [huim, hydef]; ring
  have hv2 : (C.v.re - o.re) ^ 2 + y ^ 2 = r ^ 2 := by
    rw [← hv, Complex.sq_norm, Complex.normSq_apply]; simp [hvim, hydef]; ring
  set p := C.v.re - o.re with hp
  have hup : C.u.re - o.re = -p := by
    have : (C.u.re - o.re) ^ 2 = p ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · exfalso; linarith
    · exact h
  have hp0 : 0 < p := by linarith
  have hyr : y ^ 2 < r ^ 2 := by nlinarith
  have hyr1 : -1 < y / r := by
    rw [lt_div_iff₀ hr]; nlinarith [abs_lt_of_sq_lt_sq' hyr hr.le]
  have hyr2 : y / r < 1 := by
    rw [div_lt_iff₀ hr]; nlinarith [abs_lt_of_sq_lt_sq' hyr hr.le]
  set γ := Real.arcsin (y / r) with hγ
  have hsin : Real.sin γ = y / r := Real.sin_arcsin hyr1.le hyr2.le
  have hcos : Real.cos γ = p / r := by
    rw [hγ, Real.cos_arcsin]
    have : 1 - (y / r) ^ 2 = (p / r) ^ 2 := by field_simp; linarith
    rw [this, Real.sqrt_sq (by positivity)]
  have hγ1 : -(Real.pi / 2) < γ := Real.neg_pi_div_two_lt_arcsin.2 hyr1
  have hγ2 : γ < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hyr2
  have hrs : r * Real.sin γ = y := by rw [hsin]; field_simp
  have hrc : r * Real.cos γ = p := by rw [hcos]; field_simp
  have hpi := Real.pi_pos
  -- the four angle parameters
  have hUu : (C.O 1).upperAngle C.u = Real.pi + γ := by
    unfold Disk.upperAngle
    rw [arg_eq_of_re_im _ r (Real.pi / 2 + γ) hr ⟨by linarith, by linarith⟩]
    · ring
    · simp [Real.cos_add, ← hodef, huim, ← hydef]; linarith
    · simp [Real.sin_add, ← hodef, huim, ← hydef]; linarith
  have hUv : (C.O 1).upperAngle C.v = -γ := by
    unfold Disk.upperAngle
    rw [arg_eq_of_re_im _ r (-(Real.pi / 2 + γ)) hr ⟨by linarith, by linarith⟩]
    · ring
    · simp [Real.cos_add, ← hodef, hvim, ← hydef]; linarith
    · simp [Real.sin_add, ← hodef, hvim, ← hydef]; linarith
  have hLu : (C.O 1).lowerAngle C.u = Real.pi + γ := by
    unfold Disk.lowerAngle
    rw [arg_eq_of_re_im _ r (γ - Real.pi / 2) hr ⟨by linarith, by linarith⟩]
    · ring
    · simp [Real.cos_sub, ← hodef, huim, ← hydef]; linarith
    · simp [Real.sin_sub, ← hodef, huim, ← hydef]; linarith
  have hLv : (C.O 1).lowerAngle C.v = 2 * Real.pi - γ := by
    unfold Disk.lowerAngle
    rw [arg_eq_of_re_im _ r (Real.pi / 2 - γ) hr ⟨by linarith, by linarith⟩]
    · ring
    · simp [Real.cos_sub, ← hodef, hvim, ← hydef]; linarith
    · simp [Real.sin_sub, ← hodef, hvim, ← hydef]; linarith
  have hA0 : C.A 0 = C.u := by simp [DiskChain.A]
  have hA1 : C.A 1 = C.v := by simp [DiskChain.A, hn]
  have hB0 : C.B 0 = C.u := by simp [DiskChain.B]
  have hB1 : C.B 1 = C.v := by simp [DiskChain.B, hn]
  refine ⟨hr, hγ1, hγ2, ?_, ?_, ?_, ?_⟩
  · rw [hγ, Real.arcsin_eq_zero_iff, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h hr.ne'
    · exact Or.inl
  · simp only [DiskChain.upperRail, Disk.upperArcLength, Nat.sub_self, hA0, hA1, hUu, hUv]
    ring
  · simp only [DiskChain.lowerRail, Disk.lowerArcLength, Nat.sub_self, hB0, hB1, hLu, hLv]
    ring
  · rw [Complex.dist_eq]
    have : C.u - C.v = ((-(2 * p) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; linarith
      · simp [huim, hvim]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), mul_assoc, hrc]
    ring

/-- Part 2: one-disk chains. -/
theorem one_disk_chain_bound (C : DiskChain) (hC : C.IsDiskChain) (hn : C.n = 1) :
    C.shortestPath ≤ Real.pi / 2 * dist C.u C.v ∧
      (C.shortestPath = Real.pi / 2 * dist C.u C.v ↔ (C.O 1).center.im = 0) := by
  obtain ⟨hr, hγ1, hγ2, hγ0, hα, hβ, hd⟩ := one_disk_chain_geometry C hC hn
  set r := (C.O 1).radius
  set γ := Real.arcsin ((C.O 1).center.im / (C.O 1).radius)
  have hpi := Real.pi_pos
  have hP : C.shortestPath = min (C.upperRail 1) (C.lowerRail 1) :=
    shortestPath_n_eq_one C hn (by rw [hα]; apply mul_nonneg hr.le; linarith)
      (by rw [hβ]; apply mul_nonneg hr.le; linarith)
  set t := Real.pi / 2 - |γ| with ht
  have habs : |γ| < Real.pi / 2 := abs_lt.2 ⟨hγ1, hγ2⟩
  have hmin : min (C.upperRail 1) (C.lowerRail 1) = 2 * r * t := by
    rw [hα, hβ, ht]
    rcases abs_cases γ with ⟨h, h0⟩ | ⟨h, h0⟩ <;> rw [h]
    · rw [min_eq_right (by nlinarith)]; ring
    · rw [min_eq_left (by nlinarith)]; ring
  have hcos : Real.cos γ = Real.sin t := by
    rw [ht, Real.sin_pi_div_two_sub, Real.cos_abs]
  obtain ⟨hJ, hJeq⟩ := jordan_two_mul_le_pi_mul_sin t (by linarith) (by linarith [abs_nonneg γ])
  rw [hP, hmin, hd, hcos, ← hγ0]
  refine ⟨by nlinarith, ?_⟩
  constructor
  · intro h
    have : 2 * t = Real.pi * Real.sin t := by
      have : r * (2 * t) = r * (Real.pi * Real.sin t) := by linarith
      exact mul_left_cancel₀ hr.ne' this
    have := hJeq.1 this
    exact abs_eq_zero.1 (by linarith)
  · intro h
    have : t = Real.pi / 2 := by rw [ht, h, abs_zero, sub_zero]
    rw [this, Real.sin_pi_div_two]; ring

/-- The unit-disk chain with ends `−1, 1`. -/
noncomputable def unitChain : DiskChain where
  n := 1
  O := fun _ => ⟨0, 1⟩
  u := -1
  v := 1
  a := fun _ => 0
  b := fun _ => 0

theorem unitChain_isDiskChain : unitChain.IsDiskChain := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ _; simp [unitChain]
  · simp [unitChain]
  · simp [unitChain]
  · simp [unitChain, Disk.boundary]
  · simp [unitChain, Disk.boundary]
  · simp [unitChain]
  · intro i h1 h2; simp [unitChain] at h2; omega
  · intro i h1 h2; simp [unitChain] at h2; omega
  · intro i h
    simp only [unitChain] at h
    obtain rfl : i = 0 := by omega
    simp [DiskChain.c, unitChain]
  · intro i h1 h2; simp [unitChain] at h2; omega

theorem solution :
    (∀ (o u v : ℂ) (r : ℝ), u ∈ Metric.sphere o r → v ∈ Metric.sphere o r → u ≠ v →
      r * EuclideanGeometry.angle u o v ≤ Real.pi / 2 * dist u v ∧
        (r * EuclideanGeometry.angle u o v = Real.pi / 2 * dist u v ↔
          EuclideanGeometry.angle u o v = Real.pi)) ∧
    (∀ C : DiskChain, C.IsDiskChain → C.n = 1 →
      C.shortestPath ≤ Real.pi / 2 * dist C.u C.v ∧
        (C.shortestPath = Real.pi / 2 * dist C.u C.v ↔ (C.O 1).center.im = 0)) ∧
    (∀ U : ℝ, ChainInequality U → Real.pi / 2 ≤ U) ∧
    (∀ U : ℝ, Real.pi / 2 ≤ U → ∀ C : DiskChain, C.IsDiskChain → C.n = 1 →
      C.shortestPath ≤ U * dist C.u C.v) := by
  refine ⟨one_circle_bound, one_disk_chain_bound, ?_, ?_⟩
  · intro U hU
    have h1 := hU unitChain unitChain_isDiskChain
    have h2 := (one_disk_chain_bound unitChain unitChain_isDiskChain rfl).2.2
      (by simp [unitChain])
    have hd : dist unitChain.u unitChain.v = 2 := by
      simp only [unitChain, Complex.dist_eq]
      norm_num
    rw [h2, hd] at h1
    linarith
  · intro U hU C hC hn
    have h := (one_disk_chain_bound C hC hn).1
    have : 0 ≤ dist C.u C.v := dist_nonneg
    nlinarith
