-- Prove2me | solution 1 for BrinSquier.bs12_no_zsq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T08:50:26.415443+00:00
-- url     : https://prove2.me/submissions/214fc2d4-ff7f-400f-afa4-5e1fc709301f

import Mathlib

namespace BS12Aux


/-! ## The ambient subgroup: slope a power of two, rational translation part -/

/-- Affine maps of the line with slope a power of two and rational translation part. -/
def AffD : Subgroup (ℝ ≃o ℝ) where
  carrier := {g | ∃ (n : ℤ) (b : ℚ), ∀ y : ℝ, g y = 2 ^ n * y + (b : ℝ)}
  one_mem' := ⟨0, 0, by intro y; simp⟩
  mul_mem' := by
    rintro g h ⟨n, b, hg⟩ ⟨m, c, hh⟩
    refine ⟨n + m, 2 ^ n * c + b, fun y => ?_⟩
    show g (h y) = _
    rw [hh y, hg]
    push_cast
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    ring
  inv_mem' := by
    rintro g ⟨n, b, hg⟩
    refine ⟨-n, -(2 ^ (-n) * b), fun y => ?_⟩
    have h2 : (2:ℝ) ^ n * (2:ℝ) ^ (-n) = 1 := by
      rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; simp
    have key : g (2 ^ (-n) * y + ((-(2 ^ (-n) * b) : ℚ) : ℝ)) = y := by
      rw [hg]; push_cast; linear_combination (y - (b:ℝ)) * h2
    exact g.injective ((RelIso.apply_inv_self g y).trans key.symm)

/-! ## Integer powers, in the two shapes an affine map can have -/

lemma trans_zpow {g : ℝ ≃o ℝ} {b : ℝ} (hg : ∀ y, g y = y + b) :
    ∀ (m : ℤ) (y : ℝ), (g ^ m) y = y + m * b := by
  have hinv : ∀ y, g⁻¹ y = y - b := by
    intro y
    have h2 : g (y - b) = y := by rw [hg]; ring
    exact g.injective ((RelIso.apply_inv_self g y).trans h2.symm)
  intro m
  induction m using Int.induction_on with
  | zero => intro y; simp
  | succ n ih =>
      intro y
      rw [zpow_add g (n:ℤ) 1, zpow_one]
      show (g ^ (n:ℤ)) (g y) = _
      rw [hg y, ih (y + b)]
      push_cast; ring
  | pred n ih =>
      intro y
      rw [show (-(n:ℤ) - 1) = (-(n:ℤ)) + (-1) by ring, zpow_add g (-(n:ℤ)) (-1), zpow_neg_one]
      show (g ^ (-(n:ℤ))) (g⁻¹ y) = _
      rw [hinv y, ih (y - b)]
      push_cast; ring

lemma fix_zpow {g : ℝ ≃o ℝ} {a p : ℝ} (ha : a ≠ 0) (hg : ∀ y, g y = a * (y - p) + p) :
    ∀ (m : ℤ) (y : ℝ), (g ^ m) y = a ^ m * (y - p) + p := by
  have hinv : ∀ y, g⁻¹ y = a⁻¹ * (y - p) + p := by
    intro y
    have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    have h2 : g (a⁻¹ * (y - p) + p) = y := by
      rw [hg]; linear_combination (y - p) * haa
    exact g.injective ((RelIso.apply_inv_self g y).trans h2.symm)
  intro m
  induction m using Int.induction_on with
  | zero => intro y; simp
  | succ n ih =>
      intro y
      rw [zpow_add g (n:ℤ) 1, zpow_one]
      show (g ^ (n:ℤ)) (g y) = _
      rw [hg y, ih (a * (y - p) + p)]
      rw [zpow_add₀ ha (n:ℤ) 1, zpow_one]
      ring
  | pred n ih =>
      intro y
      rw [show (-(n:ℤ) - 1) = (-(n:ℤ)) + (-1) by ring, zpow_add g (-(n:ℤ)) (-1), zpow_neg_one]
      show (g ^ (-(n:ℤ))) (g⁻¹ y) = _
      rw [hinv y, ih (a⁻¹ * (y - p) + p)]
      rw [zpow_add₀ ha (-(n:ℤ)) (-1), zpow_neg_one]
      ring

/-! ## Two small facts -/

lemma two_zpow_ne_one {j : ℤ} (hj : j ≠ 0) : (2:ℝ) ^ j ≠ 1 := by
  intro h
  have h1 : (j:ℝ) * Real.log 2 = 0 := by
    rw [← Real.log_zpow, h, Real.log_one]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h3 : (j:ℝ) = 0 := by
    rcases mul_eq_zero.1 h1 with h4 | h4
    · exact h4
    · exact absurd h4 h2
  exact hj (by exact_mod_cast h3)

/-- Commuting maps share the fixed point of an affine map whose slope is not one. -/
lemma common_fix {g h : ℝ ≃o ℝ} (hcomm : g * h = h * g) {a b : ℝ}
    (hg : ∀ y, g y = a * y + b) (ha : a ≠ 1) : ∃ r, g r = r ∧ h r = r := by
  have hsub : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  set r := b / (1 - a) with hr
  have hgr : g r = r := by
    rw [hg, hr]; field_simp; ring
  have huniq : ∀ q, g q = q → q = r := by
    intro q hq
    rw [hg] at hq
    have hq2 : q * (1 - a) = b := by linarith
    rw [hr, eq_div_iff hsub]
    exact hq2
  refine ⟨r, hgr, ?_⟩
  have : g (h r) = h r := by
    have e1 : (g * h) r = (h * g) r := by rw [hcomm]
    show g (h r) = h r
    calc g (h r) = (g * h) r := rfl
      _ = (h * g) r := e1
      _ = h (g r) := rfl
      _ = h r := by rw [hgr]
  exact huniq _ this

/-! ## Denominators -/

lemma den_mul_self (r : ℚ) : ((r.den : ℚ)) * r = (r.num : ℚ) := by
  have hd : ((r.den : ℚ)) ≠ 0 := by exact_mod_cast r.den_ne_zero
  calc ((r.den : ℚ)) * r = (r.den : ℚ) * ((r.num : ℚ) / (r.den : ℚ)) := by rw [r.num_div_den]
    _ = (r.num : ℚ) := by field_simp

lemma den_mul_selfR (r : ℚ) : ((r.den : ℝ)) * (r : ℝ) = ((r.num : ℝ)) := by
  have := den_mul_self r; exact_mod_cast this

/-! ## The two cases -/

/-- Two commuting maps that fix a common point and have slopes `2^j`, `2^k` there satisfy
the relation `u ^ k * v ^ (-j) = 1`. -/
lemma one_of_common_fix {u v : ℝ ≃o ℝ} {j k : ℤ} {r : ℝ}
    (hu : ∀ y, u y = 2 ^ j * (y - r) + r) (hv : ∀ y, v y = 2 ^ k * (y - r) + r) :
    u ^ k * v ^ (-j) = 1 := by
  have h2 : (2:ℝ) ≠ 0 := by norm_num
  have e1 := fix_zpow (zpow_ne_zero j h2) hu k
  have e2 := fix_zpow (zpow_ne_zero k h2) hv (-j)
  have hcancel : ((2:ℝ) ^ j) ^ k * ((2:ℝ) ^ k) ^ (-j) = 1 := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ h2, show j * k + k * (-j) = 0 by ring, zpow_zero]
  apply RelIso.ext
  intro y
  show (u ^ k) ((v ^ (-j)) y) = y
  rw [e2 y, e1]
  linear_combination (y - r) * hcancel

end BS12Aux

open BS12Aux

theorem solution
    (M T : ℝ ≃o ℝ) (hM : ∀ y : ℝ, M y = 2 * y) (hT : ∀ y : ℝ, T y = y + 1) :
    ¬ ∃ u ∈ Subgroup.closure ({M, T} : Set (ℝ ≃o ℝ)),
        ∃ v ∈ Subgroup.closure ({M, T} : Set (ℝ ≃o ℝ)),
          u * v = v * u ∧
            Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  have hsub : ({M, T} : Set (ℝ ≃o ℝ)) ⊆ (AffD : Set (ℝ ≃o ℝ)) := by
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨1, 0, fun y => by rw [hM]; push_cast; rw [zpow_one]; ring⟩
    · exact ⟨0, 1, fun y => by rw [hT]; push_cast; ring⟩
  have hle : Subgroup.closure ({M, T} : Set (ℝ ≃o ℝ)) ≤ AffD :=
    (Subgroup.closure_le _).2 hsub
  rintro ⟨u, hu, v, hv, hcomm, hinj⟩
  obtain ⟨j, b, hub⟩ := hle hu
  obtain ⟨k, d, hvd⟩ := hle hv
  suffices hkey : ∃ q : ℤ × ℤ, q ≠ (0, 0) ∧ u ^ q.1 * v ^ q.2 = 1 by
    obtain ⟨q, hq0, hq⟩ := hkey
    exact hq0 (hinj (by simpa using hq))
  -- turn a common fixed point into the relation
  have caseB : ∀ r : ℝ, u r = r → v r = r → ∃ q : ℤ × ℤ, q = (k, -j) ∧ u ^ q.1 * v ^ q.2 = 1 := by
    intro r hur hvr
    have hu2 : ∀ y : ℝ, u y = 2 ^ j * (y - r) + r := by
      intro y
      have hfix : (2:ℝ) ^ j * r + (b:ℝ) = r := by rw [← hub]; exact hur
      rw [hub]; linear_combination hfix
    have hv2 : ∀ y : ℝ, v y = 2 ^ k * (y - r) + r := by
      intro y
      have hfix : (2:ℝ) ^ k * r + (d:ℝ) = r := by rw [← hvd]; exact hvr
      rw [hvd]; linear_combination hfix
    exact ⟨(k, -j), rfl, one_of_common_fix hu2 hv2⟩
  by_cases hj : j = 0
  · by_cases hk : k = 0
    · -- both are translations, by rationals
      have hu1 : ∀ y : ℝ, u y = y + (b:ℝ) := by
        intro y; rw [hub, hj]; norm_num
      have hv1 : ∀ y : ℝ, v y = y + (d:ℝ) := by
        intro y; rw [hvd, hk]; norm_num
      by_cases hb : b = 0
      · refine ⟨(1, 0), by simp, ?_⟩
        have hu0 : u = 1 := by
          apply RelIso.ext; intro y; rw [hu1, hb]; norm_num
        simp [hu0]
      · refine ⟨(d.num * b.den, -(b.num * d.den)), ?_, ?_⟩
        · intro hcon
          have hne : (-(b.num * (b.den : ℤ))) ≠ 0 := by
            simp only [neg_ne_zero, mul_ne_zero_iff]
            exact ⟨Rat.num_ne_zero.2 hb, by exact_mod_cast b.den_ne_zero⟩
          have h2 : -(b.num * (d.den : ℤ)) = 0 := congrArg Prod.snd hcon
          simp only [neg_eq_zero, mul_eq_zero] at h2
          rcases h2 with h3 | h3
          · exact hb (Rat.num_eq_zero.1 h3)
          · exact d.den_ne_zero (by exact_mod_cast h3)
        · have key : ((d.num : ℝ) * (b.den : ℝ)) * (b:ℝ)
              + (-((b.num : ℝ) * (d.den : ℝ))) * (d:ℝ) = 0 := by
            linear_combination (d.num : ℝ) * den_mul_selfR b - (b.num : ℝ) * den_mul_selfR d
          apply RelIso.ext
          intro y
          show (u ^ (d.num * b.den)) ((v ^ (-(b.num * d.den))) y) = y
          rw [trans_zpow hv1, trans_zpow hu1]
          push_cast
          linarith [key]
    · -- j = 0, k ≠ 0 : v has a unique fixed point and u shares it
      obtain ⟨r, hvr, hur⟩ := common_fix hcomm.symm hvd (two_zpow_ne_one hk)
      obtain ⟨q, hq, hq1⟩ := caseB r hur hvr
      refine ⟨q, ?_, hq1⟩
      rw [hq]
      intro hcon
      exact hk (congrArg Prod.fst hcon)
  · -- j ≠ 0 : u has a unique fixed point and v shares it
    obtain ⟨r, hur, hvr⟩ := common_fix hcomm hub (two_zpow_ne_one hj)
    obtain ⟨q, hq, hq1⟩ := caseB r hur hvr
    refine ⟨q, ?_, hq1⟩
    rw [hq]
    intro hcon
    exact hj (by simpa using congrArg Prod.snd hcon)
