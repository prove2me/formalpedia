-- Prove2me | solution 1 for EllipsoidGLS.Rounded.theorem_2_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:45:39.170435+00:00
-- url     : https://prove2.me/submissions/8648bf62-e0e3-4ac6-9a23-2fe241860149
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run
import Theorems.Thm_EllipsoidGLS_Rounded_eq_32
import Theorems.Thm_EllipsoidGLS_Rounded_eq_34

open Matrix

namespace EllRndScratch

open EllipsoidGLS.Rounded

open EllipsoidGLS.Rounded

lemma inv_smul_one {m : ℕ} (s : ℝ) (hs : s ≠ 0) :
    (s • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ = s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs, one_smul]

lemma unitBall_eq (m : ℕ) :
    LinearOptimization.ellipsoidBall (0 : Fin m → ℝ) 1 =
      {x : Fin m → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ 1} := by
  ext x
  simp only [LinearOptimization.ellipsoidBall, LinearOptimization.ellipsoid, Set.mem_ofPred_eq,
    one_pow, one_smul, inv_one, one_mulVec, sub_zero]
  have h1 : ∀ i, |x i| ^ (2 : ℝ) = x i * x i := by
    intro i; rw [Real.rpow_two, sq_abs, sq]
  simp only [h1, dotProduct]
  have h0 : 0 ≤ ∑ i, x i * x i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  constructor
  · intro h; exact Real.rpow_le_one h0 h (by norm_num)
  · intro h
    by_contra hc
    push Not at hc
    have := Real.one_lt_rpow hc (by norm_num : (0:ℝ) < 1 / 2)
    linarith

lemma unitBallVol_eq (m : ℕ) (hm : 1 ≤ m) :
    unitBallVol m = Real.sqrt Real.pi ^ m / Real.Gamma (m / 2 + 1) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold unitBallVol
  rw [unitBall_eq, MeasureTheory.volume_sum_rpow_le (ι := Fin m) (p := 2) (by norm_num) 1]
  have hG : 2 * Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  rw [hG, ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

lemma unitBallVol_pos (m : ℕ) (hm : 1 ≤ m) : 0 < unitBallVol m := by
  rw [unitBallVol_eq m hm]
  have : 0 < Real.Gamma (m / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  positivity

lemma unitBallVol_succ_le (m : ℕ) (hm : 1 ≤ m) :
    unitBallVol (m + 1) ≤ 2 * unitBallVol m := by
  rw [unitBallVol_eq m hm, unitBallVol_eq (m + 1) (by omega)]
  set x : ℝ := ((m : ℝ) + 1) / 2 with hx
  have hxpos : 0 < x := by positivity
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hx]; linarith
  -- Γ(x + 1/2) ≤ √x Γ(x) by log-convexity
  have hlc := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hxpos (by linarith : 0 < x + 1)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have harg : 1 / 2 * x + 1 / 2 * (x + 1) = (m : ℝ) / 2 + 1 := by rw [hx]; ring
  rw [harg, Real.Gamma_add_one hxpos.ne'] at hlc
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hxpos
  rw [Real.mul_rpow hxpos.le hGx.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hlc
  have hsimp : √(Real.Gamma x) * (√x * √(Real.Gamma x)) = √x * Real.Gamma x := by
    rw [mul_comm, mul_assoc, Real.mul_self_sqrt hGx.le]
  rw [hsimp] at hlc
  -- hlc : Γ(m/2+1) ≤ √x * Γ x
  have hcast : ((m + 1 : ℕ) : ℝ) / 2 + 1 = x + 1 := by push_cast; rw [hx]
  rw [hcast, Real.Gamma_add_one hxpos.ne']
  have hGm : 0 < Real.Gamma ((m : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [div_le_iff₀ (by positivity), pow_succ]
  -- goal: √π^m * √π ≤ 2 * (√π^m / Γ(m/2+1)) * (x * Γ x)
  have hsx : Real.sqrt Real.pi * Real.sqrt x ≤ 2 * x := by
    rw [← Real.sqrt_mul Real.pi_pos.le]
    rw [Real.sqrt_le_left (by linarith)]
    have : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith
  have hpm : 0 < Real.sqrt Real.pi ^ m := by positivity
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hGm]
  calc Real.sqrt Real.pi ^ m * Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2 + 1)
      ≤ Real.sqrt Real.pi ^ m * Real.sqrt Real.pi * (Real.sqrt x * Real.Gamma x) := by
        gcongr
    _ = Real.sqrt Real.pi ^ m * (Real.sqrt Real.pi * Real.sqrt x) * Real.Gamma x := by ring
    _ ≤ Real.sqrt Real.pi ^ m * (2 * x) * Real.Gamma x := by gcongr
    _ = 2 * Real.sqrt Real.pi ^ m * (x * Real.Gamma x) := by ring


lemma euclNorm_sq {m : ℕ} (v : Fin m → ℝ) : euclNorm v ^ 2 = v ⬝ᵥ v := by
  unfold euclNorm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i)))

lemma euclNorm_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ euclNorm v := Real.sqrt_nonneg _

lemma dot_le_euclNorm {m : ℕ} (u v : Fin m → ℝ) : u ⬝ᵥ v ≤ euclNorm u * euclNorm v := by
  have hcs : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    simpa [dotProduct, sq] using this
  have h1 : |u ⬝ᵥ v| ≤ Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := Real.abs_le_sqrt hcs
  have hu0 : (0:ℝ) ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  rw [Real.sqrt_mul hu0] at h1
  unfold euclNorm
  exact (le_abs_self _).trans h1

lemma mem_ball_iff {m : ℕ} (a z : Fin m → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    z ∈ LinearOptimization.ellipsoidBall a ρ ↔ (z - a) ⬝ᵥ (z - a) ≤ ρ ^ 2 := by
  simp only [LinearOptimization.ellipsoidBall, LinearOptimization.ellipsoid, Set.mem_ofPred_eq]
  rw [inv_smul_one _ (by positivity), smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    inv_mul_le_iff₀ (by positivity), mul_one]

lemma key {n : ℕ} (hn : 2 ≤ n) (V1 Vn r R nc ε D s E : ℝ)
    (hV1 : 0 < V1) (hVn : Vn ≤ 2 * V1) (hr : 0 < r) (hrR : r ≤ R) (hnc : 0 < nc)
    (hε : 0 < ε) (hD : 0 < D) (hDle : D ≤ R * nc) (hs : 0 ≤ s) (hE0 : 0 ≤ E)
    (hE : E ≤ (r * ε / (2 * R ^ 2 * nc)) ^ n)
    (hF : V1 * r ^ (n - 1) * D / (n * nc) * (s / D) ^ n ≤ E * (R ^ n * Vn)) :
    s ≤ ε := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hF
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hR0 : R ≠ 0 := hR.ne'
  have hD0 : D ≠ 0 := hD.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have hnc0 : nc ≠ 0 := hnc.ne'
  have heq : V1 * r ^ m * D / (((m + 1 : ℕ) : ℝ) * nc) * (s / D) ^ (m + 1) =
      V1 * r ^ m * s ^ (m + 1) / (((m + 1 : ℕ) : ℝ) * nc * D ^ m) := by
    rw [div_pow, pow_succ D]
    field_simp
  rw [heq, div_le_iff₀ (by positivity)] at hF
  set Y := r * ε / (2 * R ^ 2 * nc) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hYR : Y * (R * nc) = r * ε / (2 * R) := by
    rw [hY]; field_simp
  have hmain : V1 * r ^ m * s ^ (m + 1) ≤
      V1 * r ^ m * (2 * ((m : ℝ) + 1) * r * ε ^ (m + 1) / (2 ^ (m + 1) * R)) := by
    calc V1 * r ^ m * s ^ (m + 1)
        ≤ E * (R ^ (m + 1) * Vn) * (((m + 1 : ℕ) : ℝ) * nc * D ^ m) := hF
      _ ≤ Y ^ (m + 1) * (R ^ (m + 1) * (2 * V1)) * (((m + 1 : ℕ) : ℝ) * nc * (R * nc) ^ m) := by
          have hVn0 : 0 ≤ Vn ∨ Vn < 0 := le_or_gt 0 Vn
          rcases hVn0 with hVn0 | hVn0
          · gcongr
          · have : E * (R ^ (m + 1) * Vn) * (((m + 1 : ℕ) : ℝ) * nc * D ^ m) ≤ 0 := by
              have : R ^ (m + 1) * Vn ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hVn0.le
              have h2 : E * (R ^ (m + 1) * Vn) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hE0 this
              exact mul_nonpos_of_nonpos_of_nonneg h2 (by positivity)
            exact this.trans (by positivity)
      _ = 2 * V1 * ((m : ℝ) + 1) * (Y * (R * nc)) ^ (m + 1) * R ^ m := by push_cast; ring
      _ = 2 * V1 * ((m : ℝ) + 1) * (r * ε / (2 * R)) ^ (m + 1) * R ^ m := by rw [hYR]
      _ = V1 * r ^ m * (2 * ((m : ℝ) + 1) * r * ε ^ (m + 1) / (2 ^ (m + 1) * R)) := by
          rw [div_pow, mul_pow, mul_pow, pow_succ R, pow_succ (2:ℝ), pow_succ r]
          field_simp
  have hs1 := le_of_mul_le_mul_left hmain (by positivity)
  have h2m : 2 * ((m : ℝ) + 1) ≤ 2 ^ (m + 1) := by
    have : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
    have : ((m : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast this
    rw [pow_succ]; linarith
  have h3 : 2 * ((m : ℝ) + 1) * r * ε ^ (m + 1) / (2 ^ (m + 1) * R) ≤ ε ^ (m + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * ((m : ℝ) + 1) * r ≤ 2 ^ (m + 1) * R :=
      mul_le_mul h2m hrR hr.le (by positivity)
    have he : 0 ≤ ε ^ (m + 1) := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ hs hε.le (by omega)).1 (hs1.trans h3)

end EllRndScratch

open EllRndScratch EllipsoidGLS.Rounded

theorem solution
    {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (a₀ c : Fin n → ℝ) (r R ε : ℝ)
    (hK : IsConvexBody K a₀ r R) (hc : 1 ≤ euclNorm c) (hε : 0 < ε) (hεr : ε < r)
    (hR : 1 ≤ R)
    (hε1 : ε ≤ 1)
    (N : ℕ) (hN : N = itN n R r ε c)
    (x : ℕ → Fin n → ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (feas : ℕ → Prop)
    (a d : ℕ → Fin n → ℝ)
    (hrun : IsRoundedRun K c a₀ R (itDelta n N R) (itP N) N x A feas a d)
    (j : ℕ) (_hj : j < N) (_hfj : feas j)
    (hmax : ∀ k < N, feas k → c ⬝ᵥ x k ≤ c ⬝ᵥ x j) :
    ∀ y ∈ K, c ⬝ᵥ y - ε ≤ c ⬝ᵥ x j := by
  have hK' := hK
  obtain ⟨hconv, _hcomp, hr, hrR, hball_in, hK_in⟩ := hK
  have hRpos : 0 < R := lt_of_lt_of_le hr hrR
  set nc := euclNorm c with hnc_def
  have hncpos : 0 < nc := by linarith
  have hc0 : c ≠ 0 := by
    intro h
    have : nc = 0 := by rw [hnc_def, h]; simp [euclNorm]
    linarith
  have hcc : c ⬝ᵥ c = nc ^ 2 := (euclNorm_sq c).symm
  -- E ≤ Y^n
  have hX : 0 < 2 * R ^ 2 * nc / (r * ε) := by positivity
  have hE : Real.exp (-(N : ℝ) / (4 * (n : ℝ))) ≤ (r * ε / (2 * R ^ 2 * nc)) ^ n := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    set L : ℕ := ⌈Real.log (2 * R ^ 2 * nc / (r * ε))⌉₊ with hL
    have hNcast : (N : ℝ) = 4 * (n : ℝ) ^ 2 * L := by
      rw [hN]; unfold itN; push_cast; rfl
    have h1 : -(N : ℝ) / (4 * (n : ℝ)) = (n : ℝ) * (-(L : ℝ)) := by
      rw [hNcast]; field_simp
    rw [h1, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    have hlog : Real.log (2 * R ^ 2 * nc / (r * ε)) ≤ L := Nat.le_ceil _
    calc Real.exp (-(L : ℝ)) ≤ Real.exp (-Real.log (2 * R ^ 2 * nc / (r * ε))) :=
          Real.exp_le_exp.2 (by linarith)
      _ = r * ε / (2 * R ^ 2 * nc) := by
          rw [Real.exp_neg, Real.exp_log hX, inv_div]
  have hx0 : x 0 = a₀ := hrun.1
  have claim : ∀ y ∈ K, c ⬝ᵥ a₀ + r * nc ≤ c ⬝ᵥ y → c ⬝ᵥ y - ε ≤ c ⬝ᵥ x j := by
    intro y hy hyc
    by_contra hcon
    push Not at hcon
    set t := max (c ⬝ᵥ x j) (c ⬝ᵥ a₀) with ht
    have hrnc : r ≤ r * nc := by nlinarith
    have hD : 0 < c ⬝ᵥ y - c ⬝ᵥ a₀ := by nlinarith
    have hDle : c ⬝ᵥ y - c ⬝ᵥ a₀ ≤ R * nc := by
      have hyb := (mem_ball_iff a₀ y R hRpos).1 (hK_in hy)
      have h1 : euclNorm (y - a₀) ≤ R := by
        have := euclNorm_sq (y - a₀)
        have h0 := euclNorm_nonneg (y - a₀)
        nlinarith
      rw [← dotProduct_sub]
      calc c ⬝ᵥ (y - a₀) ≤ nc * euclNorm (y - a₀) := dot_le_euclNorm c (y - a₀)
        _ ≤ nc * R := by gcongr
        _ = R * nc := by ring
    have ht0 : c ⬝ᵥ a₀ ≤ t := le_max_right _ _
    have ht1 : t ≤ c ⬝ᵥ y := max_le (by linarith) (by linarith)
    have hst : ε < c ⬝ᵥ y - t := by
      have : t < c ⬝ᵥ y - ε := max_lt hcon (by linarith)
      linarith
    have hdisc : {z | euclNorm (z - a₀) ≤ r ∧ c ⬝ᵥ z = c ⬝ᵥ a₀} ⊆ K := by
      intro z hz
      apply hball_in
      rw [mem_ball_iff a₀ z r hr, ← euclNorm_sq]
      exact pow_le_pow_left₀ (euclNorm_nonneg _) hz.1 2
    have h34 := eq_34 hn K hconv c a₀ y hc0 r hr hdisc hy (by linarith) t ht0 ht1
    have h32 := eq_32 hn K a₀ c r R ε hK' hc hε hεr hR hε1 N hN x A feas a d hrun
    rw [hx0] at h32
    have hsub : {z | z ∈ K ∧ t ≤ c ⬝ᵥ z} ⊆ Kk K c x feas N := fun z hz =>
      ⟨hz.1, fun k hk hfk => (hmax k hk hfk).trans ((le_max_left _ _).trans hz.2)⟩
    have hchain := h34.trans ((MeasureTheory.measure_mono hsub).trans
      (h32.1.trans h32.2.1))
    rw [h32.2.2, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hchain
    have hV1 := unitBallVol_pos (n - 1) (by omega)
    have hVn : unitBallVol n ≤ 2 * unitBallVol (n - 1) := by
      have := unitBallVol_succ_le (n - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this
    have hVn0 : 0 ≤ unitBallVol n := ENNReal.toReal_nonneg
    have hF := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
    have := key hn (unitBallVol (n - 1)) (unitBallVol n) r R nc ε (c ⬝ᵥ y - c ⬝ᵥ a₀)
      (c ⬝ᵥ y - t) _ hV1 hVn hr hrR hncpos hε hD hDle (by linarith) (Real.exp_pos _).le hE hF
    linarith
  intro y hy
  set u : Fin n → ℝ := a₀ + (r / nc) • c with hu
  have hcu : c ⬝ᵥ u = c ⬝ᵥ a₀ + r * nc := by
    rw [hu, dotProduct_add, dotProduct_smul, smul_eq_mul, hcc]
    field_simp
  have huK : u ∈ K := by
    apply hball_in
    rw [mem_ball_iff a₀ u r hr, hu, add_sub_cancel_left, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, hcc]
    field_simp
    exact le_refl _
  by_cases hyc : c ⬝ᵥ a₀ + r * nc ≤ c ⬝ᵥ y
  · exact claim y hy hyc
  · push Not at hyc
    have := claim u huK hcu.ge
    linarith
