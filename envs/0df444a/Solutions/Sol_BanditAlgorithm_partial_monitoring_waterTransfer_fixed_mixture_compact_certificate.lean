-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T20:03:42.64826+00:00
-- url     : https://prove2.me/submissions/34caab1a-0475-40a2-9496-933e33af9a2d

import Theorems.Thm_BanditAlgorithm_waterTransfer_distribution_of_ancestor_sets
import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

set_option autoImplicit false

/-! The analytic part of Lattimore--Szepesvári, Theorem 37.17,
printed pp. 501--502.  The hypotheses below are precisely what the monotone
in-tree of Lemma 37.21 and the path-sum of local estimators provide. -/

theorem partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (q : Fin k → ℝ) (hq : PMSupportedOn S q)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d))
    (anc : Fin k → Finset (Fin k))
    (hself : ∀ b, b ∈ anc b)
    (htrans : ∀ a b, a ∈ anc b → ∀ c, b ∈ anc c → a ∈ anc c)
    (f₀ : Fin k → 𝕊 → Fin k → ℝ)
    (hfvec : PMVectorEstimatorOn G S f₀)
    (V : ℝ) (hV : 0 ≤ V)
    (hfbound : ∀ a σ b, |f₀ a σ b| ≤ V)
    (hfsupp : ∀ a σ b, f₀ a σ b ≠ 0 → a ∈ anc b)
    (hloss : ∀ a b, a ∈ anc b →
      ∑ i : Fin d, G.L a i * lam i ≤ ∑ i : Fin d, G.L b i * lam i)
    (η : ℝ) (hη : 0 < η)
    (hηsmall : η * ((k : ℝ) * max 1 V) ≤ 1 / 2) :
    ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
      PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
      (∀ a, η * max 1 V ≤ p a) ∧
      (∀ a σ b, |f a σ b| ≤ V) ∧
      (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
      (∀ i : Fin d,
        ∑ a : Fin k, p a *
          (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
            η ^ 2 * (2 * (k : ℝ) ^ 3 * (max 1 V) ^ 2)) ∧
      ∑ i : Fin d, lam i * (∑ a : Fin k, (p a - q a) * G.L a i) ≤
        η * ((k : ℝ) * max 1 V) := by
  classical
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  let W : ℝ := max 1 V
  have hW1 : 1 ≤ W := le_max_left _ _
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW1
  have hVW : V ≤ W := le_max_right _ _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  let γ : ℝ := η * ((k : ℝ) * W)
  have hγpos : 0 < γ := by dsimp [γ]; positivity
  have hγle : γ ≤ 1 / 2 := by simpa [γ, W] using hηsmall
  have hγone : γ ≤ 1 := hγle.trans (by norm_num)
  have hone_sub_γ : 0 ≤ 1 - γ := sub_nonneg.mpr hγone
  have hone_sub_γ_half : 1 / 2 ≤ 1 - γ := by linarith
  obtain ⟨r, hr, hqr, hrmono, hry⟩ :=
    waterTransfer_distribution_of_ancestor_sets hkpos q hq.1 anc hself
      (fun a b ↦ a ∈ anc b) htrans
  let u : Fin k → ℝ := fun _ ↦ 1 / k
  have hu : u ∈ stdSimplex ℝ (Fin k) := by
    constructor
    · intro a
      dsimp [u]
      positivity
    · simp [u, hkpos.ne']
  let p : Fin k → ℝ := fun a ↦ (1 - γ) * r a + γ * u a
  have hp_simplex : p ∈ stdSimplex ℝ (Fin k) := by
    constructor
    · intro a
      dsimp [p]
      exact add_nonneg (mul_nonneg hone_sub_γ (hr.1 a))
        (mul_nonneg hγpos.le (hu.1 a))
    · dsimp [p]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr.2, hu.2]
      ring
  have hp_unif (a : Fin k) : γ / k ≤ p a := by
    dsimp [p, u]
    calc
      γ / (k : ℝ) = γ * (1 / (k : ℝ)) := by ring
      _ ≤ (1 - γ) * r a + γ * (1 / (k : ℝ)) :=
        le_add_of_nonneg_left (mul_nonneg hone_sub_γ (hr.1 a))
  have hp_pos (a : Fin k) : 0 < p a :=
    lt_of_lt_of_le (div_pos hγpos hkR) (hp_unif a)
  have hp_r (a : Fin k) : r a / 2 ≤ p a := by
    dsimp [p]
    have hrr : r a / 2 ≤ (1 - γ) * r a := by
      nlinarith [hr.1 a]
    exact hrr.trans (le_add_of_nonneg_right (mul_nonneg hγpos.le (hu.1 a)))
  refine ⟨p, f₀, ⟨hp_simplex, hp_pos⟩, hfvec, ?_, hfbound, ?_, ?_, ?_⟩
  · intro a
    calc
      η * max 1 V = γ / k := by field_simp [γ, W, hkR.ne']; ring
      _ ≤ p a := hp_unif a
  · intro a σ b
    have hfneg : -V ≤ f₀ a σ b := (abs_le.mp (hfbound a σ b)).1
    have hden : η * V ≤ p a := by
      calc
        η * V ≤ η * W := mul_le_mul_of_nonneg_left hVW hη.le
        _ = γ / k := by field_simp [γ, hkR.ne']; ring
        _ ≤ p a := hp_unif a
    apply (le_div_iff₀ (hp_pos a)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hfneg hη.le]
  · intro i
    have hterm (a b : Fin k) :
        p a * (q b * (η * f₀ a (G.Φ a i) b / p a) ^ 2) ≤
          η ^ 2 * (2 * (k : ℝ) * W ^ 2) := by
      by_cases hfzero : f₀ a (G.Φ a i) b = 0
      · simp [hfzero]
        positivity
      · have hab : a ∈ anc b := hfsupp a (G.Φ a i) b hfzero
        have hrba : r b ≤ r a := hrmono a b hab
        have hqb : q b ≤ (k : ℝ) * r b := by
          have := hqr b
          have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
          rw [div_le_iff₀ hkR] at this
          simpa [mul_comm] using this
        have hqpa : q b ≤ 2 * (k : ℝ) * p a := by
          have hra : r a ≤ 2 * p a := by linarith [hp_r a]
          nlinarith [hr.1 b, hr.1 a]
        have hf2 : (f₀ a (G.Φ a i) b) ^ 2 ≤ W ^ 2 := by
          have habs := hfbound a (G.Φ a i) b
          have hfaW : |f₀ a (G.Φ a i) b| ≤ W := habs.trans hVW
          have hprod : 0 ≤
              (W - |f₀ a (G.Φ a i) b|) * (W + |f₀ a (G.Φ a i) b|) :=
            mul_nonneg (sub_nonneg.mpr hfaW)
              (add_nonneg hWpos.le (abs_nonneg _))
          nlinarith [sq_abs (f₀ a (G.Φ a i) b)]
        have hqnonneg : 0 ≤ q b := hq.1.1 b
        have hratio : q b / p a ≤ 2 * (k : ℝ) := by
          rw [div_le_iff₀ (hp_pos a)]
          simpa [mul_assoc, mul_left_comm, mul_comm] using hqpa
        have hratio0 : 0 ≤ q b / p a := div_nonneg hqnonneg (hp_pos a).le
        calc
          p a * (q b * (η * f₀ a (G.Φ a i) b / p a) ^ 2) =
              η ^ 2 * ((q b / p a) * (f₀ a (G.Φ a i) b) ^ 2) := by
                field_simp [ne_of_gt (hp_pos a)]
          _ ≤ η ^ 2 * ((2 * (k : ℝ)) * W ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hratio hf2 (sq_nonneg _)
                (by positivity : 0 ≤ 2 * (k : ℝ))) (sq_nonneg η)
          _ = η ^ 2 * (2 * (k : ℝ) * W ^ 2) := by ring
    calc
      (∑ a : Fin k, p a *
          (∑ b : Fin k, q b * (η * f₀ a (G.Φ a i) b / p a) ^ 2)) =
          ∑ a : Fin k, ∑ b : Fin k,
            p a * (q b * (η * f₀ a (G.Φ a i) b / p a) ^ 2) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
      _ ≤ ∑ _a : Fin k, ∑ _b : Fin k,
          η ^ 2 * (2 * (k : ℝ) * W ^ 2) := by
            exact Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hterm a b
      _ = η ^ 2 * (2 * (k : ℝ) ^ 3 * W ^ 2) := by
            simp [pow_succ]
            ring
  · let y : Fin k → ℝ := fun a ↦ ∑ i : Fin d, G.L a i * lam i
    have hryNeg := hry (fun a ↦ -y a) (fun a b hab ↦ neg_le_neg (hloss a b hab))
    have hry' : ∑ a : Fin k, r a * y a ≤ ∑ b : Fin k, q b * y b := by
      have hqneg : ∑ b : Fin k, q b * (-y b) = -(∑ b : Fin k, q b * y b) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      have hrneg : ∑ a : Fin k, r a * (-y a) = -(∑ a : Fin k, r a * y a) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      rw [hqneg, hrneg] at hryNeg
      linarith
    have hy_nonneg (a : Fin k) : 0 ≤ y a := by
      dsimp [y]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hL a i).1 (hlam.1 i)
    have hy_le_one (a : Fin k) : y a ≤ 1 := by
      calc
        y a ≤ ∑ i : Fin d, 1 * lam i := by
          dsimp [y]
          exact Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_right (hL a i).2 (hlam.1 i)
        _ = 1 := by simp [hlam.2]
    have hu_y : ∑ a : Fin k, u a * y a ≤ 1 := by
      calc
        ∑ a : Fin k, u a * y a ≤ ∑ a : Fin k, u a * 1 := by
          exact Finset.sum_le_sum fun a _ ↦
            mul_le_mul_of_nonneg_left (hy_le_one a) (hu.1 a)
        _ = 1 := by simp [hu.2]
    have hq_y_nonneg : 0 ≤ ∑ a : Fin k, q a * y a := by
      apply Finset.sum_nonneg
      intro a ha
      exact mul_nonneg (hq.1.1 a) (hy_nonneg a)
    have hmain :
        ∑ a : Fin k, (p a - q a) * y a ≤ γ := by
      dsimp [p]
      calc
        ∑ a : Fin k, (((1 - γ) * r a + γ * u a) - q a) * y a =
            (1 - γ) * (∑ a : Fin k, r a * y a - ∑ a : Fin k, q a * y a) +
              γ * (∑ a : Fin k, u a * y a - ∑ a : Fin k, q a * y a) := by
                simp only [sub_mul, add_mul, Finset.sum_add_distrib,
                  Finset.sum_sub_distrib]
                rw [show (∑ x : Fin k, γ * r x * y x) =
                    γ * ∑ x : Fin k, r x * y x by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring]
                rw [show (∑ x : Fin k, γ * u x * y x) =
                    γ * ∑ x : Fin k, u x * y x by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring]
                ring
        _ ≤ γ := by
          have hfirst : ∑ a : Fin k, r a * y a - ∑ a : Fin k, q a * y a ≤ 0 :=
            sub_nonpos.mpr hry'
          have hsecond : ∑ a : Fin k, u a * y a - ∑ a : Fin k, q a * y a ≤ 1 := by
            linarith
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hone_sub_γ hfirst,
            mul_le_mul_of_nonneg_left hsecond hγpos.le]
    calc
      ∑ i : Fin d, lam i * (∑ a : Fin k, (p a - q a) * G.L a i) =
          ∑ a : Fin k, (p a - q a) * y a := by
            dsimp [y]
            calc
              ∑ i : Fin d, lam i * (∑ a : Fin k, (p a - q a) * G.L a i) =
                  ∑ i : Fin d, ∑ a : Fin k,
                    lam i * ((p a - q a) * G.L a i) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Finset.mul_sum]
              _ = ∑ a : Fin k, ∑ i : Fin d,
                    lam i * ((p a - q a) * G.L a i) := Finset.sum_comm
              _ = ∑ a : Fin k, (p a - q a) *
                    (∑ i : Fin d, G.L a i * lam i) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ ≤ γ := hmain
      _ = η * ((k : ℝ) * max 1 V) := by rfl

end
end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (q : Fin k → ℝ) (hq : BanditAlgorithm.PMSupportedOn S q)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d))
    (anc : Fin k → Finset (Fin k))
    (hself : ∀ b, b ∈ anc b)
    (htrans : ∀ a b, a ∈ anc b → ∀ c, b ∈ anc c → a ∈ anc c)
    (f₀ : Fin k → 𝕊 → Fin k → ℝ)
    (hfvec : BanditAlgorithm.PMVectorEstimatorOn G S f₀)
    (V : ℝ) (hV : 0 ≤ V)
    (hfbound : ∀ a σ b, |f₀ a σ b| ≤ V)
    (hfsupp : ∀ a σ b, f₀ a σ b ≠ 0 → a ∈ anc b)
    (hloss : ∀ a b, a ∈ anc b →
      ∑ i : Fin d, G.L a i * lam i ≤ ∑ i : Fin d, G.L b i * lam i)
    (η : ℝ) (hη : 0 < η)
    (hηsmall : η * ((k : ℝ) * max 1 V) ≤ 1 / 2) :
    ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
      BanditAlgorithm.PMInteriorDistribution p ∧
      BanditAlgorithm.PMVectorEstimatorOn G S f ∧
      (∀ a, η * max 1 V ≤ p a) ∧
      (∀ a σ b, |f a σ b| ≤ V) ∧
      (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
      (∀ i : Fin d,
        ∑ a : Fin k, p a *
          (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
            η ^ 2 * (2 * (k : ℝ) ^ 3 * (max 1 V) ^ 2)) ∧
      ∑ i : Fin d, lam i * (∑ a : Fin k, (p a - q a) * G.L a i) ≤
        η * ((k : ℝ) * max 1 V) :=
  BanditAlgorithm.partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
    G hk hL S q hq lam hlam anc hself htrans f₀ hfvec V hV hfbound hfsupp hloss η hη
      hηsmall
