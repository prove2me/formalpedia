-- Prove2me | solution 1 for FMLPricing.BranchBound.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:02:49.111804+00:00
-- url     : https://prove2.me/submissions/4ebcb0ca-eb1f-4d8b-9309-46688540d45f

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

open FMLPricing.BranchBound

namespace FMLAlg

variable {m n : ℕ} (I : FML m n)

lemma denom_pos (c : Fin m) (p : Fin n → ℝ) : 0 < denom I c p := by
  unfold denom; positivity

lemma q0_pos (p : Fin n → ℝ) (c : Fin m) : 0 < q0 I p c := by
  unfold q0; exact one_div_pos.mpr (denom_pos I c p)

lemma q0_mono (hI : Standing I) {p p' : Fin n → ℝ} (h : p ≤ p') (c : Fin m) :
    q0 I p c ≤ q0 I p' c := by
  unfold q0
  apply one_div_le_one_div_of_le (denom_pos I c p')
  unfold denom
  refine (add_le_add_iff_left 1).mpr (Finset.sum_le_sum fun j _ => ?_)
  exact Real.exp_le_exp.mpr (by nlinarith [hI.b_pos j, h j])

lemma Xset_bounds (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) (c : Fin m) :
    q0 I (pLo I) c ≤ x c ∧ x c ≤ q0 I (pHi I) c := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨q0_mono I hI hp.1 c, q0_mono I hI hp.2 c⟩

lemma s_mul_zOf (c : Fin m) (j : Fin n) (p : Fin n → ℝ) :
    s I c j * zOf I p j = Real.exp (I.a c j - I.b j * p j) := by
  unfold s zOf; rw [← Real.exp_add]; ring_nf

lemma q0_eq (c : Fin m) (p : Fin n → ℝ) :
    q0 I p c = 1 / (1 + ∑ j, s I c j * zOf I p j) := by
  unfold q0 denom; simp only [s_mul_zOf]

lemma sum_eq_of_q0 (c : Fin m) (p : Fin n → ℝ) :
    ∑ j, s I c j * zOf I p j = 1 / q0 I p c - 1 := by
  rw [q0_eq, one_div_one_div]; ring

lemma zOf_priceOf (hI : Standing I) {z : Fin n → ℝ} (hz : ∀ j, 0 < z j) :
    zOf I (priceOf I z) = z := by
  funext j
  unfold zOf priceOf
  rw [show -(-(I.b j)⁻¹ * Real.log (z j)) * I.b j = Real.log (z j) by
    field_simp [(hI.b_pos j).ne']]
  exact Real.exp_log (hz j)

lemma zLo_pos (j : Fin n) : 0 < zLo I j := Real.exp_pos _

lemma zOf_mem (hI : Standing I) {p : Fin n → ℝ} (hp : p ∈ priceBox I) :
    zOf I p ∈ Set.Icc (zLo I) (zHi I) :=
  ⟨fun j => Real.exp_le_exp.mpr (by nlinarith [hp.2 j, hI.b_pos j]),
   fun j => Real.exp_le_exp.mpr (by nlinarith [hp.1 j, hI.b_pos j])⟩

lemma priceOf_mem (hI : Standing I) {z : Fin n → ℝ} (hz : z ∈ Set.Icc (zLo I) (zHi I)) :
    priceOf I z ∈ priceBox I := by
  have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1 j)
  have h := zOf_priceOf I hI hpos
  constructor <;> intro j
  · have h2 := hz.2 j
    rw [← h] at h2
    unfold zOf zHi at h2
    have := Real.exp_le_exp.mp h2
    nlinarith [hI.b_pos j]
  · have h2 := hz.1 j
    rw [← h] at h2
    unfold zOf zLo at h2
    have := Real.exp_le_exp.mp h2
    nlinarith [hI.b_pos j]

lemma mu_eq {t : ℝ} (ht : 0 < t) : (1 - t) / t = 1 / t - 1 := by
  field_simp

lemma mu_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (1 - b) / b ≤ (1 - a) / a := by
  rw [mu_eq (ha.trans_le hab), mu_eq ha]
  have := one_div_le_one_div_of_le ha hab
  linarith

lemma xLo_pos (x : Fin m → ℝ) (r : ℝ) (c : Fin m) : 0 < xLo I x r c :=
  (q0_pos I _ c).trans_le (le_max_right _ _)

lemma xHi_pos {x : Fin m → ℝ} {r : ℝ} (hx : ∀ c, 0 < x c) (hr : 0 < r) (c : Fin m) :
    0 < xHi I x r c :=
  lt_min (by linarith [hx c]) (q0_pos I _ c)

/-- Every feasible point of `LP(x, r)` gives `χ(x, δ⁺, δ⁻) ∈ R(x, r) ∩ X`. -/
lemma chi_mem (hI : Standing I) {x : Fin m → ℝ} (hx : ∀ c, 0 < x c) {r : ℝ} (hr : 0 < r)
    {v : LPVars m n} (hv : LPFeasibleAt I x r v) :
    chi x v.δp v.δm ∈ Rbox I x r ∩ Xset I := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hv
  have hzpos : ∀ j, 0 < v.z j := fun j => (zLo_pos I j).trans_le (h5 j).1
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
  have hy : ∀ c, 0 < ∑ j, s I c j * v.z j := fun c =>
    Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (hzpos j)) hne
  have hchi : ∀ c, chi x v.δp v.δm c = 1 / (1 + ∑ j, s I c j * v.z j) := by
    intro c
    have e : v.δm c - v.δp c = (∑ j, s I c j * v.z j) - (1 - x c) / x c := by
      have := h1 c; unfold mu at this; linarith
    unfold chi
    rw [e]
    have hxc := (hx c).ne'
    have hyc := hy c
    rw [div_eq_div_iff (by field_simp; nlinarith [hx c]) (by linarith)]
    field_simp
    ring
  have hmem : priceOf I v.z ∈ priceBox I := priceOf_mem I hI ⟨fun j => (h5 j).1, fun j => (h5 j).2⟩
  have hq : chi x v.δp v.δm = q0 I (priceOf I v.z) := by
    funext c
    rw [hchi, q0_eq, zOf_priceOf I hI hzpos]
  refine ⟨⟨fun c => ?_, fun c => ?_⟩, hq ▸ ⟨_, hmem, rfl⟩⟩
  · -- lower end
    have h4c := h4 c
    have e := h1 c
    have hlo := xLo_pos I x r c
    have hyl : ∑ j, s I c j * v.z j ≤ (1 - xLo I x r c) / xLo I x r c := by
      unfold mu at h4c e; linarith
    rw [le_div_iff₀ hlo] at hyl
    show xLo I x r c ≤ chi x v.δp v.δm c
    rw [hchi, le_div_iff₀ (by linarith [hy c])]
    linarith
  · have h3c := h3 c
    have e := h1 c
    have hhi := xHi_pos I hx hr c
    have hyl : (1 - xHi I x r c) / xHi I x r c ≤ ∑ j, s I c j * v.z j := by
      unfold mu at h3c e; linarith
    rw [div_le_iff₀ hhi] at hyl
    show chi x v.δp v.δm c ≤ xHi I x r c
    rw [hchi, div_le_iff₀ (by linarith [hy c])]
    linarith

lemma zOf_inj (hI : Standing I) : Function.Injective (zOf I) := by
  intro p p' h
  funext j
  have := congrFun h j
  unfold zOf at this
  have := Real.exp_injective this
  have hb := (hI.b_pos j).ne'
  have : (p j - p' j) * I.b j = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hb

lemma q_eq_of (c : Fin m) (j : Fin n) (p : Fin n → ℝ) :
    q I c j p = s I c j * zOf I p j * q0 I p c := by
  unfold q q0
  rw [s_mul_zOf]; ring

lemma obj_eq (hI : Standing I) (x : Fin m → ℝ) (p : Fin n → ℝ) (hq : ∀ c, q0 I p c = x c) :
    Pi I p = cnstrObj I x (zOf I p) := by
  have hlog : ∀ j, Real.log (zOf I p j) = -(p j) * I.b j := fun j => by
    unfold zOf; rw [Real.log_exp]
  have hqq : ∀ c j, q I c j p = s I c j * zOf I p j * x c := fun c j => by
    rw [q_eq_of, hq]
  unfold Pi cnstrObj kx
  simp only [hqq, hlog]
  calc ∑ c, I.w c * ∑ j, p j * (s I c j * zOf I p j * x c)
      = ∑ c, ∑ j, I.w c * (p j * (s I c j * zOf I p j * x c)) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ j, ∑ c, I.w c * (p j * (s I c j * zOf I p j * x c)) := Finset.sum_comm
    _ = -∑ j, zOf I p j * (-p j * I.b j) * ((I.b j)⁻¹ * ∑ c, I.w c * s I c j * x c) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hb := (hI.b_pos j).ne'
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        field_simp

theorem lemma1 (hI : Standing I) (x : Fin m → ℝ) (hx : x ∈ Xset I) :
    Set.BijOn (zOf I) {p | p ∈ priceBox I ∧ ∀ c, q0 I p c = x c} (cnstrFeasible I x) ∧
      (∀ p ∈ priceBox I, (∀ c, q0 I p c = x c) → Pi I p = cnstrObj I x (zOf I p)) ∧
      ConcaveOn ℝ (Set.Icc (zLo I) (zHi I)) (cnstrObj I x) := by
  refine ⟨⟨?_, (zOf_inj I hI).injOn, ?_⟩, fun p _ hq => obj_eq I hI x p hq, ?_⟩
  · rintro p ⟨hp, hq⟩
    refine ⟨zOf_mem I hI hp, fun c => ?_⟩
    rw [← hq c, q0_eq, one_div_one_div]
  · rintro z ⟨hz, hzc⟩
    have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1 j)
    refine ⟨priceOf I z, ⟨priceOf_mem I hI hz, fun c => ?_⟩, zOf_priceOf I hI hpos⟩
    rw [q0_eq, zOf_priceOf I hI hpos, hzc c, one_div_one_div]
  · have hxpos : ∀ c, 0 < x c := by
      obtain ⟨p, -, rfl⟩ := hx
      exact fun c => q0_pos I p c
    have hk : ∀ j, 0 ≤ kx I j x := fun j => by
      unfold kx
      exact mul_nonneg (inv_pos.mpr (hI.b_pos j)).le
        (Finset.sum_nonneg fun c _ => by
          have := hI.w_pos c; have := Real.exp_pos (I.a c j); have := hxpos c
          unfold s; positivity)
    have hf : ∀ w : Fin n → ℝ, cnstrObj I x w = ∑ j, kx I j x * Real.negMulLog (w j) := by
      intro w
      unfold cnstrObj Real.negMulLog
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    refine ⟨convex_Icc _ _, ?_⟩
    intro u hu v hv a b ha hb hab
    rw [hf, hf, hf]
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hu0 : u j ∈ Set.Ici (0 : ℝ) := ((zLo_pos I j).trans_le (hu.1 j)).le
    have hv0 : v j ∈ Set.Ici (0 : ℝ) := ((zLo_pos I j).trans_le (hv.1 j)).le
    have h := Real.concaveOn_negMulLog.2 hu0 hv0 ha hb hab
    simp only [smul_eq_mul] at h
    have := mul_le_mul_of_nonneg_left h (hk j)
    linarith

end FMLAlg

theorem solution {m n : ℕ} (I : FML m n) (hI : Standing I) (x : Fin m → ℝ) (hx : x ∈ Xset I) :
    Set.BijOn (zOf I) {p | p ∈ priceBox I ∧ ∀ c, q0 I p c = x c} (cnstrFeasible I x) ∧
      (∀ p ∈ priceBox I, (∀ c, q0 I p c = x c) → Pi I p = cnstrObj I x (zOf I p)) ∧
      ConcaveOn ℝ (Set.Icc (zLo I) (zHi I)) (cnstrObj I x) :=
  FMLAlg.lemma1 I hI x hx
