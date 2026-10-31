-- Prove2me | solution 1 for FMLPricing.BranchBound.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:01:24.618167+00:00
-- url     : https://prove2.me/submissions/489c3ccc-e216-4652-b15c-cdbfbbfd62b2

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

theorem prop7 (hI : Standing I)
    (x : Fin m → ℝ) (hx : ∀ c, 0 < x c) (r : ℝ) (hr : 0 < r) :
    (Rbox I x r ∩ Xset I).Nonempty ↔ LPFeasible I x r := by
  constructor
  · rintro ⟨_, hR, ⟨p, hp, rfl⟩⟩
    set d : Fin m → ℝ := fun c => mu x c - mu (q0 I p) c with hd
    refine ⟨⟨∑ c, (max (d c) 0 + max (-d c) 0), zOf I p, fun c => max (d c) 0,
      fun c => max (-d c) 0⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c
      show ∑ j, s I c j * zOf I p j + max (d c) 0 - max (-d c) 0 = mu x c
      rw [add_sub_assoc, max_zero_sub_eq_self, sum_eq_of_q0, hd]
      simp only [mu]
      rw [mu_eq (q0_pos I p c)]
      ring
    · intro c
      exact Finset.single_le_sum (f := fun c => max (d c) 0 + max (-d c) 0)
        (fun c _ => add_nonneg (le_max_right _ _) (le_max_right _ _)) (Finset.mem_univ c)
    · intro c
      show max (d c) 0 - max (-d c) 0 ≤ mu x c - mu (xHi I x r) c
      rw [max_zero_sub_eq_self, hd]
      have := mu_anti (q0_pos I p c) (hR.2 c)
      simp only [mu]; linarith
    · intro c
      show max (-d c) 0 - max (d c) 0 ≤ mu (xLo I x r) c - mu x c
      have := max_zero_sub_eq_self (-d c)
      rw [neg_neg] at this
      rw [this, hd]
      have := mu_anti (xLo_pos I x r c) (hR.1 c)
      simp only [mu]; linarith
    · intro j
      exact ⟨(zOf_mem I hI hp).1 j, (zOf_mem I hI hp).2 j⟩
    · intro c
      exact ⟨le_max_right _ _, le_max_right _ _⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, chi_mem I hI hx hr hv⟩

theorem cor1 (hI : Standing I)
    (x : Fin m → ℝ) (hx : ∀ c, 0 < x c) (r : ℝ) (hr : 0 < r)
    (hR : (Rbox I x r ∩ Xset I).Nonempty) (v : LPVars m n) (hv : IsLPSolution I x r v) :
    chi x v.δp v.δm ∈ Rbox I x r ∩ Xset I ∧ (x ∈ Xset I → chi x v.δp v.δm = x) := by
  refine ⟨chi_mem I hI hx hr hv.1, fun hX => ?_⟩
  obtain ⟨p, hp, hpx⟩ := hX
  have hfeas : LPFeasibleAt I x r ⟨0, zOf I p, 0, 0⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c
      show ∑ j, s I c j * zOf I p j + 0 - 0 = mu x c
      rw [sum_eq_of_q0, hpx]
      simp only [mu]
      rw [mu_eq (hx c)]; ring
    · intro c; show (0 : ℝ) + 0 ≤ 0; norm_num
    · intro c
      show (0 : ℝ) - 0 ≤ mu x c - mu (xHi I x r) c
      have hb := Xset_bounds I hI ⟨p, hp, hpx⟩ c
      have := mu_anti (hx c) (le_min (by linarith) hb.2 : x c ≤ xHi I x r c)
      simp only [mu, xHi] at this ⊢; linarith
    · intro c
      show (0 : ℝ) - 0 ≤ mu (xLo I x r) c - mu x c
      have hb := Xset_bounds I hI ⟨p, hp, hpx⟩ c
      have := mu_anti (xLo_pos I x r c) (max_le (by linarith) hb.1 : xLo I x r c ≤ x c)
      simp only [mu, xLo] at this ⊢; linarith
    · intro j
      exact ⟨(zOf_mem I hI hp).1 j, (zOf_mem I hI hp).2 j⟩
    · intro c; exact ⟨le_rfl, le_rfl⟩
  have hγ : v.γ ≤ 0 := hv.2 _ hfeas
  obtain ⟨-, h2, -, -, -, h6⟩ := hv.1
  funext c
  have hp0 : v.δp c = 0 := by linarith [h2 c, (h6 c).1, (h6 c).2]
  have hm0 : v.δm c = 0 := by linarith [h2 c, (h6 c).1, (h6 c).2]
  unfold chi
  rw [hp0, hm0]
  simp

end FMLAlg

theorem solution {m n : ℕ} (I : FML m n) (hI : Standing I)
    (x : Fin m → ℝ) (hx : ∀ c, 0 < x c) (r : ℝ) (hr : 0 < r)
    (hR : (Rbox I x r ∩ Xset I).Nonempty) (v : LPVars m n) (hv : IsLPSolution I x r v) :
    chi x v.δp v.δm ∈ Rbox I x r ∩ Xset I ∧ (x ∈ Xset I → chi x v.δp v.δm = x) :=
  FMLAlg.cor1 I hI x hx r hr hR v hv
