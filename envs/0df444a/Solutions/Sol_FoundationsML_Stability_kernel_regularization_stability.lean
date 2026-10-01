-- Prove2me | solution 1 for FoundationsML.Stability.kernel_regularization_stability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T16:39:00.129367+00:00
-- url     : https://prove2.me/submissions/c9b719d5-b3ef-4c43-9ec4-581d97fbeca6

import Mathlib
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_SigmaAdmissible
import Definitions.Def_FoundationsML_Stability_IsRKHSOf
import Definitions.Def_FoundationsML_Stability_IsMinimizer

set_option autoImplicit false

theorem e983_small_t (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * c ≤ ε := by
  refine ⟨min 1 (ε / (c + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have h1 : min 1 (ε / (c + 1)) ≤ ε / (c + 1) := min_le_right _ _
  have h2 : ε / (c + 1) * c ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  calc min 1 (ε / (c + 1)) * c ≤ ε / (c + 1) * c := mul_le_mul_of_nonneg_right h1 hc
    _ ≤ ε := h2

theorem e983_strong {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : H → ℝ) (lam : ℝ) (hlam : 0 < lam) (h g : H)
    (hcomb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → R ((1 - t) • h + t • g) ≤ (1 - t) * R h + t * R g)
    (hmin : ∀ g' : H, R h + lam * ‖h‖ ^ 2 ≤ R g' + lam * ‖g'‖ ^ 2) :
    R h + lam * ‖h‖ ^ 2 + lam * ‖g - h‖ ^ 2 ≤ R g + lam * ‖g‖ ^ 2 := by
  have hnorm : ∀ t : ℝ, ‖(1 - t) • h + t • g‖ ^ 2
      = (1 - t) * ‖h‖ ^ 2 + t * ‖g‖ ^ 2 - t * (1 - t) * ‖g - h‖ ^ 2 := by
    intro t
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm h g]
    ring
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      R h + lam * ‖h‖ ^ 2 + lam * (1 - t) * ‖g - h‖ ^ 2 ≤ R g + lam * ‖g‖ ^ 2 := by
    intro t ht0 ht1
    have h1 := hmin ((1 - t) • h + t • g)
    rw [hnorm t] at h1
    have h2 := hcomb t ht0.le ht1
    have h3 : t * (R h + lam * ‖h‖ ^ 2 + lam * (1 - t) * ‖g - h‖ ^ 2)
        ≤ t * (R g + lam * ‖g‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc0 : 0 ≤ lam * ‖g - h‖ ^ 2 := by positivity
  obtain ⟨t, ht0, ht1, htc⟩ := e983_small_t (lam * ‖g - h‖ ^ 2) ε hc0 hε
  have := key t ht0 ht1
  nlinarith

open FoundationsML.Stability in
theorem e983_ev_comb {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) (hR : IsRKHSOf K Φ ev)
    (h g : H) (t : ℝ) (x : X) :
    ev ((1 - t) • h + t • g) x = (1 - t) * ev h x + t * ev g x := by
  rw [hR.2 ((1 - t) • h + t • g) x, hR.2 h x, hR.2 g x, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]

open FoundationsML.Stability in
theorem e983_emp_comb {X Y H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) (hR : IsRKHSOf K Φ ev)
    (L : ℝ → Y → ℝ) (hLconv : ∀ y : Y, ConvexOn ℝ Set.univ (fun y' : ℝ => L y' y))
    {m : ℕ} (S : Fin m → X × Y) (h g : H) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    EmpiricalError L S (ev ((1 - t) • h + t • g))
      ≤ (1 - t) * EmpiricalError L S (ev h) + t * EmpiricalError L S (ev g) := by
  unfold EmpiricalError Loss
  have hm : (0:ℝ) ≤ 1 / (m:ℝ) := by positivity
  calc (1 / (m:ℝ)) * ∑ i, L (ev ((1 - t) • h + t • g) (S i).1) (S i).2
      ≤ (1 / (m:ℝ)) * ∑ i, ((1 - t) * L (ev h (S i).1) (S i).2
          + t * L (ev g (S i).1) (S i).2) := by
        apply mul_le_mul_of_nonneg_left _ hm
        apply Finset.sum_le_sum
        intro i _
        rw [e983_ev_comb K Φ ev hR]
        have := (hLconv (S i).2).2 (Set.mem_univ (ev h (S i).1)) (Set.mem_univ (ev g (S i).1))
          (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
        simpa only [smul_eq_mul] using this
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

open FoundationsML.Stability in
theorem e983_diff {X Y : Type*} (L : ℝ → Y → ℝ) {m : ℕ} (S S' : Fin m → X × Y) (i : Fin m)
    (hi : ∀ j : Fin m, j ≠ i → S j = S' j) (f : X → ℝ) :
    EmpiricalError L S f - EmpiricalError L S' f
      = (1 / (m:ℝ)) * (Loss L f (S i) - Loss L f (S' i)) := by
  unfold EmpiricalError
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · intro j _ hj
    rw [hi j hj, sub_self]
  · intro hn
    exact absurd (Finset.mem_univ i) hn

open FoundationsML.Stability in
theorem e983_evbound {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) (hR : IsRKHSOf K Φ ev)
    (r : ℝ) (hr : 0 ≤ r) (hK : ∀ x : X, K x x ≤ r ^ 2) (a b : H) (x : X) :
    |ev a x - ev b x| ≤ r * ‖a - b‖ := by
  rw [hR.2 a, hR.2 b, ← inner_sub_left]
  have hΦ : ‖Φ x‖ ≤ r := by
    have h1 : ‖Φ x‖ ^ 2 ≤ r ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← hR.1]; exact hK x
    nlinarith [norm_nonneg (Φ x)]
  calc |inner ℝ (a - b) (Φ x)| ≤ ‖a - b‖ * ‖Φ x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖a - b‖ * r := mul_le_mul_of_nonneg_left hΦ (norm_nonneg _)
    _ = r * ‖a - b‖ := mul_comm _ _

open FoundationsML.Stability in
theorem solution
    {X Y H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) (hRKHS : IsRKHSOf K Φ ev)
    (r : ℝ) (hr : 0 ≤ r) (hK : ∀ x : X, K x x ≤ r ^ 2)
    (L : ℝ → Y → ℝ) (σ : ℝ) (hσ : 0 ≤ σ) (hAdm : SigmaAdmissible ev L σ)
    (hLconv : ∀ y : Y, ConvexOn ℝ Set.univ (fun y' : ℝ => L y' y))
    {m : ℕ} (hm : 0 < m) (lam : ℝ) (hlam : 0 < lam)
    (S S' : Fin m → X × Y) (hSS' : ∃ i : Fin m, ∀ j : Fin m, j ≠ i → S j = S' j)
    (h h' : H)
    (hmin : IsMinimizer (fun g : H => EmpiricalError L S (ev g) + lam * ‖g‖ ^ 2) h)
    (hmin' : IsMinimizer (fun g : H => EmpiricalError L S' (ev g) + lam * ‖g‖ ^ 2) h') :
    ∀ z : X × Y, |Loss L (ev h) z - Loss L (ev h') z| ≤ σ ^ 2 * r ^ 2 / (m * lam) := by
  intro z
  obtain ⟨i, hi⟩ := hSS'
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have k1 : EmpiricalError L S (ev h) + lam * ‖h‖ ^ 2 + lam * ‖h' - h‖ ^ 2
      ≤ EmpiricalError L S (ev h') + lam * ‖h'‖ ^ 2 :=
    e983_strong (fun g => EmpiricalError L S (ev g)) lam hlam h h'
      (fun t ht0 ht1 => e983_emp_comb K Φ ev hRKHS L hLconv S h h' t ht0 ht1) hmin
  have k2 : EmpiricalError L S' (ev h') + lam * ‖h'‖ ^ 2 + lam * ‖h - h'‖ ^ 2
      ≤ EmpiricalError L S' (ev h) + lam * ‖h‖ ^ 2 :=
    e983_strong (fun g => EmpiricalError L S' (ev g)) lam hlam h' h
      (fun t ht0 ht1 => e983_emp_comb K Φ ev hRKHS L hLconv S' h' h t ht0 ht1) hmin'
  rw [norm_sub_rev h h'] at k2
  have d1 := e983_diff L S S' i hi (ev h')
  have d2 := e983_diff L S S' i hi (ev h)
  have a1 : Loss L (ev h') (S i) - Loss L (ev h) (S i) ≤ σ * (r * ‖h' - h‖) := by
    unfold Loss
    calc _ ≤ |L (ev h' (S i).1) (S i).2 - L (ev h (S i).1) (S i).2| := le_abs_self _
      _ ≤ σ * |ev h' (S i).1 - ev h (S i).1| := hAdm h h' _ _
      _ ≤ σ * (r * ‖h' - h‖) :=
        mul_le_mul_of_nonneg_left (e983_evbound K Φ ev hRKHS r hr hK h' h _) hσ
  have a2 : Loss L (ev h) (S' i) - Loss L (ev h') (S' i) ≤ σ * (r * ‖h' - h‖) := by
    unfold Loss
    calc _ ≤ |L (ev h (S' i).1) (S' i).2 - L (ev h' (S' i).1) (S' i).2| := le_abs_self _
      _ ≤ σ * |ev h (S' i).1 - ev h' (S' i).1| := hAdm h' h _ _
      _ = σ * |ev h' (S' i).1 - ev h (S' i).1| := by rw [abs_sub_comm]
      _ ≤ σ * (r * ‖h' - h‖) :=
        mul_le_mul_of_nonneg_left (e983_evbound K Φ ev hRKHS r hr hK h' h _) hσ
  have hsum : 2 * lam * ‖h' - h‖ ^ 2 ≤ (1 / (m:ℝ)) * (2 * (σ * (r * ‖h' - h‖))) := by
    have e : (1 / (m:ℝ)) * ((Loss L (ev h') (S i) - Loss L (ev h) (S i))
        + (Loss L (ev h) (S' i) - Loss L (ev h') (S' i)))
        = (EmpiricalError L S (ev h') - EmpiricalError L S' (ev h'))
          - (EmpiricalError L S (ev h) - EmpiricalError L S' (ev h)) := by
      rw [d1, d2]; ring
    have hm1 : (0:ℝ) ≤ 1 / (m:ℝ) := by positivity
    calc 2 * lam * ‖h' - h‖ ^ 2
        ≤ (1 / (m:ℝ)) * ((Loss L (ev h') (S i) - Loss L (ev h) (S i))
          + (Loss L (ev h) (S' i) - Loss L (ev h') (S' i))) := by rw [e]; linarith
      _ ≤ (1 / (m:ℝ)) * (2 * (σ * (r * ‖h' - h‖))) :=
        mul_le_mul_of_nonneg_left (by linarith) hm1
  have hD : (m:ℝ) * lam * ‖h' - h‖ ^ 2 ≤ σ * r * ‖h' - h‖ := by
    have h2 : 2 * lam * ‖h' - h‖ ^ 2 ≤ (2 * (σ * (r * ‖h' - h‖))) / m := by
      rw [div_eq_inv_mul, ← one_div]; exact hsum
    rw [le_div_iff₀ hmpos] at h2
    nlinarith
  have hev : |Loss L (ev h) z - Loss L (ev h') z| ≤ σ * (r * ‖h' - h‖) := by
    unfold Loss
    calc _ ≤ σ * |ev h z.1 - ev h' z.1| := hAdm h' h _ _
      _ = σ * |ev h' z.1 - ev h z.1| := by rw [abs_sub_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (e983_evbound K Φ ev hRKHS r hr hK h' h _) hσ
  refine hev.trans ?_
  rw [le_div_iff₀ (by positivity)]
  rcases (norm_nonneg (h' - h)).eq_or_lt with h0 | hpos
  · rw [← h0]
    have := mul_nonneg (sq_nonneg σ) (sq_nonneg r)
    nlinarith
  · have hb : (m:ℝ) * lam * ‖h' - h‖ ≤ σ * r := by
      have hh : (m:ℝ) * lam * ‖h' - h‖ * ‖h' - h‖ ≤ σ * r * ‖h' - h‖ := by nlinarith
      exact le_of_mul_le_mul_right hh hpos
    have := mul_le_mul_of_nonneg_left hb (mul_nonneg hσ hr)
    nlinarith
